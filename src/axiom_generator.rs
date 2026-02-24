use std::collections::HashMap;

use itertools::Itertools;

use crate::VarName;
use crate::axiom_builder_state::{AxiomBuilderState, BodyPropositionData};
use crate::create_wrapper::RESULT_PARAM;
use crate::prog_ir::{LetBinding, Type, TypeDecl};
use crate::spec_ir::{Expression, Parameter, Proposition};

/// Cache key for function applications - combines function name and argument expressions
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
struct ApplicationKey {
    func_name: String,
    args: Vec<Expression>,
}

/// Result of extracting expressions with their preceding steps and parameters
#[derive(Debug, Clone)]
struct ExprExtraction {
    /// The final expressions extracted
    expressions: Vec<Expression>,
    /// Preceding proposition steps for each expression
    preceding_steps: Vec<Vec<Proposition>>,
    /// Additional parameters introduced during extraction
    parameters: Vec<Parameter>,
}

/// Generates axioms in the spec IR from parsed program IR functions.
pub struct AxiomGenerator {
    /// Type declarations for looking up constructor types
    type_constructors: Vec<TypeDecl>,
    /// Counter for generating unique variable names (e.g., res_0, res_1, ...)
    var_counter: usize,
    /// Map of function names to their return types
    function_types: HashMap<VarName, Type>,
    /// Accumulated functions and their body propositions
    prepared: Vec<(LetBinding, Vec<BodyPropositionData>)>,
}

impl AxiomGenerator {
    /// Create a new AxiomGenerator with the given type constructors
    pub fn new(type_constructors: Vec<TypeDecl>) -> Self {
        Self {
            type_constructors,
            var_counter: 0,
            function_types: HashMap::new(),
            prepared: Vec::new(),
        }
    }

    /// Get the next variable name and increment the counter
    fn next_var(&mut self) -> VarName {
        let name = VarName(format!("res_{}", self.var_counter));
        self.var_counter += 1;
        name
    }

    /// Get the registered return type for a function, if available
    fn get_function_type(&self, name: &VarName) -> Option<&Type> {
        self.function_types.get(name)
    }

    /// Check if a proposition is an equality with RESULT_PARAM on the right side
    fn is_result_equality(prop: &Proposition) -> bool {
        if let Proposition::Expr(Expression::BinaryOp(_, crate::prog_ir::BinaryOp::Eq, rhs)) = prop
            && let Expression::Variable(name) = rhs.as_ref()
        {
            return name.0 == RESULT_PARAM;
        }
        false
    }

    /// Wrap an expression as an equality with RESULT_PARAM if not already wrapped
    fn wrap_result_equality(&self, prop: &Proposition) -> Proposition {
        if Self::is_result_equality(prop) {
            prop.clone()
        } else {
            let expr = prop.as_expr();
            Proposition::Expr(Expression::BinaryOp(
                Box::new(expr.clone()),
                crate::prog_ir::BinaryOp::Eq,
                Box::new(Expression::Variable(RESULT_PARAM.into())),
            ))
        }
    }

    #[cfg(test)]
    /// Get the prepared functions and their body propositions (test only)
    pub(crate) fn get_prepared(&self) -> &[(LetBinding, Vec<BodyPropositionData>)] {
        &self.prepared
    }

    /// Look up the type of a constructor parameter by constructor name and field index
    fn get_constructor_field_type(&self, constructor_name: &str, field_index: usize) -> Type {
        self.type_constructors
            .iter()
            .find_map(|type_decl| {
                type_decl
                    .variants
                    .iter()
                    .find(|variant| variant.name == constructor_name)
                    .and_then(|variant| variant.fields.get(field_index).map(|(_, ty)| ty.clone()))
            })
            .unwrap_or_else(|| {
                panic!(
                    "Failed to find constructor {} at index {}",
                    constructor_name, field_index
                )
            })
    }

    /// Extract a single expression from results with validation.
    /// Ensures exactly one result, one expression step, and no additional parameters.
    fn extract_single_expr(results: Vec<BodyPropositionData>) -> Result<Expression, String> {
        // Validate result count
        if results.len() != 1 {
            return Err(format!(
                "Expected exactly one result, got {}",
                results.len()
            ));
        }
        let body_data = results.into_iter().next().unwrap();

        // Validate no input constraints and no additional parameters
        if !body_data.input_constraints.is_empty() {
            return Err(format!(
                "Expected no input constraints, got {}",
                body_data.input_constraints.len()
            ));
        }
        if !body_data.additional_parameters.is_empty() {
            return Err(format!(
                "Expected no additional parameters, got {}",
                body_data.additional_parameters.len()
            ));
        }

        // Validate exactly one body step and extract expression
        if body_data.body_steps.len() != 1 {
            return Err(format!(
                "Expected exactly one body step, got {}",
                body_data.body_steps.len()
            ));
        }

        match &body_data.body_steps[0] {
            Proposition::Expr(e) => Ok(e.clone()),
            _ => Err("Expected body step to be an expression".to_string()),
        }
    }

    /// Extract expressions with their preceding proposition steps and parameters.
    /// Returns all combinations of results across the input expressions.
    fn extract_exprs_with_steps(
        &mut self,
        exprs: Vec<&crate::prog_ir::Expression>,
        cache: &mut HashMap<ApplicationKey, VarName>,
    ) -> Result<Vec<ExprExtraction>, String> {
        let all_results: Vec<Vec<BodyPropositionData>> = exprs
            .iter()
            .map(|expr| self.analyze_expression(expr, cache))
            .collect();

        all_results
            .into_iter()
            .multi_cartesian_product()
            .map(|combination| {
                let mut all_exprs = Vec::new();
                let mut all_steps = Vec::new();
                let mut all_params = Vec::new();

                for body_data in combination {
                    let (last_prop, preceding) = Self::combine_all_steps(
                        &body_data.input_constraints,
                        &body_data.body_steps,
                    )?;

                    let expr = match last_prop {
                        Proposition::Expr(e) => e.clone(),
                        _ => return Err("Expected final step to be an expression".to_string()),
                    };

                    all_exprs.push(expr);
                    all_steps.push(preceding.to_vec());
                    all_params.extend(body_data.additional_parameters);
                }

                Ok(ExprExtraction {
                    expressions: all_exprs,
                    preceding_steps: all_steps,
                    parameters: all_params,
                })
            })
            .collect()
    }

    /// Combine input constraints and body steps, extracting the final step
    fn combine_all_steps(
        input_constraints: &[Proposition],
        body_steps: &[Proposition],
    ) -> Result<(Proposition, Vec<Proposition>), String> {
        let mut all_steps = Vec::with_capacity(input_constraints.len() + body_steps.len());
        all_steps.extend_from_slice(input_constraints);
        all_steps.extend_from_slice(body_steps);

        let (last_prop, preceding) = all_steps
            .split_last()
            .ok_or("Expected at least one proposition step")?;

        Ok((last_prop.clone(), preceding.to_vec()))
    }

    /// Convert a pattern to a predicate-based proposition
    /// For Nil: generates `is_nil l`
    /// For Cons(x, xs): generates `((is_cons l) && ((head l) == x)) && ((tail l) == xs)`
    fn pattern_to_predicate_proposition(
        &self,
        scrutinee: &Expression,
        pattern: &crate::prog_ir::Pattern,
    ) -> Proposition {
        match pattern {
            crate::prog_ir::Pattern::Literal(lit) => {
                // For literal patterns, use equality
                Proposition::Expr(Expression::BinaryOp(
                    Box::new(scrutinee.clone()),
                    crate::prog_ir::BinaryOp::Eq,
                    Box::new(Expression::Literal(lit.clone())),
                ))
            }
            crate::prog_ir::Pattern::Wildcard => {
                panic!(
                    "Wildcard patterns must be handled before calling pattern_to_predicate_proposition"
                )
            }
            crate::prog_ir::Pattern::Variable(_) => {
                panic!(
                    "Variable patterns must be handled before calling pattern_to_predicate_proposition"
                )
            }
            crate::prog_ir::Pattern::Constructor(constructor_name, nested_patterns) => {
                let is_cons_pred = Proposition::Predicate(
                    format!("is_{}", constructor_name.get_simple_name().to_lowercase()),
                    vec![scrutinee.clone()],
                );

                // Build field constraints and combine with constructor predicate
                let field_constraints = nested_patterns
                    .iter()
                    .enumerate()
                    .filter_map(|(field_index, nested_pattern)| {
                        self.pattern_to_field_equality(
                            scrutinee,
                            constructor_name,
                            field_index,
                            nested_pattern,
                        )
                    })
                    .collect::<Vec<_>>();

                // Combine all constraints with AND
                self.combine_constraints(is_cons_pred, field_constraints)
            }
            crate::prog_ir::Pattern::Tuple(patterns) => {
                let elem_constraints = patterns
                    .iter()
                    .enumerate()
                    .map(|(index, pat)| {
                        let elem_expr =
                            Expression::Variable(VarName(format!("_tuple_elem_{}", index)));
                        self.pattern_to_predicate_proposition(&elem_expr, pat)
                    })
                    .collect::<Vec<_>>();

                self.combine_constraints(
                    Proposition::Predicate("true".to_string(), vec![]),
                    elem_constraints,
                )
            }
        }
    }

    /// Combine multiple constraints into a single AND proposition
    fn combine_constraints(
        &self,
        initial: Proposition,
        constraints: Vec<Proposition>,
    ) -> Proposition {
        let mut all_props = vec![initial];
        all_props.extend(constraints);
        Proposition::And(all_props)
    }

    /// Generate a field equality constraint for a constructor field
    /// Gets the actual field name from the type declaration for the constructor
    /// Returns None for Wildcard patterns (which don't introduce constraints)
    fn pattern_to_field_equality(
        &self,
        scrutinee: &Expression,
        constructor_name: &crate::prog_ir::ConstructorName,
        field_index: usize,
        pattern: &crate::prog_ir::Pattern,
    ) -> Option<Proposition> {
        // Get the actual field name from the type declaration
        let accessor_name = self
            .type_constructors
            .iter()
            .find_map(|type_decl| {
                type_decl
                    .variants
                    .iter()
                    .find(|v| v.name == constructor_name.get_simple_name())
                    .and_then(|variant| {
                        variant
                            .fields
                            .get(field_index)
                            .map(|(name, _)| name.clone())
                    })
            })
            .unwrap_or_else(|| {
                panic!(
                    "Failed to find field {} for constructor {}",
                    field_index,
                    constructor_name.get_simple_name()
                )
            });

        let field_access =
            Expression::FieldAccess(accessor_name.clone(), Box::new(scrutinee.clone()));

        match pattern {
            crate::prog_ir::Pattern::Variable(var_name) => {
                // Generate (head l) == x
                Some(Proposition::Expr(Expression::BinaryOp(
                    Box::new(field_access),
                    crate::prog_ir::BinaryOp::Eq,
                    Box::new(Expression::Variable(var_name.clone())),
                )))
            }
            crate::prog_ir::Pattern::Literal(lit) => {
                // Generate (head l) == literal
                Some(Proposition::Expr(Expression::BinaryOp(
                    Box::new(field_access),
                    crate::prog_ir::BinaryOp::Eq,
                    Box::new(Expression::Literal(lit.clone())),
                )))
            }
            crate::prog_ir::Pattern::Constructor(_constructor_name, _nested_patterns) => {
                // Nested constructor pattern: recursively process
                Some(self.pattern_to_predicate_proposition(&field_access, pattern))
            }
            crate::prog_ir::Pattern::Wildcard => None,
            crate::prog_ir::Pattern::Tuple(_) => {
                panic!("Nested tuple patterns not yet supported")
            }
        }
    }

    /// Extract all variables introduced by a pattern
    fn vars_from_pattern(&self, pattern: &crate::prog_ir::Pattern) -> Vec<(VarName, Type)> {
        match pattern {
            crate::prog_ir::Pattern::Variable(_name) => {
                unimplemented!("Need to infer or track the type of variable pattern")
            }
            crate::prog_ir::Pattern::Constructor(constructor_name, nested_patterns) => {
                nested_patterns
                    .iter()
                    .enumerate()
                    .flat_map(|(index, p)| match p {
                        crate::prog_ir::Pattern::Variable(name) => {
                            let typ = self.get_constructor_field_type(
                                constructor_name.get_simple_name(),
                                index,
                            );
                            vec![(name.clone(), typ)]
                        }
                        _ => self.vars_from_pattern(p),
                    })
                    .collect()
            }
            crate::prog_ir::Pattern::Literal(_) => vec![],
            crate::prog_ir::Pattern::Wildcard => vec![],
            crate::prog_ir::Pattern::Tuple(patterns) => patterns
                .iter()
                .flat_map(|p| self.vars_from_pattern(p))
                .collect(),
        }
    }

    /// Analyze both branches of an if-then-else expression
    /// Extracts the condition and processes both true and false branches
    fn analyze_ite_branches(
        &mut self,
        condition_body_data: &BodyPropositionData,
        then_branch: &crate::prog_ir::Expression,
        else_branch: &crate::prog_ir::Expression,
        cache: &mut HashMap<ApplicationKey, VarName>,
    ) -> Vec<BodyPropositionData> {
        let (last_cond, preceding_conds) = condition_body_data
            .body_steps
            .split_last()
            .unwrap_or_else(|| panic!("Expected at least one condition step"));
        let condition_expr = last_cond.as_expr().clone();

        let mut results = Vec::new();
        for (is_true, branch) in [(true, then_branch), (false, else_branch)] {
            let mut branch_cache = cache.clone();
            let branch_results = self.analyze_expression(branch, &mut branch_cache);

            for branch_body_data in branch_results {
                let mut input_constraints = condition_body_data.input_constraints.clone();
                input_constraints.extend(preceding_conds.to_vec());

                // Add the guard condition (or its negation for false branch)
                let condition_prop = if is_true {
                    Proposition::Expr(condition_expr.clone())
                } else {
                    Proposition::Not(Box::new(Proposition::Expr(condition_expr.clone())))
                };
                input_constraints.push(condition_prop);
                input_constraints.extend(branch_body_data.input_constraints.clone());

                let mut params = condition_body_data.additional_parameters.clone();
                params.extend(branch_body_data.additional_parameters);

                results.push(BodyPropositionData {
                    input_constraints,
                    body_steps: branch_body_data.body_steps,
                    additional_parameters: params,
                });
            }
        }
        results
    }

    /// Prepare a function for batch axiom generation
    pub fn prepare_function(&mut self, binding: &LetBinding) -> Result<(), String> {
        // Validate that binding has a return type annotation
        if binding.return_type.is_none() {
            return Err(format!(
                "Function '{}' must have an explicit return type annotation",
                binding.name
            ));
        }

        self.function_types
            .insert(binding.name.clone(), binding.return_type.clone().unwrap());

        // Create a fresh cache for this axiom's analysis
        let mut cache = HashMap::new();
        let mut body_propositions = self.analyze_expression(&binding.body, &mut cache);

        // Wrap final results with = RESULT_PARAM at the function body level
        body_propositions = body_propositions
            .into_iter()
            .map(|body_prop| self.wrap_body_proposition_steps(body_prop))
            .collect();

        self.prepared.push((binding.clone(), body_propositions));
        Ok(())
    }

    /// Wrap the final body step with = RESULT_PARAM if not already wrapped
    fn wrap_body_proposition_steps(
        &self,
        mut body_prop: BodyPropositionData,
    ) -> BodyPropositionData {
        if !body_prop.body_steps.is_empty() {
            let last_prop = body_prop.body_steps.last().unwrap().clone();
            if !Self::is_result_equality(&last_prop) {
                body_prop.body_steps.pop();
                body_prop
                    .body_steps
                    .push(self.wrap_result_equality(&last_prop));
            }
        }
        body_prop
    }

    /// Analyze expressions, building propositions
    fn analyze_expression(
        &mut self,
        body: &crate::prog_ir::Expression,
        cache: &mut HashMap<ApplicationKey, VarName>,
    ) -> Vec<BodyPropositionData> {
        match body {
            crate::prog_ir::Expression::Variable(var_name) => vec![BodyPropositionData {
                input_constraints: vec![],
                body_steps: vec![Proposition::Expr(Expression::Variable(var_name.clone()))],
                additional_parameters: vec![],
            }],
            crate::prog_ir::Expression::Constructor(constructor_name, expressions) => {
                let converted_expressions: Vec<_> = expressions
                    .iter()
                    .map(|expr| {
                        Self::extract_single_expr(self.analyze_expression(expr, cache))
                            .unwrap_or_else(|e| panic!("Constructor argument: {}", e))
                    })
                    .collect();
                vec![BodyPropositionData {
                    input_constraints: vec![],
                    body_steps: vec![Proposition::Expr(Expression::Constructor(
                        constructor_name.clone(),
                        converted_expressions,
                    ))],
                    additional_parameters: vec![],
                }]
            }
            crate::prog_ir::Expression::Literal(literal) => vec![BodyPropositionData {
                input_constraints: vec![],
                body_steps: vec![Proposition::Expr(Expression::Literal(literal.clone()))],
                additional_parameters: vec![],
            }],
            crate::prog_ir::Expression::UnaryOp(unary_op, expression) => {
                let combined = self
                    .extract_exprs_with_steps(vec![expression], cache)
                    .unwrap_or_else(|e| panic!("UnaryOp operand: {}", e));

                combined
                    .into_iter()
                    .map(|extraction| {
                        assert_eq!(
                            extraction.expressions.len(),
                            1,
                            "UnaryOp requires exactly 1 expression"
                        );
                        let mut body_steps = extraction.preceding_steps.concat();
                        body_steps.push(Proposition::Expr(Expression::UnaryOp(
                            *unary_op,
                            Box::new(extraction.expressions[0].clone()),
                        )));
                        BodyPropositionData {
                            input_constraints: vec![],
                            body_steps,
                            additional_parameters: extraction.parameters,
                        }
                    })
                    .collect()
            }
            crate::prog_ir::Expression::BinaryOp(expression, binary_op, expression1) => {
                let combined = self
                    .extract_exprs_with_steps(vec![&expression, &expression1], cache)
                    .unwrap_or_else(|e| panic!("BinaryOp operand: {}", e));

                combined
                    .into_iter()
                    .map(|extraction| {
                        assert_eq!(
                            extraction.expressions.len(),
                            2,
                            "BinaryOp requires exactly 2 expressions"
                        );
                        let mut body_steps = extraction.preceding_steps.concat();
                        body_steps.push(Proposition::Expr(Expression::BinaryOp(
                            Box::new(extraction.expressions[0].clone()),
                            *binary_op,
                            Box::new(extraction.expressions[1].clone()),
                        )));
                        BodyPropositionData {
                            input_constraints: vec![],
                            body_steps,
                            additional_parameters: extraction.parameters,
                        }
                    })
                    .collect()
            }
            crate::prog_ir::Expression::Application(func_expr, arg_exprs) => {
                let func_body_data =
                    Self::extract_single_expr(self.analyze_expression(func_expr, cache))
                        .unwrap_or_else(|e| panic!("Application function: {}", e));

                let func_name = match func_body_data {
                    Expression::Variable(v) => v,
                    _ => panic!(
                        "Application function must evaluate to a variable, got: {:?}",
                        func_body_data
                    ),
                };

                let combined = self
                    .extract_exprs_with_steps(arg_exprs.iter().collect(), cache)
                    .unwrap_or_else(|e| panic!("Application argument: {}", e));

                // Look up the function's return type once
                let func_return_type = self.get_function_type(&func_name).cloned();

                let mut results = Vec::new();
                for mut extraction in combined {
                    // Create application key from function name and arguments
                    let app_key = ApplicationKey {
                        func_name: func_name.0.clone(),
                        args: extraction.expressions.clone(),
                    };

                    // Check cache and add parameter if first occurrence
                    if let Some(cached_var) = cache.get(&app_key) {
                        // Reuse existing existential variable, don't add parameter
                        let existential = Expression::Variable(cached_var.clone());

                        let mut body_steps = extraction.preceding_steps.concat();
                        let mut predicate_args = extraction.expressions;
                        predicate_args.push(existential.clone());

                        body_steps
                            .push(Proposition::Predicate(func_name.0.clone(), predicate_args));
                        body_steps.push(Proposition::Expr(existential));

                        results.push(BodyPropositionData {
                            input_constraints: vec![],
                            body_steps,
                            additional_parameters: extraction.parameters,
                        });
                    } else {
                        // First occurrence: create new existential and add parameter
                        let exists_var = self.next_var();
                        cache.insert(app_key, exists_var.clone());

                        let existential = Expression::Variable(exists_var.clone());

                        let mut body_steps = extraction.preceding_steps.concat();
                        let mut predicate_args = extraction.expressions;
                        predicate_args.push(existential.clone());

                        body_steps
                            .push(Proposition::Predicate(func_name.0.clone(), predicate_args));
                        body_steps.push(Proposition::Expr(existential));

                        extraction.parameters.push(Parameter::existential(
                            exists_var,
                            func_return_type.clone().unwrap_or_else(|| {
                                panic!("Function '{}' type not registered", func_name)
                            }),
                        ));

                        results.push(BodyPropositionData {
                            input_constraints: vec![],
                            body_steps,
                            additional_parameters: extraction.parameters,
                        });
                    }
                }
                results
            }
            crate::prog_ir::Expression::Match(scrutinee, cases) => {
                // Analyze scrutinee once to get its expression for pattern matching
                let pattern_constraint_base =
                    &Self::extract_single_expr(self.analyze_expression(scrutinee, cache))
                        .unwrap_or_else(|e| panic!("Match scrutinee: {}", e));

                // For each branch of the match, create a result with pattern constraint and branch steps
                let mut results = vec![];
                for (pattern, branch_expr) in cases {
                    // Clone cache for this exclusive branch
                    let mut branch_cache = cache.clone();
                    let branch_results = self.analyze_expression(branch_expr, &mut branch_cache);
                    for branch_body_data in branch_results {
                        let pattern_vars = self.vars_from_pattern(pattern);
                        let pattern_constraint =
                            self.pattern_to_predicate_proposition(pattern_constraint_base, pattern);

                        let (last, rest) = branch_body_data.body_steps.split_last().unwrap();
                        let mut body_steps = rest.to_vec();
                        body_steps.push(self.wrap_result_equality(last));

                        let mut all_vars = Parameter::from_vars(&pattern_vars);
                        all_vars.extend(branch_body_data.additional_parameters);

                        // Combine: outer pattern constraint + any nested pattern constraints + body steps
                        let mut all_patterns = vec![pattern_constraint];
                        all_patterns.extend(branch_body_data.input_constraints.clone());

                        results.push(BodyPropositionData {
                            input_constraints: all_patterns,
                            body_steps,
                            additional_parameters: all_vars,
                        });
                    }
                }
                results
            }
            crate::prog_ir::Expression::IfThenElse {
                condition,
                then_branch,
                else_branch,
            } => {
                let condition_results = self.analyze_expression(condition, cache);
                let mut results = Vec::new();

                for condition_body_data in condition_results {
                    results.extend(self.analyze_ite_branches(
                        &condition_body_data,
                        then_branch,
                        else_branch,
                        cache,
                    ));
                }
                results
            }
            crate::prog_ir::Expression::Not(expr) => {
                let combined = self
                    .extract_exprs_with_steps(vec![expr], cache)
                    .unwrap_or_else(|e| panic!("Not expression: {}", e));

                combined
                    .into_iter()
                    .map(|extraction| {
                        assert_eq!(
                            extraction.expressions.len(),
                            1,
                            "Not requires exactly 1 expression"
                        );
                        let mut body_steps = extraction.preceding_steps.concat();
                        body_steps.push(Proposition::Expr(Expression::Not(Box::new(
                            extraction.expressions[0].clone(),
                        ))));
                        BodyPropositionData {
                            input_constraints: vec![],
                            body_steps,
                            additional_parameters: extraction.parameters,
                        }
                    })
                    .collect()
            }
            crate::prog_ir::Expression::Tuple(expressions) => {
                let combined = self
                    .extract_exprs_with_steps(expressions.iter().collect(), cache)
                    .unwrap_or_else(|e| panic!("Tuple element: {}", e));

                combined
                    .into_iter()
                    .map(|extraction| {
                        let mut body_steps = extraction.preceding_steps.concat();
                        body_steps
                            .push(Proposition::Expr(Expression::Tuple(extraction.expressions)));
                        BodyPropositionData {
                            input_constraints: vec![],
                            body_steps,
                            additional_parameters: extraction.parameters,
                        }
                    })
                    .collect()
            }
        }
    }

    /// Build a configured AxiomBuilderState from all prepared functions
    /// The builder contains the prepared functions and can be used to generate axioms
    pub fn build_all(&self) -> AxiomBuilderState {
        AxiomBuilderState::new(self.type_constructors.clone(), self.prepared.clone())
    }
}

#[cfg(test)]
mod tests {
    use itertools::Itertools as _;

    use crate::{ToLean, test_helpers};

    /// Assert that axiom branches match expected Lean output
    fn assert_axiom_branches(
        actual: &[Vec<crate::spec_ir::Proposition>],
        expected: &[Vec<&str>],
    ) {
        assert_eq!(
            actual.len(),
            expected.len(),
            "Expected {} branches, got {}",
            expected.len(),
            actual.len()
        );
        for (i, (actual_branch, expected_branch)) in actual.iter().zip(expected).enumerate() {
            let actual_lean: Vec<String> =
                actual_branch.iter().map(|p| p.to_lean()).collect();
            let expected_strings: Vec<String> =
                expected_branch.iter().map(|s| s.to_string()).collect();
            assert_eq!(
                actual_lean, expected_strings,
                "Branch {} mismatch",
                i
            );
        }
    }

    #[test]
    fn test_and_predicate_with_non_comparison() {
        // Test AND with an expression and a predicate: should create res_0 ∧ expr, not expr + res_0
        // Using a boolean function that returns true and ANDs with a recursive call
        let program_str = "type [@grind] ilist = Nil | Cons of { head : int; tail : ilist }\nlet [@simp] [@grind] rec all_positive (l : ilist) : bool = match l with | Nil -> true | Cons { head = h; tail = t } -> (h > 0) && all_positive t";
        let props = test_helpers::generate_axioms_for(program_str, "all_positive");

        assert_axiom_branches(
            &props,
            &[
                vec!["(is_nil l)", "(true = res)"],
                vec![
                    "((is_cons l) ∧ ((head l) = h) ∧ ((tail l) = t))",
                    "(all_positive t res_0)",
                    "(((h > 0) ∧ res_0) = res)",
                ],
            ],
        );
    }

    #[test]
    fn test_or_predicate_with_comparison() {
        // Test OR with a comparison and a predicate: should create expr ∨ res_0
        // Using the mem function which ORs a comparison with a recursive call
        let program_str = "type [@grind] ilist = Nil | Cons of { head : int; tail : ilist }\nlet [@simp] [@grind] rec mem (x : int) (l : ilist) : bool = match l with | Nil -> false | Cons { head = h; tail = t } -> (h = x) || mem x t";
        let props = test_helpers::generate_axioms_for(program_str, "mem");

        assert_axiom_branches(
            &props,
            &[
                vec!["(is_nil l)", "(false = res)"],
                vec![
                    "((is_cons l) ∧ ((head l) = h) ∧ ((tail l) = t))",
                    "(mem x t res_0)",
                    "(((h = x) ∨ res_0) = res)",
                ],
            ],
        );
    }

    #[test]
    fn test_nested_and_with_predicates() {
        let program_str = "type [@grind] ilist = Nil | Cons of { head : int; tail : ilist }\nlet [@simp] [@grind] rec all_eq (l : ilist) (x : int) : bool = match l with | Nil -> true | Cons { head = h; tail = t } -> (h = x) && all_eq t x";
        let props = test_helpers::generate_axioms_for(program_str, "all_eq");

        assert_axiom_branches(
            &props,
            &[
                vec!["(is_nil l)", "(true = res)"],
                vec![
                    "((is_cons l) ∧ ((head l) = h) ∧ ((tail l) = t))",
                    "(all_eq t x res_0)",
                    "(((h = x) ∧ res_0) = res)",
                ],
            ],
        );
    }

    #[test]
    fn test_arithmetic_with_predicate() {
        let program_str = "type [@grind] ilist = Nil | Cons of { head : int; tail : ilist }\nlet [@simp] [@grind] rec len (l : ilist) : int = match l with | Nil -> 0 | Cons { head = x; tail = xs } -> 1 + len xs";
        let props = test_helpers::generate_axioms_for(program_str, "len");

        assert_axiom_branches(
            &props,
            &[
                vec!["(is_nil l)", "(0 = res)"],
                vec![
                    "((is_cons l) ∧ ((head l) = x) ∧ ((tail l) = xs))",
                    "(len xs res_0)",
                    "((1 + res_0) = res)",
                ],
            ],
        );
    }

    #[test]
    fn test_nested_match_with_and() {
        let program_str = "type [@grind] ilist = Nil | Cons of { head : int; tail : ilist }\nlet [@simp] [@grind] rec sorted (l : ilist) : bool = match l with | Nil -> true | Cons { head = x; tail = xs } -> match xs with | Nil -> true | Cons { head = y; tail = ys } -> (x <= y) && sorted xs";
        let props = test_helpers::generate_axioms_for(program_str, "sorted");

        assert_axiom_branches(
            &props,
            &[
                vec!["(is_nil l)", "(true = res)"],
                vec![
                    "((is_cons l) ∧ ((head l) = x) ∧ ((tail l) = xs))",
                    "(is_nil xs)",
                    "(true = res)",
                ],
                vec![
                    "((is_cons l) ∧ ((head l) = x) ∧ ((tail l) = xs))",
                    "((is_cons xs) ∧ ((head xs) = y) ∧ ((tail xs) = ys))",
                    "(sorted xs res_0)",
                    "(((x ≤ y) ∧ res_0) = res)",
                ],
            ],
        );
    }

    #[test]
    fn test_ite_in_binary_op() {
        let program_str = "type [@grind] data = Nil | Val of { value : int }\nlet [@simp] [@grind] rec test (d : data) : int = match d with | Nil -> 0 | Val { value = x } -> 1 + ite (x > 0) x 0";
        let props = test_helpers::generate_axioms_for(program_str, "test");

        assert_axiom_branches(
            &props,
            &[
                vec!["(is_nil d)", "(0 = res)"],
                vec![
                    "((is_val d) ∧ ((value d) = x))",
                    "(x > 0)",
                    "((1 + x) = res)",
                ],
                vec![
                    "((is_val d) ∧ ((value d) = x))",
                    "¬((x > 0))",
                    "((1 + 0) = res)",
                ],
            ],
        );
    }

    #[test]
    fn test_tree_height_function() {
        let program_str = "type [@grind] tree = Leaf | Node of { value : int; left : tree; right : tree }

        let [@simp] [@grind] rec height (t : tree) : int = match t with | Leaf -> 0 | Node { value = v; left = l; right = r } -> 1 + ite (height l > height r) (height l) (height r)";
        let props = test_helpers::generate_axioms_for(program_str, "height");

        assert_axiom_branches(
            &props,
            &[
                vec!["(is_leaf t)", "(0 = res)"],
                vec![
                    "((is_node t) ∧ ((value t) = v) ∧ ((left t) = l) ∧ ((right t) = r))",
                    "(height l res_0)",
                    "(height r res_1)",
                    "(res_0 > res_1)",
                    "(height l res_0)",
                    "((1 + res_0) = res)",
                ],
                vec![
                    "((is_node t) ∧ ((value t) = v) ∧ ((left t) = l) ∧ ((right t) = r))",
                    "(height l res_0)",
                    "(height r res_1)",
                    "¬((res_0 > res_1))",
                    "(height r res_1)",
                    "((1 + res_1) = res)",
                ],
            ],
        );
    }

    #[test]
    fn test_simple_ite_expression() {
        let program_str = "type [@grind] ilist = Nil | Cons of { head : int; tail : ilist }\nlet [@simp] [@grind] rec max_or_zero (l : ilist) : int = match l with | Nil -> 0 | Cons { head = h; tail = t } -> ite (h > 0) h 0";
        let props = test_helpers::generate_axioms_for(program_str, "max_or_zero");

        assert_axiom_branches(
            &props,
            &[
                vec!["(is_nil l)", "(0 = res)"],
                vec![
                    "((is_cons l) ∧ ((head l) = h) ∧ ((tail l) = t))",
                    "(h > 0)",
                    "(h = res)",
                ],
                vec![
                    "((is_cons l) ∧ ((head l) = h) ∧ ((tail l) = t))",
                    "¬((h > 0))",
                    "(0 = res)",
                ],
            ],
        );
    }

    #[test]
    fn test_application_deduplication() {
        let program_str = "type [@grind] ilist = Nil | Cons of { head : int; tail : ilist }\nlet [@simp] [@grind] rec max_elem (l : ilist) : int = match l with | Nil -> 0 | Cons { head = h; tail = t } -> ite (h >= (max_elem t)) h (max_elem t)";
        let props = test_helpers::generate_axioms_for(program_str, "max_elem");

        let branch_0: Vec<String> =
            props[0].iter().map(|p| p.to_lean()).collect();
        let branch_1: Vec<String> =
            props[1].iter().map(|p| p.to_lean()).collect();
        let branch_2: Vec<String> =
            props[2].iter().map(|p| p.to_lean()).collect();

        assert_axiom_branches(
            &props,
            &[
                vec!["(is_nil l)", "(0 = res)"],
                vec![
                    "((is_cons l) ∧ ((head l) = h) ∧ ((tail l) = t))",
                    "(max_elem t res_0)",
                    "(h ≥ res_0)",
                    "(h = res)",
                ],
                vec![
                    "((is_cons l) ∧ ((head l) = h) ∧ ((tail l) = t))",
                    "(max_elem t res_0)",
                    "¬((h ≥ res_0))",
                    "(max_elem t res_0)",
                    "(res_0 = res)",
                ],
            ],
        );

        // Verify deduplication
        let res_0_in_true = branch_1.join(" ").matches("res_0").count();
        assert_eq!(res_0_in_true, 2);

        let res_0_in_false = branch_2.join(" ").matches("res_0").count();
        assert_eq!(res_0_in_false, 4);
    }
}

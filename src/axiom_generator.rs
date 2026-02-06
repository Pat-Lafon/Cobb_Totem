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
        if results.len() != 1 {
            return Err(format!(
                "Expected exactly one result, got {}",
                results.len()
            ));
        }
        let body_data = results.into_iter().next().unwrap();
        let total_steps = body_data.pattern_constraints.len() + body_data.body_steps.len();
        if total_steps != 1 {
            return Err(format!(
                "Expected exactly one proposition step, got {}",
                total_steps
            ));
        }
        if !body_data.additional_parameters.is_empty() {
            return Err(format!(
                "Expected no additional universals, got {}",
                body_data.additional_parameters.len()
            ));
        }
        // Pattern constraints should never appear here - extract_single_expr is for simple expressions only
        if !body_data.pattern_constraints.is_empty() {
            return Err(
                "Expected no pattern constraints for simple expression extraction".to_string(),
            );
        }
        match &body_data.body_steps[0] {
            Proposition::Expr(e) => Ok(e.clone()),
            _ => Err("Expected proposition step to be an expression".to_string()),
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
                    let mut all_body_steps = body_data.pattern_constraints.clone();
                    all_body_steps.extend(body_data.body_steps.clone());

                    let (last_prop, preceding) = all_body_steps
                        .split_last()
                        .ok_or("Expected at least one proposition step")?;

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
                panic!()
            }
            crate::prog_ir::Pattern::Variable(_) => {
                panic!()
            }
            crate::prog_ir::Pattern::Constructor(constructor_name, nested_patterns) => {
                // For constructors, generate predicate-based expressions
                let is_cons_pred = Proposition::Predicate(
                    format!("is_{}", constructor_name.get_simple_name().to_lowercase()),
                    vec![scrutinee.clone()],
                );

                // Build field constraints using the actual field names from the type declaration
                let mut field_constraints = vec![];
                for (field_index, nested_pattern) in nested_patterns.iter().enumerate() {
                    // Now match the pattern against this field
                    if let Some(field_constraint) = self.pattern_to_field_equality(
                        scrutinee,
                        constructor_name,
                        field_index,
                        nested_pattern,
                    ) {
                        field_constraints.push(field_constraint);
                    }
                }

                // Combine: (is_cons l) && (field_constraint_0) && (field_constraint_1) && ...
                // For nullary constructors, field_constraints is empty, so result is just the predicate
                let mut result = is_cons_pred;
                for constraint in field_constraints {
                    result = Proposition::And(Box::new(result), Box::new(constraint));
                }
                result
            }
            crate::prog_ir::Pattern::Tuple(patterns) => {
                // For tuple patterns, generate constraints for each element
                let mut result = Proposition::Predicate("true".to_string(), vec![]);
                for (index, pat) in patterns.iter().enumerate() {
                    // Generate tuple element accessor
                    let elem_expr = Expression::Variable(VarName(format!("_tuple_elem_{}", index)));
                    let elem_constraint = self.pattern_to_predicate_proposition(&elem_expr, pat);
                    result = Proposition::And(Box::new(result), Box::new(elem_constraint));
                }
                result
            }
        }
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
        let body_propositions = self.analyze_expression(&binding.body, &mut cache);
        self.prepared.push((binding.clone(), body_propositions));
        Ok(())
    }

    /// Analyze expressions, building propositions
    fn analyze_expression(
        &mut self,
        body: &crate::prog_ir::Expression,
        cache: &mut HashMap<ApplicationKey, VarName>,
    ) -> Vec<BodyPropositionData> {
        match body {
            crate::prog_ir::Expression::Variable(var_name) => vec![BodyPropositionData {
                pattern_constraints: vec![],
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
                    pattern_constraints: vec![],
                    body_steps: vec![Proposition::Expr(Expression::Constructor(
                        constructor_name.clone(),
                        converted_expressions,
                    ))],
                    additional_parameters: vec![],
                }]
            }
            crate::prog_ir::Expression::Literal(literal) => vec![BodyPropositionData {
                pattern_constraints: vec![],
                body_steps: vec![Proposition::Expr(Expression::Literal(literal.clone()))],
                additional_parameters: vec![],
            }],
            crate::prog_ir::Expression::UnaryOp(unary_op, expression) => {
                let combined = self
                    .extract_exprs_with_steps(vec![expression], cache)
                    .unwrap_or_else(|e| panic!("UnaryOp operand: {}", e));

                let mut results = Vec::new();
                for extraction in combined {
                    assert_eq!(
                        extraction.expressions.len(),
                        1,
                        "UnaryOp requires exactly 1 expression, got {}",
                        extraction.expressions.len()
                    );

                    let mut body_steps = extraction.preceding_steps.concat();
                    body_steps.push(Proposition::Expr(Expression::UnaryOp(
                        *unary_op,
                        Box::new(extraction.expressions[0].clone()),
                    )));

                    results.push(BodyPropositionData {
                        pattern_constraints: vec![],
                        body_steps,
                        additional_parameters: extraction.parameters,
                    });
                }
                results
            }
            crate::prog_ir::Expression::BinaryOp(expression, binary_op, expression1) => {
                let combined = self
                    .extract_exprs_with_steps(vec![&expression, &expression1], cache)
                    .unwrap_or_else(|e| panic!("BinaryOp operand: {}", e));

                let mut results = Vec::new();
                for extraction in combined {
                    assert_eq!(
                        extraction.expressions.len(),
                        2,
                        "BinaryOp requires exactly 2 expressions, got {}",
                        extraction.expressions.len()
                    );

                    let mut body_steps = extraction.preceding_steps.concat();
                    body_steps.push(Proposition::Expr(Expression::BinaryOp(
                        Box::new(extraction.expressions[0].clone()),
                        *binary_op,
                        Box::new(extraction.expressions[1].clone()),
                    )));

                    results.push(BodyPropositionData {
                        pattern_constraints: vec![],
                        body_steps,
                        additional_parameters: extraction.parameters,
                    });
                }
                results
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
                            pattern_constraints: vec![],
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
                            pattern_constraints: vec![],
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

                        // Check if the final step is already an equality with RESULT_PARAM
                        let (last, rest) = branch_body_data.body_steps.split_last().unwrap();

                        let mut body_steps = rest.to_vec();

                        if Self::is_result_equality(last) {
                            // Final step is already wrapped with = res, don't wrap again
                            body_steps.push(last.clone());
                        } else {
                            // Wrap the final expression with = RESULT_PARAM
                            let last_expr = last.as_expr();
                            body_steps.push(Proposition::Expr(Expression::BinaryOp(
                                Box::new(last_expr.clone()),
                                crate::prog_ir::BinaryOp::Eq,
                                Box::new(Expression::Variable(RESULT_PARAM.into())),
                            )));
                        }

                        let mut all_vars = Parameter::from_vars(&pattern_vars);
                        all_vars.extend(branch_body_data.additional_parameters);

                        // Combine: outer pattern constraint + any nested pattern constraints + body steps
                        let mut all_patterns = vec![pattern_constraint];
                        all_patterns.extend(branch_body_data.pattern_constraints.clone());

                        results.push(BodyPropositionData {
                            pattern_constraints: all_patterns,
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
                    let (last_cond, preceding_conds) = condition_body_data
                        .body_steps
                        .split_last()
                        .unwrap_or_else(|| panic!("Expected at least one condition step"));
                    let condition_expr = last_cond.as_expr().clone();

                    // Loop over both branches with their bool values
                    for (is_true, branch) in [(true, then_branch), (false, else_branch)] {
                        // Clone cache for this exclusive branch (independent from condition and sibling branch)
                        let mut branch_cache = cache.clone();
                        let branch_results = self.analyze_expression(branch, &mut branch_cache);
                        for branch_body_data in branch_results {
                            // Pattern constraints: from condition + nested patterns in branch
                            let mut pattern_constraints =
                                condition_body_data.pattern_constraints.clone();
                            pattern_constraints
                                .extend(branch_body_data.pattern_constraints.clone());

                            // Body steps: preceding condition steps + condition equality + branch steps
                            let mut body_steps = preceding_conds.to_vec();
                            body_steps.push(Proposition::Expr(Expression::BinaryOp(
                                Box::new(condition_expr.clone()),
                                crate::prog_ir::BinaryOp::Eq,
                                Box::new(Expression::Literal(crate::Literal::Bool(is_true))),
                            )));
                            body_steps.extend(branch_body_data.body_steps);

                            let mut params = condition_body_data.additional_parameters.clone();
                            params.extend(branch_body_data.additional_parameters);

                            results.push(BodyPropositionData {
                                pattern_constraints,
                                body_steps,
                                additional_parameters: params,
                            });
                        }
                    }
                }
                results
            }
            crate::prog_ir::Expression::Not(expr) => {
                // Extract the argument with its preceding steps
                let combined = self
                    .extract_exprs_with_steps(vec![expr], cache)
                    .unwrap_or_else(|e| panic!("Not expression: {}", e));

                let mut results = Vec::new();
                for extraction in combined {
                    assert_eq!(
                        extraction.expressions.len(),
                        1,
                        "Not requires exactly 1 expression, got {}",
                        extraction.expressions.len()
                    );

                    // Flatten all preceding steps
                    let mut body_steps = extraction.preceding_steps.concat();

                    // Add the final Not expression
                    body_steps.push(Proposition::Expr(Expression::Not(Box::new(
                        extraction.expressions[0].clone(),
                    ))));

                    results.push(BodyPropositionData {
                        pattern_constraints: vec![],
                        body_steps,
                        additional_parameters: extraction.parameters,
                    });
                }
                results
            }
            crate::prog_ir::Expression::Tuple(expressions) => {
                let combined = self
                    .extract_exprs_with_steps(expressions.iter().collect(), cache)
                    .unwrap_or_else(|e| panic!("Tuple element: {}", e));

                let mut results = Vec::new();
                for extraction in combined {
                    let mut body_steps = extraction.preceding_steps.concat();
                    body_steps.push(Proposition::Expr(Expression::Tuple(extraction.expressions)));

                    results.push(BodyPropositionData {
                        pattern_constraints: vec![],
                        body_steps,
                        additional_parameters: extraction.parameters,
                    });
                }
                results
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

    #[test]
    fn test_and_predicate_with_non_comparison() {
        // Test AND with an expression and a predicate: should create res_0 ∧ expr, not expr + res_0
        // Using a boolean function that returns true and ANDs with a recursive call
        let program_str = "type [@grind] ilist = Nil | Cons of { head : int; tail : ilist }\nlet [@simp] [@grind] rec all_positive (l : ilist) : bool = match l with | Nil -> true | Cons { head = h; tail = t } -> (h > 0) && all_positive t";
        let props = test_helpers::generate_axioms_for(program_str, "all_positive");

        assert_eq!(
            props[0].iter().map(|p| p.to_lean()).collect_vec(),
            vec!["(is_nil l)", "(true = res)"]
        );

        assert_eq!(
            props[1].iter().map(|p| p.to_lean()).collect_vec(),
            vec![
                "(((is_cons l) ∧ ((head l) = h)) ∧ ((tail l) = t))",
                "(all_positive t res_0)",
                "(((h > 0) ∧ res_0) = res)"
            ]
        );
    }

    #[test]
    fn test_or_predicate_with_comparison() {
        // Test OR with a comparison and a predicate: should create expr ∨ res_0
        // Using the mem function which ORs a comparison with a recursive call
        let program_str = "type [@grind] ilist = Nil | Cons of { head : int; tail : ilist }\nlet [@simp] [@grind] rec mem (x : int) (l : ilist) : bool = match l with | Nil -> false | Cons { head = h; tail = t } -> (h = x) || mem x t";
        let props = test_helpers::generate_axioms_for(program_str, "mem");

        assert_eq!(
            props[0].iter().map(|p| p.to_lean()).collect_vec(),
            vec!["(is_nil l)", "(false = res)"]
        );

        assert_eq!(
            props[1].iter().map(|p| p.to_lean()).collect_vec(),
            vec![
                "(((is_cons l) ∧ ((head l) = h)) ∧ ((tail l) = t))",
                "(mem x t res_0)",
                "(((h = x) ∨ res_0) = res)"
            ]
        );
    }

    #[test]
    fn test_nested_and_with_predicates() {
        // Test AND where both sides involve predicates: all_eq uses AND with predicate
        // all_eq t x: (h = x) && all_eq t x
        let program_str = "type [@grind] ilist = Nil | Cons of { head : int; tail : ilist }\nlet [@simp] [@grind] rec all_eq (l : ilist) (x : int) : bool = match l with | Nil -> true | Cons { head = h; tail = t } -> (h = x) && all_eq t x";
        let props = test_helpers::generate_axioms_for(program_str, "all_eq");

        assert_eq!(
            props[0].iter().map(|p| p.to_lean()).collect_vec(),
            vec!["(is_nil l)", "(true = res)"]
        );

        assert_eq!(
            props[1].iter().map(|p| p.to_lean()).collect_vec(),
            vec![
                "(((is_cons l) ∧ ((head l) = h)) ∧ ((tail l) = t))",
                "(all_eq t x res_0)",
                "(((h = x) ∧ res_0) = res)"
            ]
        );
    }

    #[test]
    fn test_arithmetic_with_predicate() {
        // Test arithmetic operation with a predicate: len uses 1 + recursive call
        // Tests that arithmetic expressions wrap the predicate result properly
        let program_str = "type [@grind] ilist = Nil | Cons of { head : int; tail : ilist }\nlet [@simp] [@grind] rec len (l : ilist) : int = match l with | Nil -> 0 | Cons { head = x; tail = xs } -> 1 + len xs";
        let props = test_helpers::generate_axioms_for(program_str, "len");

        assert_eq!(
            props[0].iter().map(|p| p.to_lean()).collect_vec(),
            vec!["(is_nil l)", "(0 = res)"]
        );

        assert_eq!(
            props[1].iter().map(|p| p.to_lean()).collect_vec(),
            vec![
                "(((is_cons l) ∧ ((head l) = x)) ∧ ((tail l) = xs))",
                "(len xs res_0)",
                "((1 + res_0) = res)"
            ]
        );
    }

    #[test]
    fn test_nested_match_with_and() {
        // Test nested match with AND: sorted has nested matches with AND in innermost branch
        // Pattern: outer match on l, inner match on xs, result has (x <= y) && sorted xs
        let program_str = "type [@grind] ilist = Nil | Cons of { head : int; tail : ilist }\nlet [@simp] [@grind] rec sorted (l : ilist) : bool = match l with | Nil -> true | Cons { head = x; tail = xs } -> match xs with | Nil -> true | Cons { head = y; tail = ys } -> (x <= y) && sorted xs";
        let props = test_helpers::generate_axioms_for(program_str, "sorted");

        // Base case: l = Nil -> true
        assert_eq!(
            props[0].iter().map(|p| p.to_lean()).collect_vec(),
            vec!["(is_nil l)", "(true = res)"]
        );

        // First recursive case: l = Cons, xs = Nil -> true
        assert_eq!(
            props[1].iter().map(|p| p.to_lean()).collect_vec(),
            vec![
                "(((is_cons l) ∧ ((head l) = x)) ∧ ((tail l) = xs))",
                "(is_nil xs)",
                "(true = res)"
            ]
        );

        // Second recursive case: l = Cons, xs = Cons, with AND and predicate
        assert_eq!(
            props[2].iter().map(|p| p.to_lean()).collect_vec(),
            vec![
                "(((is_cons l) ∧ ((head l) = x)) ∧ ((tail l) = xs))",
                "(((is_cons xs) ∧ ((head xs) = y)) ∧ ((tail xs) = ys))",
                "(sorted xs res_0)",
                "(((x ≤ y) ∧ res_0) = res)"
            ]
        );
    }

    #[test]
    fn test_ite_in_binary_op() {
        // Test ite inside a binary operation: 1 + ite(x > 0, x, 0)
        let program_str = "type [@grind] data = Nil | Val of { value : int }\nlet [@simp] [@grind] rec test (d : data) : int = match d with | Nil -> 0 | Val { value = x } -> 1 + ite (x > 0) x 0";
        let props = test_helpers::generate_axioms_for(program_str, "test");

        // Base case: Nil -> 0
        assert_eq!(
            props[0].iter().map(|p| p.to_lean()).collect_vec(),
            vec!["(is_nil d)", "(0 = res)"]
        );

        // Recursive case: Val with ite - true branch (x > 0)
        assert_eq!(
            props[1].iter().map(|p| p.to_lean()).collect_vec(),
            vec![
                "((is_val d) ∧ ((value d) = x))",
                "((x > 0) = true)",
                "((1 + x) = res)"
            ]
        );

        // Recursive case: Val with ite - false branch (x > 0 is false)
        assert_eq!(
            props[2].iter().map(|p| p.to_lean()).collect_vec(),
            vec![
                "((is_val d) ∧ ((value d) = x))",
                "((x > 0) = false)",
                "((1 + 0) = res)"
            ]
        );
    }

    #[test]
    fn test_tree_height_function() {
        // Test tree height function with binary tree structure
        let program_str = "type [@grind] tree = Leaf | Node of { value : int; left : tree; right : tree }

        let [@simp] [@grind] rec height (t : tree) : int = match t with | Leaf -> 0 | Node { value = v; left = l; right = r } -> 1 + ite (height l > height r) (height l) (height r)";
        let props = test_helpers::generate_axioms_for(program_str, "height");

        // Base case: Leaf -> 0
        assert_eq!(
            props[0].iter().map(|p| p.to_lean()).collect_vec(),
            vec!["(is_leaf t)", "(0 = res)"]
        );

        // Recursive case: Node with ite - true branch (height l > height r)
        // Condition sets up res_0 = height l, res_1 = height r
        // True branch reuses res_0 from condition
        assert_eq!(
            props[1].iter().map(|p| p.to_lean()).collect_vec(),
            vec![
                "((((is_node t) ∧ ((value t) = v)) ∧ ((left t) = l)) ∧ ((right t) = r))",
                "(height l res_0)",
                "(height r res_1)",
                "((res_0 > res_1) = true)",
                "(height l res_0)",
                "((1 + res_0) = res)"
            ]
        );

        // Recursive case: Node with ite - false branch (height l > height r is false)
        // False branch shares res_0, res_1 from condition and reuses them
        assert_eq!(
            props[2].iter().map(|p| p.to_lean()).collect_vec(),
            vec![
                "((((is_node t) ∧ ((value t) = v)) ∧ ((left t) = l)) ∧ ((right t) = r))",
                "(height l res_0)",
                "(height r res_1)",
                "((res_0 > res_1) = false)",
                "(height r res_1)",
                "((1 + res_1) = res)"
            ]
        );
    }

    #[test]
    fn test_simple_ite_expression() {
        // Test ite in simple form without nested predicates or operators
        let program_str = "type [@grind] ilist = Nil | Cons of { head : int; tail : ilist }\nlet [@simp] [@grind] rec max_or_zero (l : ilist) : int = match l with | Nil -> 0 | Cons { head = h; tail = t } -> ite (h > 0) h 0";
        let props = test_helpers::generate_axioms_for(program_str, "max_or_zero");

        // Base case: Nil -> 0
        assert_eq!(
            props[0].iter().map(|p| p.to_lean()).collect_vec(),
            vec!["(is_nil l)", "(0 = res)"]
        );

        // Recursive case: Cons with ite - true branch (h > 0)
        assert_eq!(
            props[1].iter().map(|p| p.to_lean()).collect_vec(),
            vec![
                "(((is_cons l) ∧ ((head l) = h)) ∧ ((tail l) = t))",
                "((h > 0) = true)",
                "(h = res)"
            ]
        );

        // Recursive case: Cons with ite - false branch (h > 0 is false)
        assert_eq!(
            props[2].iter().map(|p| p.to_lean()).collect_vec(),
            vec![
                "(((is_cons l) ∧ ((head l) = h)) ∧ ((tail l) = t))",
                "((h > 0) = false)",
                "(0 = res)"
            ]
        );
    }

    #[test]
    fn test_application_deduplication() {
        // Test that duplicate function applications in the same branch reuse the same existential
        // Function calls the same recursive function twice: max(a, b) = ite (a >= b) a b
        let program_str = "type [@grind] ilist = Nil | Cons of { head : int; tail : ilist }\nlet [@simp] [@grind] rec max_elem (l : ilist) : int = match l with | Nil -> 0 | Cons { head = h; tail = t } -> ite (h >= (max_elem t)) h (max_elem t)";
        let props = test_helpers::generate_axioms_for(program_str, "max_elem");

        // Base case: Nil -> 0
        assert_eq!(
            props[0].iter().map(|p| p.to_lean()).collect_vec(),
            vec!["(is_nil l)", "(0 = res)"]
        );

        // Recursive case: Cons with ite - true branch (h >= max_elem t)
        // The condition references max_elem t once, should reuse same res_0
        let props_1 = props[1].iter().map(|p| p.to_lean()).collect_vec();
        assert_eq!(
            props_1,
            vec![
                "(((is_cons l) ∧ ((head l) = h)) ∧ ((tail l) = t))",
                "(max_elem t res_0)",
                "((h ≥ res_0) = true)",
                "(h = res)"
            ]
        );

        // Recursive case: Cons with ite - false branch (h >= max_elem t is false)
        // Both branches share the condition's cache (max_elem t = res_0 from condition)
        // So the false branch body reuses res_0
        let props_2 = props[2].iter().map(|p| p.to_lean()).collect_vec();
        assert_eq!(
            props_2,
            vec![
                "(((is_cons l) ∧ ((head l) = h)) ∧ ((tail l) = t))",
                "(max_elem t res_0)",
                "((h ≥ res_0) = false)",
                "(max_elem t res_0)",
                "(res_0 = res)"
            ]
        );

        // Verify deduplication: within each branch, max_elem t is deduplicated
        let res_0_in_true = props_1.join(" ").matches("res_0").count();
        assert_eq!(
            res_0_in_true, 2,
            "True branch: res_0 should appear 2 times (predicate + condition), got {}",
            res_0_in_true
        );

        // False branch also shares res_0 from condition: appears in predicate, condition, result predicate, and result expr
        let res_0_in_false = props_2.join(" ").matches("res_0").count();
        assert_eq!(
            res_0_in_false, 4,
            "False branch: res_0 should appear 4 times (predicate + condition + result predicate + result expr), got {}",
            res_0_in_false
        );
    }
}

use std::collections::HashMap;

use itertools::Itertools;

use crate::VarName;
use crate::axiom_builder_state::{AxiomBuilderState, BodyPropositionData};
use crate::create_wrapper::{RESULT_PARAM, wrapper_name};
use crate::prog_ir::{LetBinding, Type, TypeDecl};
use crate::spec_ir::{Expression, Parameter, Proposition};

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
                    .and_then(|variant| variant.fields.get(field_index).cloned())
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
        if body_data.proposition_steps.len() != 1 {
            return Err(format!(
                "Expected exactly one proposition step, got {}",
                body_data.proposition_steps.len()
            ));
        }
        if !body_data.additional_parameters.is_empty() {
            return Err(format!(
                "Expected no additional universals, got {}",
                body_data.additional_parameters.len()
            ));
        }
        match &body_data.proposition_steps[0] {
            Proposition::Expr(e) => Ok(e.clone()),
            _ => Err("Expected proposition step to be an expression".to_string()),
        }
    }

    /// Extract expressions with their preceding proposition steps and parameters.
    /// Returns all combinations of results across the input expressions.
    /// Each result tuple contains: the final expressions, preceding propositions, and new parameters.
    fn extract_exprs_with_steps(
        &mut self,
        exprs: Vec<&crate::prog_ir::Expression>,
    ) -> Result<Vec<(Vec<Expression>, Vec<Vec<Proposition>>, Vec<Parameter>)>, String> {
        let all_results: Vec<Vec<BodyPropositionData>> = exprs
            .iter()
            .map(|expr| self.from_expression(expr))
            .collect();

        all_results
            .into_iter()
            .multi_cartesian_product()
            .map(|combination| {
                let mut all_exprs = Vec::new();
                let mut all_steps = Vec::new();
                let mut all_params = Vec::new();

                for body_data in combination {
                    let (last_prop, preceding) = body_data
                        .proposition_steps
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

                Ok((all_exprs, all_steps, all_params))
            })
            .collect()
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

    /// Convert a pattern to a spec_ir Expression
    fn expr_from_pattern(&self, pattern: &crate::prog_ir::Pattern) -> Expression {
        match pattern {
            crate::prog_ir::Pattern::Variable(name) => Expression::Variable(name.clone()),
            crate::prog_ir::Pattern::Constructor(name, nested_patterns) => {
                let converted_patterns: Vec<_> = nested_patterns
                    .iter()
                    .map(|p| self.expr_from_pattern(p))
                    .collect();
                Expression::Constructor(name.clone(), converted_patterns)
            }
            crate::prog_ir::Pattern::Literal(lit) => Expression::Literal(lit.clone()),
            crate::prog_ir::Pattern::Wildcard => {
                panic!("Wildcard patterns are not supported in axiom generation")
            }
            crate::prog_ir::Pattern::Tuple(patterns) => {
                let elements = patterns.iter().map(|p| self.expr_from_pattern(p)).collect();
                Expression::Tuple(elements)
            }
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
        let body_propositions = self.from_expression(&binding.body);
        self.prepared.push((binding.clone(), body_propositions));
        Ok(())
    }

    /// Analyze expressions, building propositions
    fn from_expression(&mut self, body: &crate::prog_ir::Expression) -> Vec<BodyPropositionData> {
        match body {
            crate::prog_ir::Expression::Variable(var_name) => vec![BodyPropositionData {
                proposition_steps: vec![Proposition::Expr(Expression::Variable(var_name.clone()))],
                additional_parameters: vec![],
            }],
            crate::prog_ir::Expression::Constructor(constructor_name, expressions) => {
                let converted_expressions: Vec<_> = expressions
                    .iter()
                    .map(|expr| {
                        Self::extract_single_expr(self.from_expression(expr))
                            .unwrap_or_else(|e| panic!("Constructor argument: {}", e))
                    })
                    .collect();
                vec![BodyPropositionData {
                    proposition_steps: vec![Proposition::Expr(Expression::Constructor(
                        constructor_name.clone(),
                        converted_expressions,
                    ))],
                    additional_parameters: vec![],
                }]
            }
            crate::prog_ir::Expression::Literal(literal) => vec![BodyPropositionData {
                proposition_steps: vec![Proposition::Expr(Expression::Literal(literal.clone()))],
                additional_parameters: vec![],
            }],
            crate::prog_ir::Expression::UnaryOp(unary_op, expression) => {
                let combined = self
                    .extract_exprs_with_steps(vec![expression])
                    .unwrap_or_else(|e| panic!("UnaryOp operand: {}", e));

                let mut results = Vec::new();
                for (exprs, preceding_steps_list, params) in combined {
                    assert_eq!(
                        exprs.len(),
                        1,
                        "UnaryOp requires exactly 1 expression, got {}",
                        exprs.len()
                    );

                    let mut proposition_steps = preceding_steps_list.concat();
                    proposition_steps.push(Proposition::Expr(Expression::UnaryOp(
                        *unary_op,
                        Box::new(exprs[0].clone()),
                    )));

                    results.push(BodyPropositionData {
                        proposition_steps,
                        additional_parameters: params,
                    });
                }
                results
            }
            crate::prog_ir::Expression::BinaryOp(expression, binary_op, expression1) => {
                let combined = self
                    .extract_exprs_with_steps(vec![&expression, &expression1])
                    .unwrap_or_else(|e| panic!("BinaryOp operand: {}", e));

                let mut results = Vec::new();
                for (exprs, preceding_steps_list, params) in combined {
                    assert_eq!(
                        exprs.len(),
                        2,
                        "BinaryOp requires exactly 2 expressions, got {}",
                        exprs.len()
                    );

                    let mut proposition_steps = preceding_steps_list.concat();
                    proposition_steps.push(Proposition::Expr(Expression::BinaryOp(
                        Box::new(exprs[0].clone()),
                        *binary_op,
                        Box::new(exprs[1].clone()),
                    )));

                    results.push(BodyPropositionData {
                        proposition_steps,
                        additional_parameters: params,
                    });
                }
                results
            }
            crate::prog_ir::Expression::Application(func_expr, arg_exprs) => {
                let func_body_data = Self::extract_single_expr(self.from_expression(func_expr))
                    .unwrap_or_else(|e| panic!("Application function: {}", e));

                let func_name = match func_body_data {
                    Expression::Variable(v) => v,
                    _ => panic!(
                        "Application function must evaluate to a variable, got: {:?}",
                        func_body_data
                    ),
                };

                // Create a wrapper predicate with an existential parameter for function applications
                let combined = self
                    .extract_exprs_with_steps(arg_exprs.iter().collect())
                    .unwrap_or_else(|e| panic!("Application argument: {}", e));

                let mut results = Vec::new();
                for (mut converted_args, preceding_steps_per_arg, arg_params) in combined {
                    let exists_var = self.next_var();
                    let existential = Expression::Variable(exists_var.clone());

                    let func_name_wrapper = wrapper_name(&func_name);
                    converted_args.push(existential.clone());

                    // Flatten all preceding steps from arguments
                    let mut proposition_steps = preceding_steps_per_arg.concat();
                    proposition_steps
                        .push(Proposition::Predicate(func_name_wrapper, converted_args));
                    proposition_steps.push(Proposition::Expr(existential.clone()));

                    // Look up the function's return type if available
                    let func_return_type = self.get_function_type(&func_name).cloned();

                    let mut additional_parameters = arg_params;
                    additional_parameters.push(Parameter::existential(
                        exists_var,
                        func_return_type.unwrap_or_else(|| {
                            panic!("Function '{}' type not registered", func_name)
                        }),
                    ));

                    results.push(BodyPropositionData {
                        proposition_steps,
                        additional_parameters,
                    });
                }
                results
            }
            crate::prog_ir::Expression::Match(scrutinee, cases) => {
                // Analyze scrutinee once to get its expression for pattern matching
                let pattern_constraint_base =
                    &Self::extract_single_expr(self.from_expression(scrutinee))
                        .unwrap_or_else(|e| panic!("Match scrutinee: {}", e));

                // For each branch of the match, create a result with pattern constraint and branch steps
                let mut results = vec![];
                for (pattern, branch_expr) in cases {
                    let branch_results = self.from_expression(branch_expr);
                    for branch_body_data in branch_results {
                        let pattern_vars = self.vars_from_pattern(pattern);
                        let pattern_expr = self.expr_from_pattern(pattern);
                        let pattern_constraint = Proposition::Expr(Expression::BinaryOp(
                            Box::new(pattern_constraint_base.clone()),
                            crate::prog_ir::BinaryOp::Eq,
                            Box::new(pattern_expr),
                        ));

                        // Check if the final step is already an equality with RESULT_PARAM
                        let (last, rest) = branch_body_data.proposition_steps.split_last().unwrap();

                        let mut final_steps = vec![pattern_constraint];
                        final_steps.extend(rest.to_vec());

                        if Self::is_result_equality(last) {
                            // Final step is already wrapped with = res, don't wrap again
                            final_steps.push(last.clone());
                        } else {
                            // Wrap the final expression with = RESULT_PARAM
                            let last_expr = last.as_expr();
                            final_steps.push(Proposition::Expr(Expression::BinaryOp(
                                Box::new(last_expr.clone()),
                                crate::prog_ir::BinaryOp::Eq,
                                Box::new(Expression::Variable(RESULT_PARAM.into())),
                            )));
                        }

                        let mut all_vars = Parameter::from_vars(&pattern_vars);
                        all_vars.extend(branch_body_data.additional_parameters);
                        results.push(BodyPropositionData {
                            proposition_steps: final_steps,
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
                let condition_results = self.from_expression(condition);
                let mut results = Vec::new();

                for condition_body_data in condition_results {
                    let (last_cond, preceding_conds) = condition_body_data
                        .proposition_steps
                        .split_last()
                        .unwrap_or_else(|| panic!("Expected at least one condition step"));
                    let condition_expr = last_cond.as_expr().clone();

                    // Loop over both branches with their bool values
                    for (is_true, branch) in [(true, then_branch), (false, else_branch)] {
                        let branch_results = self.from_expression(branch);
                        for branch_body_data in branch_results {
                            let mut steps: Vec<Proposition> = preceding_conds.to_vec();
                            steps.push(Proposition::Expr(Expression::BinaryOp(
                                Box::new(condition_expr.clone()),
                                crate::prog_ir::BinaryOp::Eq,
                                Box::new(Expression::Literal(crate::Literal::Bool(is_true))),
                            )));
                            steps.extend(branch_body_data.proposition_steps);

                            let mut params = condition_body_data.additional_parameters.clone();
                            params.extend(branch_body_data.additional_parameters);

                            results.push(BodyPropositionData {
                                proposition_steps: steps,
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
                    .extract_exprs_with_steps(vec![expr])
                    .unwrap_or_else(|e| panic!("Not expression: {}", e));

                let mut results = Vec::new();
                for (exprs, preceding_steps_list, params) in combined {
                    assert_eq!(
                        exprs.len(),
                        1,
                        "Not requires exactly 1 expression, got {}",
                        exprs.len()
                    );

                    // Flatten all preceding steps
                    let mut all_steps = preceding_steps_list.concat();

                    // Add the final Not expression
                    all_steps.push(Proposition::Expr(Expression::Not(Box::new(
                        exprs[0].clone(),
                    ))));

                    results.push(BodyPropositionData {
                        proposition_steps: all_steps,
                        additional_parameters: params,
                    });
                }
                results
            }
            crate::prog_ir::Expression::Tuple(expressions) => {
                let combined = self
                    .extract_exprs_with_steps(expressions.iter().collect())
                    .unwrap_or_else(|e| panic!("Tuple element: {}", e));

                let mut results = Vec::new();
                for (exprs, preceding_steps_list, params) in combined {
                    let mut proposition_steps = preceding_steps_list.concat();
                    proposition_steps.push(Proposition::Expr(Expression::Tuple(exprs)));

                    results.push(BodyPropositionData {
                        proposition_steps,
                        additional_parameters: params,
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
        let program_str = "type [@grind] ilist = Nil | Cons of int * ilist\nlet [@simp] [@grind] rec all_positive (l : ilist) : bool = match l with | Nil -> true | Cons (h, t) -> (h > 0) && all_positive t";
        let props = test_helpers::generate_axioms_for(program_str, "all_positive");

        assert_eq!(
            props[0].iter().map(|p| p.to_lean()).collect_vec(),
            vec!["(l = .Nil)", "(true = res)"]
        );

        assert_eq!(
            props[1].iter().map(|p| p.to_lean()).collect_vec(),
            vec![
                "(l = (.Cons h t))",
                "(all_positive_wrapper t res_0)",
                "(((h > 0) ∧ res_0) = res)"
            ]
        );
    }

    #[test]
    fn test_or_predicate_with_comparison() {
        // Test OR with a comparison and a predicate: should create expr ∨ res_0
        // Using the mem function which ORs a comparison with a recursive call
        let program_str = "type [@grind] ilist = Nil | Cons of int * ilist\nlet [@simp] [@grind] rec mem (x : int) (l : ilist) : bool = match l with | Nil -> false | Cons (h, t) -> (h = x) || mem x t";
        let props = test_helpers::generate_axioms_for(program_str, "mem");

        assert_eq!(
            props[0].iter().map(|p| p.to_lean()).collect_vec(),
            vec!["(l = .Nil)", "(false = res)"]
        );

        assert_eq!(
            props[1].iter().map(|p| p.to_lean()).collect_vec(),
            vec![
                "(l = (.Cons h t))",
                "(mem_wrapper x t res_0)",
                "(((h = x) ∨ res_0) = res)"
            ]
        );
    }

    #[test]
    fn test_nested_and_with_predicates() {
        // Test AND where both sides involve predicates: all_eq uses AND with predicate
        // all_eq t x: (h = x) && all_eq t x
        let program_str = "type [@grind] ilist = Nil | Cons of int * ilist\nlet [@simp] [@grind] rec all_eq (l : ilist) (x : int) : bool = match l with | Nil -> true | Cons (h, t) -> (h = x) && all_eq t x";
        let props = test_helpers::generate_axioms_for(program_str, "all_eq");

        assert_eq!(
            props[0].iter().map(|p| p.to_lean()).collect_vec(),
            vec!["(l = .Nil)", "(true = res)"]
        );

        assert_eq!(
            props[1].iter().map(|p| p.to_lean()).collect_vec(),
            vec![
                "(l = (.Cons h t))",
                "(all_eq_wrapper t x res_0)",
                "(((h = x) ∧ res_0) = res)"
            ]
        );
    }

    #[test]
    fn test_arithmetic_with_predicate() {
        // Test arithmetic operation with a predicate: len uses 1 + recursive call
        // Tests that arithmetic expressions wrap the predicate result properly
        let program_str = "type [@grind] ilist = Nil | Cons of int * ilist\nlet [@simp] [@grind] rec len (l : ilist) : int = match l with | Nil -> 0 | Cons (x, xs) -> 1 + len xs";
        let props = test_helpers::generate_axioms_for(program_str, "len");

        assert_eq!(
            props[0].iter().map(|p| p.to_lean()).collect_vec(),
            vec!["(l = .Nil)", "(0 = res)"]
        );

        assert_eq!(
            props[1].iter().map(|p| p.to_lean()).collect_vec(),
            vec![
                "(l = (.Cons x xs))",
                "(len_wrapper xs res_0)",
                "((1 + res_0) = res)"
            ]
        );
    }

    #[test]
    fn test_nested_match_with_and() {
        // Test nested match with AND: sorted has nested matches with AND in innermost branch
        // Pattern: outer match on l, inner match on xs, result has (x <= y) && sorted xs
        let program_str = "type [@grind] ilist = Nil | Cons of int * ilist\nlet [@simp] [@grind] rec sorted (l : ilist) : bool = match l with | Nil -> true | Cons (x, xs) -> match xs with | Nil -> true | Cons (y, ys) -> (x <= y) && sorted xs";
        let props = test_helpers::generate_axioms_for(program_str, "sorted");

        // Base case: l = Nil -> true
        assert_eq!(
            props[0].iter().map(|p| p.to_lean()).collect_vec(),
            vec!["(l = .Nil)", "(true = res)"]
        );

        // First recursive case: l = Cons, xs = Nil -> true
        assert_eq!(
            props[1].iter().map(|p| p.to_lean()).collect_vec(),
            vec!["(l = (.Cons x xs))", "(xs = .Nil)", "(true = res)"]
        );

        // Second recursive case: l = Cons, xs = Cons, with AND and predicate
        assert_eq!(
            props[2].iter().map(|p| p.to_lean()).collect_vec(),
            vec![
                "(l = (.Cons x xs))",
                "(xs = (.Cons y ys))",
                "(sorted_wrapper xs res_0)",
                "(((x ≤ y) ∧ res_0) = res)"
            ]
        );
    }

    #[test]
    fn test_ite_in_binary_op() {
        // Test ite inside a binary operation: 1 + ite(x > 0, x, 0)
        let program_str = "type [@grind] data = Nil | Val of int\nlet [@simp] [@grind] rec test (d : data) : int = match d with | Nil -> 0 | Val (x) -> 1 + ite (x > 0) x 0";
        let props = test_helpers::generate_axioms_for(program_str, "test");

        // Base case: Nil -> 0
        assert_eq!(
            props[0].iter().map(|p| p.to_lean()).collect_vec(),
            vec!["(d = .Nil)", "(0 = res)"]
        );

        // Recursive case: Val with ite - true branch (x > 0)
        assert_eq!(
            props[1].iter().map(|p| p.to_lean()).collect_vec(),
            vec!["(d = (.Val x))", "((x > 0) = true)", "((1 + x) = res)"]
        );

        // Recursive case: Val with ite - false branch (x > 0 is false)
        assert_eq!(
            props[2].iter().map(|p| p.to_lean()).collect_vec(),
            vec!["(d = (.Val x))", "((x > 0) = false)", "((1 + 0) = res)"]
        );
    }

    #[test]
    fn test_tree_height_function() {
        // Test tree height function with binary tree structure
        let program_str = "type [@grind] tree = Leaf | Node of int * tree * tree

        let [@simp] [@grind] rec height (t : tree) : int = match t with | Leaf -> 0 | Node (v, l, r) -> 1 + ite (height l > height r) (height l) (height r)";
        let props = test_helpers::generate_axioms_for(program_str, "height");

        // Base case: Leaf -> 0
        assert_eq!(
            props[0].iter().map(|p| p.to_lean()).collect_vec(),
            vec!["(t = .Leaf)", "(0 = res)"]
        );

        // Recursive case: Node with ite - true branch (height l > height r)
        assert_eq!(
            props[1].iter().map(|p| p.to_lean()).collect_vec(),
            vec![
                "(t = (.Node v l r))",
                "(height_wrapper l res_0)",
                "(height_wrapper r res_1)",
                "((res_0 > res_1) = true)",
                "(height_wrapper l res_2)",
                "((1 + res_2) = res)"
            ]
        );

        // Recursive case: Node with ite - false branch (height l > height r is false)
        assert_eq!(
            props[2].iter().map(|p| p.to_lean()).collect_vec(),
            vec![
                "(t = (.Node v l r))",
                "(height_wrapper l res_0)",
                "(height_wrapper r res_1)",
                "((res_0 > res_1) = false)",
                "(height_wrapper r res_3)",
                "((1 + res_3) = res)"
            ]
        );
    }

    #[test]
    fn test_simple_ite_expression() {
        // Test ite in simple form without nested predicates or operators
        let program_str = "type [@grind] ilist = Nil | Cons of int * ilist\nlet [@simp] [@grind] rec max_or_zero (l : ilist) : int = match l with | Nil -> 0 | Cons (h, t) -> ite (h > 0) h 0";
        let props = test_helpers::generate_axioms_for(program_str, "max_or_zero");

        // Base case: Nil -> 0
        assert_eq!(
            props[0].iter().map(|p| p.to_lean()).collect_vec(),
            vec!["(l = .Nil)", "(0 = res)"]
        );

        // Recursive case: Cons with ite - true branch (h > 0)
        assert_eq!(
            props[1].iter().map(|p| p.to_lean()).collect_vec(),
            vec!["(l = (.Cons h t))", "((h > 0) = true)", "(h = res)"]
        );

        // Recursive case: Cons with ite - false branch (h > 0 is false)
        assert_eq!(
            props[2].iter().map(|p| p.to_lean()).collect_vec(),
            vec!["(l = (.Cons h t))", "((h > 0) = false)", "(0 = res)"]
        );
    }
}

use crate::VarName;
use crate::axiom_builder_state::{AxiomBuilderState, BodyPropositionData};
use crate::create_wrapper::{RESULT_PARAM, wrapper_name};
use crate::prog_ir::{LetBinding, Type, TypeDecl};
use crate::spec_ir::{Expression, Parameter, Proposition};

/// Generates axioms in the spec IR from parsed program IR functions.
#[derive(Clone)]
pub struct AxiomGenerator {
    /// Type declarations for looking up constructor types
    type_constructors: Vec<TypeDecl>,
    /// Counter for generating unique variable names (e.g., res_0, res_1, ...)
    var_counter: usize,
    /// Map of function names to their return types
    function_types: std::collections::HashMap<VarName, Type>,
}

impl AxiomGenerator {
    /// Create a new AxiomGenerator with the given type constructors
    pub fn new(type_constructors: Vec<TypeDecl>) -> Self {
        Self {
            type_constructors,
            var_counter: 0,
            function_types: std::collections::HashMap::new(),
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
            .expect(&format!(
                "Failed to find constructor {} at index {}",
                constructor_name, field_index
            ))
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
    /// For each argument, returns: the final expression, preceding propositions, and new parameters.
    fn extract_exprs_with_steps(
        &mut self,
        exprs: Vec<&crate::prog_ir::Expression>,
    ) -> Result<(Vec<Expression>, Vec<Vec<Proposition>>, Vec<Parameter>), String> {
        let mut all_exprs = Vec::new();
        let mut all_preceding_steps = Vec::new();
        let mut all_params = Vec::new();

        for expr in exprs {
            let results = self.from_expression(expr);
            if results.len() != 1 {
                return Err(format!(
                    "Expected exactly one result, got {}",
                    results.len()
                ));
            }
            let body_data = results.into_iter().next().unwrap();

            let (last_prop, preceding) = body_data
                .proposition_steps
                .split_last()
                .ok_or("Expected at least one proposition step")?;

            match last_prop {
                Proposition::Expr(e) => {
                    all_exprs.push(e.clone());
                    all_preceding_steps.push(preceding.to_vec());
                    all_params.extend(body_data.additional_parameters);
                }
                _ => return Err("Expected final step to be an expression".to_string()),
            }
        }

        Ok((all_exprs, all_preceding_steps, all_params))
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
            crate::prog_ir::Pattern::Wildcard => unimplemented!(),
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
                unimplemented!()
            }
        }
    }

    /// Analyze a function and return an intermediate builder state
    pub fn prepare_function(&mut self, binding: &LetBinding) -> Result<AxiomBuilderState, String> {
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

        Ok(AxiomBuilderState::new(
            self.type_constructors.clone(),
            binding.clone(),
            body_propositions,
        ))
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
                let (exprs, preceding_steps_list, params) = self
                    .extract_exprs_with_steps(vec![expression])
                    .unwrap_or_else(|e| panic!("UnaryOp operand: {}", e));

                assert_eq!(exprs.len(), 1, "UnaryOp requires exactly 1 expression");

                let mut proposition_steps = preceding_steps_list.concat();
                proposition_steps.push(Proposition::Expr(Expression::UnaryOp(
                    *unary_op,
                    Box::new(exprs[0].clone()),
                )));

                vec![BodyPropositionData {
                    proposition_steps,
                    additional_parameters: params,
                }]
            }
            crate::prog_ir::Expression::BinaryOp(expression, binary_op, expression1) => {
                let (exprs, preceding_steps_list, params) = self
                    .extract_exprs_with_steps(vec![&expression, &expression1])
                    .unwrap_or_else(|e| panic!("BinaryOp operand: {}", e));

                assert_eq!(exprs.len(), 2, "BinaryOp requires exactly 2 expressions");

                let mut proposition_steps = preceding_steps_list.concat();
                proposition_steps.push(Proposition::Expr(Expression::BinaryOp(
                    Box::new(exprs[0].clone()),
                    *binary_op,
                    Box::new(exprs[1].clone()),
                )));

                vec![BodyPropositionData {
                    proposition_steps,
                    additional_parameters: params,
                }]
            }
            crate::prog_ir::Expression::Application(func_expr, arg_exprs) => {
                let func_body_data = Self::extract_single_expr(self.from_expression(func_expr))
                    .unwrap_or_else(|e| panic!("Application function: {}", e));

                let func_name = match func_body_data {
                    Expression::Variable(v) => v,
                    _ => panic!("Not sure yet"),
                };

                // Create a wrapper predicate with an existential parameter for function applications
                let (mut converted_args, preceding_steps_per_arg, arg_params) = self
                    .extract_exprs_with_steps(arg_exprs.iter().collect())
                    .unwrap_or_else(|e| panic!("Application argument: {}", e));

                let exists_var = self.next_var();
                let existential = Expression::Variable(exists_var.clone());

                let func_name_wrapper = wrapper_name(&func_name);
                converted_args.push(existential.clone());

                // Flatten all preceding steps from arguments
                let mut proposition_steps = preceding_steps_per_arg.concat();
                proposition_steps.push(Proposition::Predicate(func_name_wrapper, converted_args));
                proposition_steps.push(Proposition::Expr(existential.clone()));

                // Look up the function's return type if available
                let func_return_type = self.get_function_type(&func_name).cloned();

                let mut additional_parameters = arg_params;
                additional_parameters.push(Parameter::existential(
                    exists_var,
                    func_return_type
                        .unwrap_or_else(|| panic!("Function '{}' type not registered", func_name)),
                ));

                vec![BodyPropositionData {
                    proposition_steps,
                    additional_parameters,
                }]
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
                    let result_toggle = branch_results.len() == 1;
                    for branch_body_data in branch_results {
                        let pattern_vars = self.vars_from_pattern(pattern);
                        let pattern_constraint = Proposition::Expr(Expression::BinaryOp(
                            Box::new(pattern_constraint_base.clone()),
                            crate::prog_ir::BinaryOp::Eq,
                            Box::new(self.expr_from_pattern(pattern)),
                        ));
                        let final_steps = if result_toggle {
                            let (last, rest) =
                                branch_body_data.proposition_steps.split_last().unwrap();
                            let mut bop = rest.to_vec();
                            bop.push(Proposition::Expr(
                                Expression::BinaryOp(
                                    Box::new(last.as_expr().clone()),
                                    crate::prog_ir::BinaryOp::Eq,
                                    Box::new(Expression::Variable(RESULT_PARAM.into())),
                                ), /*   Box::new(.clone()),
                                   Box::new(Proposition::Expr()), */
                            ));
                            let mut steps = vec![pattern_constraint.clone()];
                            steps.extend(bop);
                            steps
                        } else {
                            let mut steps = vec![pattern_constraint.clone()];
                            steps.extend(branch_body_data.proposition_steps);
                            steps
                        };
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
                // Extract condition, then, and else branches with their preceding steps
                let (exprs, preceding_steps_list, params) = self
                    .extract_exprs_with_steps(vec![condition, then_branch, else_branch])
                    .unwrap_or_else(|e| panic!("IfThenElse expression: {}", e));

                assert_eq!(exprs.len(), 3, "IfThenElse requires exactly 3 expressions");

                // Flatten all preceding steps from all three branches
                let mut all_steps = preceding_steps_list.concat();

                // Add the final IfThenElse expression
                all_steps.push(Proposition::Expr(Expression::IfThenElse {
                    condition: Box::new(exprs[0].clone()),
                    then_branch: Box::new(exprs[1].clone()),
                    else_branch: Box::new(exprs[2].clone()),
                }));

                vec![BodyPropositionData {
                    proposition_steps: all_steps,
                    additional_parameters: params,
                }]
            }
            crate::prog_ir::Expression::Tuple(_expressions) => todo!(),
        }
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

        // Recursive case: Node with height computation
        assert_eq!(
            props[1].iter().map(|p| p.to_lean()).collect_vec(),
            vec![
                "(t = (.Node v l r))",
                "(height_wrapper l res_0)",
                "(height_wrapper r res_1)",
                "(height_wrapper l res_2)",
                "(height_wrapper r res_3)",
                "((1 + (ite (res_0 > res_1) res_2 res_3)) = res)"
            ]
        );
    }
}

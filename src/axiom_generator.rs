use crate::VarName;
use crate::axiom_builder_state::{AxiomBuilderState, BodyPropositionData};
use crate::create_wrapper::RESULT_PARAM;
use crate::prog_ir::{LetBinding, Type, TypeDecl};
use crate::spec_ir::{Expression, Parameter, Proposition, Quantifier};

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
    pub fn get_function_type(&self, name: &VarName) -> Option<&Type> {
        self.function_types.get(name)
    }

    /// Convert a list of (VarName, Type) pairs into universal parameters
    fn varnames_to_universals(params: &[(VarName, Type)]) -> Vec<Parameter> {
        params
            .iter()
            .map(|(name, typ)| Parameter {
                name: name.clone(),
                typ: typ.clone(),
                quantifier: Quantifier::Universal,
            })
            .collect()
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

        let universal_params = Self::varnames_to_universals(&binding.params);

        self.function_types
            .insert(binding.name.clone(), binding.return_type.clone().unwrap());
        let body_propositions = self.from_expression(&binding.body);

        Ok(AxiomBuilderState::new(
            self.type_constructors.clone(),
            binding.clone(),
            body_propositions,
            universal_params,
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
                let expr = Self::extract_single_expr(self.from_expression(expression))
                    .unwrap_or_else(|e| panic!("UnaryOp operand: {}", e));
                vec![BodyPropositionData {
                    proposition_steps: vec![Proposition::Expr(Expression::UnaryOp(
                        *unary_op,
                        Box::new(expr),
                    ))],
                    additional_parameters: vec![],
                }]
            }
            crate::prog_ir::Expression::BinaryOp(expression, binary_op, expression1) => {
                let left = self.from_expression(&expression);
                let right = self.from_expression(&expression1);
                assert!(
                    left.len() == 1 && right.len() == 1,
                    "unimplemented for other cases"
                );
                let left_data = left.into_iter().next().unwrap();
                let right_data = right.into_iter().next().unwrap();

                let (left_prop, left_rest) = left_data.proposition_steps.split_last().unwrap();
                let (right_prop, right_rest) = right_data.proposition_steps.split_last().unwrap();

                let mut proposition_steps = left_rest.to_vec();
                proposition_steps.extend_from_slice(right_rest);
                proposition_steps.push(Proposition::Expr(Expression::BinaryOp(
                    Box::new(left_prop.as_expr().clone()),
                    *binary_op,
                    Box::new(right_prop.as_expr().clone()),
                )));
                let mut additional_parameters = left_data.additional_parameters;
                additional_parameters.extend(right_data.additional_parameters);

                vec![BodyPropositionData {
                    proposition_steps,
                    additional_parameters,
                }]
            }
            crate::prog_ir::Expression::Application(func_expr, arg_exprs) => {
                let func_body_data = Self::extract_single_expr(self.from_expression(func_expr))
                    .unwrap_or_else(|e| panic!("Application function: {}", e));

                let func_name = match func_body_data {
                    Expression::Variable(v) => v,
                    _ => panic!("Not sure yet"),
                };

                let mut converted_args: Vec<_> = arg_exprs
                    .iter()
                    .map(|expr| {
                        Self::extract_single_expr(self.from_expression(expr))
                            .unwrap_or_else(|e| panic!("Application argument: {}", e))
                    })
                    .collect();

                let exists_var = self.next_var();
                let existential = Expression::Variable(exists_var.clone());

                let func_name_wrapper = format!("{func_name}_wrapper");
                converted_args.push(existential.clone());

                // Look up the function's return type if available
                let func_return_type = self.get_function_type(&func_name).cloned();

                vec![BodyPropositionData {
                    proposition_steps: vec![
                        Proposition::Predicate(func_name_wrapper, converted_args),
                        Proposition::Expr(existential),
                    ],
                    additional_parameters: vec![Parameter {
                        name: exists_var,
                        typ: func_return_type.unwrap_or_else(|| {
                            panic!("Function '{}' type not registered", func_name)
                        }),
                        quantifier: Quantifier::Existential,
                    }],
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
                        let pattern_expr = self.expr_from_pattern(pattern);
                        let pattern_constraint = Proposition::Expr(Expression::BinaryOp(
                            Box::new(pattern_constraint_base.clone()),
                            crate::prog_ir::BinaryOp::Eq,
                            Box::new(pattern_expr),
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
                        let mut all_vars = Self::varnames_to_universals(&pattern_vars);
                        all_vars.extend(branch_body_data.additional_parameters);
                        results.push(BodyPropositionData {
                            proposition_steps: final_steps,
                            additional_parameters: all_vars,
                        });
                    }
                }
                results
            }
            crate::prog_ir::Expression::Tuple(_expressions) => todo!(),
        }
    }
}

#[cfg(test)]
mod tests {
    use itertools::Itertools as _;

    use super::*;
    use crate::ocamlparser::OcamlParser;
    use crate::prog_ir::{AstNode, LetBinding};
    use crate::spec_ir::create_ilist_type;
    use crate::{ToLean, VarName};

    /// Helper: parse program, extract type and function definitions
    fn parse_program(program_str: &str) -> Vec<AstNode> {
        let nodes = OcamlParser::parse_nodes(program_str).expect("Failed to parse program");
        assert_eq!(
            nodes.len(),
            2,
            "Expected exactly two nodes (type + function)"
        );
        nodes
    }

    /// Helper: find a function binding by name
    fn find_function(nodes: &[AstNode], name: &str) -> LetBinding {
        nodes
            .iter()
            .find_map(|node| match node {
                AstNode::LetBinding(binding) if binding.name == VarName::new(name) => {
                    Some(binding.clone())
                }
                _ => None,
            })
            .expect(&format!("Expected to find {} function binding", name))
    }

    /// Helper: generate axioms from a program string and function name
    fn generate_axioms_for(program_str: &str, func_name: &str) -> Vec<Vec<Proposition>> {
        let parsed_nodes = parse_program(program_str);
        let function = find_function(&parsed_nodes, func_name);
        let mut generator = AxiomGenerator::new(vec![create_ilist_type()]);

        let builder = generator
            .prepare_function(&function)
            .expect("Failed to prepare function");
        builder
            .body_propositions
            .iter()
            .map(|axiom| axiom.proposition_steps.clone())
            .collect()
    }

    #[test]
    fn test_and_predicate_with_non_comparison() {
        // Test AND with an expression and a predicate: should create res_0 ∧ expr, not expr + res_0
        // Using a boolean function that returns true and ANDs with a recursive call
        let program_str = "type [@grind] ilist = Nil | Cons of int * ilist\nlet [@simp] [@grind] rec all_positive (l : ilist) : bool = match l with | Nil -> true | Cons (h, t) -> (h > 0) && all_positive t";
        let props = generate_axioms_for(program_str, "all_positive");

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
        let props = generate_axioms_for(program_str, "mem");

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
        let props = generate_axioms_for(program_str, "all_eq");

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
        let props = generate_axioms_for(program_str, "len");

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
        let props = generate_axioms_for(program_str, "sorted");

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
}

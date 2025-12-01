use crate::VarName;
use crate::free_variable_validation::ValidateNoFreeVariables;
use crate::prog_ir::{AstNode, LetBinding, Type};
use crate::spec_ir::{Axiom, Expression, Parameter, Proposition, Quantifier};

/// Takes a parsed program IR function and generates axioms in the spec IR
pub struct AxiomGenerator;

impl AxiomGenerator {
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

    /// Generate axioms from a function definition
    fn from_let_binding(binding: &LetBinding) -> Result<Vec<Axiom>, String> {
        // Extract parameters from the let binding and convert them to universals
        let universals = Self::varnames_to_universals(&binding.params);

        let func_prop_start = Proposition::Predicate(
            binding.name.to_string(),
            binding
                .params
                .iter()
                .map(|(n, _)| crate::spec_ir::Expression::Variable(n.clone()))
                .collect(),
        );

        let possible_bodies = Self::from_expression(&binding.body);

        let axioms: Vec<Axiom> = possible_bodies
            .into_iter()
            .map(|(prop, additional_vars)| {
                let mut params = universals.clone();
                params.extend(Self::varnames_to_universals(&additional_vars));
                Axiom {
                    name: "blah".to_string(),
                    params,
                    body: Proposition::Implication(
                        Box::new(func_prop_start.clone()),
                        Box::new(prop),
                    ),
                    proof: None,
                }
            })
            .collect();

        // Validate that all variables in each axiom body are declared as parameters
        for axiom in &axioms {
            axiom.validate_no_free_variables()?;
        }

        Ok(axioms)
    }

    fn from_expression(
        body: &crate::prog_ir::Expression,
    ) -> Vec<(Proposition, Vec<(VarName, Type)>)> {
        match body {
            crate::prog_ir::Expression::Variable(var_name) => vec![(
                Proposition::Expr(Expression::Variable(var_name.clone())),
                vec![],
            )],
            crate::prog_ir::Expression::Constructor(constructor_name, expressions) => {
                let converted_expressions: Vec<_> = expressions
                    .iter()
                    .map(|expr| {
                        let results = Self::from_expression(expr);
                        assert_eq!(
                            results.len(),
                            1,
                            "Constructor argument should have exactly one result"
                        );
                        let (prop, vars) = results.into_iter().next().unwrap();
                        assert!(
                            vars.is_empty(),
                            "Constructor argument should not introduce variables"
                        );
                        match prop {
                            Proposition::Expr(e) => e,
                            _ => panic!("Constructor argument must be an expression"),
                        }
                    })
                    .collect();
                vec![(
                    Proposition::Expr(Expression::Constructor(
                        constructor_name.clone(),
                        converted_expressions,
                    )),
                    vec![],
                )]
            }
            crate::prog_ir::Expression::Literal(literal) => vec![(
                Proposition::Expr(Expression::Literal(literal.clone())),
                vec![],
            )],
            crate::prog_ir::Expression::UnaryOp(unary_op, expression) => {
                let results = Self::from_expression(expression);
                assert_eq!(
                    results.len(),
                    1,
                    "UnaryOp operand should have exactly one result"
                );
                let (prop, vars) = results.into_iter().next().unwrap();
                assert!(
                    vars.is_empty(),
                    "UnaryOp operand should not introduce variables"
                );
                match prop {
                    Proposition::Expr(e) => vec![(
                        Proposition::Expr(Expression::UnaryOp(*unary_op, Box::new(e))),
                        vec![],
                    )],
                    _ => panic!("UnaryOp operand must be an expression"),
                }
            }
            crate::prog_ir::Expression::BinaryOp(expression, binary_op, expression1) => {
                let left_results = Self::from_expression(expression);
                assert_eq!(
                    left_results.len(),
                    1,
                    "BinaryOp left operand should have exactly one result"
                );
                let (left_prop, left_vars) = left_results.into_iter().next().unwrap();
                assert!(
                    left_vars.is_empty(),
                    "BinaryOp left operand should not introduce variables"
                );

                let right_results = Self::from_expression(expression1);
                assert_eq!(
                    right_results.len(),
                    1,
                    "BinaryOp right operand should have exactly one result"
                );
                let (right_prop, right_vars) = right_results.into_iter().next().unwrap();
                assert!(
                    right_vars.is_empty(),
                    "BinaryOp right operand should not introduce variables"
                );

                match (left_prop, right_prop) {
                    (Proposition::Expr(left_e), Proposition::Expr(right_e)) => vec![(
                        Proposition::Expr(Expression::BinaryOp(
                            Box::new(left_e),
                            *binary_op,
                            Box::new(right_e),
                        )),
                        vec![],
                    )],
                    _ => panic!("BinaryOp operands must be expressions"),
                }
            }
            crate::prog_ir::Expression::Application(func_expr, arg_exprs) => {
                let func_results = Self::from_expression(func_expr);
                assert_eq!(
                    func_results.len(),
                    1,
                    "Application function should have exactly one result"
                );
                let (func_prop, func_vars) = func_results.into_iter().next().unwrap();
                assert!(
                    func_vars.is_empty(),
                    "Application function should not introduce variables"
                );

                let converted_args: Vec<_> = arg_exprs
                    .iter()
                    .map(|expr| {
                        let results = Self::from_expression(expr);
                        assert_eq!(
                            results.len(),
                            1,
                            "Application argument should have exactly one result"
                        );
                        let (prop, vars) = results.into_iter().next().unwrap();
                        assert!(
                            vars.is_empty(),
                            "Application argument should not introduce variables"
                        );
                        match prop {
                            Proposition::Expr(e) => e,
                            _ => panic!("Application argument must be an expression"),
                        }
                    })
                    .collect();

                match func_prop {
                    Proposition::Expr(Expression::Variable(func_name)) => {
                        vec![(
                            Proposition::Predicate(func_name.to_string(), converted_args),
                            vec![],
                        )]
                    }
                    _ => panic!("Application function must be a variable"),
                }
            }
            crate::prog_ir::Expression::Match(expression, items) => todo!(),
            crate::prog_ir::Expression::Tuple(expressions) => todo!(),
        }
    }

    /// Generate axioms from an AST node
    pub fn from_ast_node(node: &AstNode) -> Result<Vec<Axiom>, String> {
        match node {
            AstNode::TypeDeclaration(_) => {
                Err("Cannot generate axioms from type declarations".to_string())
            }
            AstNode::LetBinding(binding) => Self::from_let_binding(binding),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ocamlparser::OcamlParser;
    use crate::{ToLean as _, VarName};

    #[test]
    fn test_generate_axioms_from_length_function() {
        let len_function_str = "let [@simp] [@grind] rec len (l : ilist) (n : int) : bool = match l with | Nil -> n = 0 | Cons (_, xs) -> len xs (n - 1)";
        let nodes =
            OcamlParser::parse_nodes(len_function_str).expect("Failed to parse len function");
        assert_eq!(nodes.len(), 1, "Expected exactly one node");

        let len_function = match nodes.into_iter().next().unwrap() {
            AstNode::LetBinding(binding) => {
                assert_eq!(binding.name, VarName::new("len"));
                binding
            }
            node => panic!("Expected LetBinding, got {:?}", node),
        };

        let axioms =
            AxiomGenerator::from_let_binding(&len_function).expect("Failed to generate axioms");

        // Should generate exactly the expected axioms for len: len_nil and len_cons
        assert_eq!(axioms.len(), 2, "Expected 2 axioms");

        // len_nil: ∀ l : List, ∀ n : Int, ((l = .Nil ∧ len l n) → n = 0)
        let len_nil = &axioms[0];
        assert_eq!(len_nil.name, "len_nil");
        assert_eq!(
            len_nil.to_lean(),
            "theorem len_nil : ∀ l : List, ∀ n : Int, ((l = .Nil ∧ len l n) → n = 0) := sorry"
        );

        // len_cons: ∀ x : Int, ∀ xs : List, ∀ l : List, ∀ n : Int, ((l = .Cons x xs ∧ len xs n) → len l (n + 1))
        let len_cons = &axioms[1];
        assert_eq!(len_cons.name, "len_cons");
        assert_eq!(
            len_cons.to_lean(),
            "theorem len_cons : ∀ x : Int, ∀ xs : List, ∀ l : List, ∀ n : Int, ((l = .Cons x xs ∧ len xs n) → len l (n + 1)) := sorry"
        );
    }
}

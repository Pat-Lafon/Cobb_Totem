use crate::free_variable_validation::ValidateNoFreeVariables;
use crate::prog_ir::{AstNode, LetBinding};
use crate::spec_ir::Axiom;

/// Takes a parsed program IR function and generates axioms in the spec IR
pub struct AxiomGenerator;

impl AxiomGenerator {
    /// Generate axioms from a function definition
    pub fn from_let_binding(_binding: &LetBinding) -> Result<Vec<Axiom>, String> {
        // TODO: Generate axioms from the let binding
        let axioms: Vec<Axiom> = unimplemented!("Axiom generation from let binding");

        // Validate that all variables in each axiom body are declared as parameters
        for axiom in &axioms {
            axiom.validate_no_free_variables()?;
        }

        Ok(axioms)
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
    use crate::VarName;
    use crate::ocamlparser::OcamlParser;
    use crate::spec_ir::predicates;

    #[test]
    fn test_generate_axioms_from_length_function() {
        let len_function_str = "let [@simp] [@grind] rec len (l : ilist) (n : int) : bool = match l with | Nil -> n = 0 | Cons (_, xs) -> len xs (n - 1)";
        let nodes = OcamlParser::parse_nodes(len_function_str)
            .expect("Failed to parse len function");
        assert_eq!(nodes.len(), 1, "Expected exactly one node");

        let len_function = match nodes.into_iter().next().unwrap() {
            AstNode::LetBinding(binding) => {
                assert_eq!(binding.name, VarName::new("len"));
                binding
            }
            node => panic!("Expected LetBinding, got {:?}", node),
        };

        let _axioms =
            AxiomGenerator::from_let_binding(&len_function).expect("Failed to generate axioms");

        // Should generate exactly the expected axioms for len: len_nil and len_cons
        unimplemented!("Assert len_nil and len_cons axioms are generated correctly");
    }
}

use crate::prog_ir::{LetBinding, AstNode};
use crate::spec_ir::Axiom;
use crate::VarName;

/// Takes a parsed program IR function and generates axioms in the spec IR
pub struct AxiomGenerator;

impl AxiomGenerator {
    /// Generate axioms from a function definition
    pub fn from_let_binding(_binding: &LetBinding) -> Result<Vec<Axiom>, String> {
        unimplemented!()
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
    use crate::spec_ir::predicates;

    #[test]
    fn test_generate_axioms_from_length_function() {
        let prelude_nodes = predicates::parse_all().expect("Failed to parse prelude");

        let len_function = prelude_nodes
            .iter()
            .find_map(|node| {
                if let AstNode::LetBinding(binding) = node {
                    if binding.name == VarName::new("len") {
                        return Some(binding.clone());
                    }
                }
                None
            })
            .expect("Failed to find len function");

        let _axioms = AxiomGenerator::from_let_binding(&len_function)
            .expect("Failed to generate axioms");

        // Should generate exactly the expected axioms for len: len_nil and len_cons
        unimplemented!("Assert len_nil and len_cons axioms are generated correctly");
    }
}

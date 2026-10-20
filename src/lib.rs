//! The pipeline runs `ocamlparser` (tree-sitter) → `prog_ir` → `axiom_generator` (`prepare_function`,
//! one `PreparedBinding` per function) → `axiom_builder_state` (`generate_all`, where the axiom shapes
//! are decided) → `spec_ir`, whose `Display` impls render the `let[@axiom]` output.

pub mod axiom_builder_state;
pub mod axiom_generator;
pub(crate) mod axiom_validation;
pub(crate) mod domain_axiom_builder;
pub(crate) mod integration_tests;
pub mod ocamlparser;
pub mod prog_ir;
pub(crate) mod proposition_transforms;
pub mod spec_ir;

use ocamlparser::OcamlParser;
use prog_ir::AstNode;
use std::fmt;

/// Literal values used in expressions
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Literal {
    Int(i32),
    Bool(bool),
}

/// A variable name with type safety
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct VarName(String);

impl VarName {
    /// Create a new variable name
    pub fn new(name: impl Into<String>) -> Self {
        VarName(name.into())
    }

    /// Get the name as a string slice
    pub fn as_str(&self) -> &str {
        &self.0
    }

    /// Consume and get the inner String
    pub fn into_string(self) -> String {
        self.0
    }
}

impl std::ops::Deref for VarName {
    type Target = str;

    fn deref(&self) -> &str {
        &self.0
    }
}

impl fmt::Display for VarName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl From<&str> for VarName {
    fn from(s: &str) -> Self {
        VarName(s.to_string())
    }
}

impl AsRef<str> for VarName {
    fn as_ref(&self) -> &str {
        &self.0
    }
}

impl fmt::Display for Literal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Literal::Int(n) => write!(f, "{}", n),
            Literal::Bool(b) => write!(f, "{}", b),
        }
    }
}

/// Generate the axioms for a complete OCaml program
pub fn generate_axioms(
    program_str: &str,
) -> Result<Vec<spec_ir::Axiom>, Box<dyn std::error::Error>> {
    let parsed_nodes = OcamlParser::parse_nodes(program_str)?;

    let type_decls = parsed_nodes
        .iter()
        .filter_map(|node| match node {
            AstNode::TypeDeclaration(type_decl) => Some(type_decl.clone()),
            _ => None,
        })
        .collect::<Vec<_>>();

    let type_decl = type_decls
        .into_iter()
        .next()
        .ok_or("Expected to find at least one type declaration")?;

    let functions: Vec<_> = parsed_nodes
        .iter()
        .filter_map(|node| match node {
            AstNode::LetBinding(binding) => Some(binding.clone()),
            _ => None,
        })
        .collect();

    let mut generator = axiom_generator::AxiomGenerator::new(vec![type_decl]);
    for func in &functions {
        generator.prepare_function(func)?;
    }

    Ok(generator.build_all().generate_all())
}

/// Test utilities for parsing and generating axioms (crate internal for testing)
#[cfg(test)]
pub(crate) mod test_helpers {
    use crate::axiom_generator::AxiomGenerator;
    use crate::ocamlparser::OcamlParser;
    use crate::prog_ir::{AstNode, TypeDecl};
    use crate::spec_ir::{Axiom, Proposition};

    /// Parse program string and extract type and function definitions
    pub fn parse_program(program_str: &str) -> Vec<AstNode> {
        let nodes = OcamlParser::parse_nodes(program_str).expect("Failed to parse program");
        nodes
    }

    /// Extract type declarations from parsed nodes
    pub fn extract_type_decls(nodes: &[AstNode]) -> Vec<TypeDecl> {
        nodes
            .iter()
            .filter_map(|node| match node {
                AstNode::TypeDeclaration(type_decl) => Some(type_decl.clone()),
                _ => None,
            })
            .collect()
    }

    /// Generate axiom proposition steps from a program string
    pub(crate) fn generate_axioms_for(program_str: &str) -> Vec<Vec<Proposition>> {
        let parsed_nodes = parse_program(program_str);
        let type_decls = extract_type_decls(&parsed_nodes);

        let mut generator = AxiomGenerator::new(type_decls);

        // Prepare all functions in the program so that calls between them are resolved
        for node in &parsed_nodes {
            if let AstNode::LetBinding(binding) = node {
                generator
                    .prepare_function(binding)
                    .expect("Failed to prepare function");
            }
        }

        generator
            .get_prepared()
            .iter()
            .flat_map(|prepared| {
                prepared
                    .body_propositions
                    .iter()
                    .map(|axiom| {
                        let mut all_body_steps = axiom.body_steps.clone();
                        all_body_steps.extend(axiom.guard.clone());
                        all_body_steps.push(Proposition::Expr(axiom.result_expr.clone()));

                        let mut steps = axiom.input_constraints.clone();
                        if !all_body_steps.is_empty() {
                            steps.push(Proposition::optional_conjunction(all_body_steps));
                        }

                        steps
                    })
                    .collect::<Vec<_>>()
            })
            .collect()
    }

    /// Generate every axiom for every function in a program string
    pub(crate) fn generate_program_axioms(program_str: &str) -> Vec<Axiom> {
        let parsed_nodes = parse_program(program_str);
        let mut generator = AxiomGenerator::new(extract_type_decls(&parsed_nodes));

        // Prepare all functions in the program so that calls between them are resolved
        for node in &parsed_nodes {
            if let AstNode::LetBinding(binding) = node {
                generator
                    .prepare_function(binding)
                    .expect("Failed to prepare function");
            }
        }

        generator.build_all().generate_all()
    }
}

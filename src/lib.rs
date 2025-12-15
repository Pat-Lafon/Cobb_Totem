pub mod axiom_builder_state;
pub mod axiom_generator;
pub mod axiom_validation;
pub mod create_wrapper;
pub mod lean_backend;
pub mod lean_validation;
pub mod ocamlparser;
pub mod prog_ir;
pub mod spec_ir;

use std::fmt;

/// Literal values used in expressions
#[derive(Debug, Clone, PartialEq, Eq)]
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

/// Trait for converting AST nodes to Lean syntax
pub trait ToLean {
    fn to_lean(&self) -> String;
}

impl fmt::Display for Literal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Literal::Int(n) => write!(f, "{}", n),
            Literal::Bool(b) => write!(f, "{}", b),
        }
    }
}

impl ToLean for Literal {
    fn to_lean(&self) -> String {
        match self {
            Literal::Int(n) => n.to_string(),
            Literal::Bool(b) => b.to_string(),
        }
    }
}

/// Test utilities for parsing and generating axioms
#[cfg(test)]
mod test_helpers {
    use crate::axiom_generator::AxiomGenerator;
    use crate::ocamlparser::OcamlParser;
    use crate::prog_ir::{AstNode, LetBinding, TypeDecl};
    use crate::spec_ir::{Axiom, Proposition};
    use crate::VarName;

    /// Parse program string and extract type and function definitions
    pub fn parse_program(program_str: &str) -> Vec<AstNode> {
        let nodes = OcamlParser::parse_nodes(program_str).expect("Failed to parse program");
        assert_eq!(
            nodes.len(),
            2,
            "Expected exactly two nodes (type + function)"
        );
        nodes
    }

    /// Find a function binding by name in a list of AST nodes
    pub fn find_function(nodes: &[AstNode], name: &str) -> LetBinding {
        nodes
            .iter()
            .find_map(|node| match node {
                AstNode::LetBinding(binding) if binding.name == VarName::new(name) => {
                    Some(binding.clone())
                }
                _ => None,
            })
            .unwrap_or_else(|| panic!("Expected to find {} function binding", name))
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

    /// Generate axiom proposition steps from a program string and function name
    pub fn generate_axioms_for(program_str: &str, func_name: &str) -> Vec<Vec<Proposition>> {
        let parsed_nodes = parse_program(program_str);
        let function = find_function(&parsed_nodes, func_name);
        let type_decls = extract_type_decls(&parsed_nodes);

        let mut generator = AxiomGenerator::new(type_decls);
        generator
            .prepare_function(&function)
            .expect("Failed to prepare function");

        generator
            .get_prepared()
            .iter()
            .find(|(binding, _)| binding.name == function.name)
            .map(|(_, props)| {
                props
                    .iter()
                    .map(|axiom| axiom.proposition_steps.clone())
                    .collect()
            })
            .unwrap_or_default()
    }

    /// Generate complete axioms with wrapper from a program string and function name
    pub fn generate_axioms_with_wrapper(
        program_str: &str,
        func_name: &str,
    ) -> (Vec<AstNode>, Vec<crate::spec_ir::Axiom>, LetBinding) {
        use crate::create_wrapper;

        let parsed_nodes = parse_program(program_str);
        let function = find_function(&parsed_nodes, func_name);
        let type_constructors = extract_type_decls(&parsed_nodes);

        let mut generator = AxiomGenerator::new(type_constructors.clone());
        generator
            .prepare_function(&function)
            .expect("Failed to prepare function");

        // Create wrapper
        let wrapper = create_wrapper::create_wrapper(&function);

        // Build axioms with proof tactic
        let builder = generator.build_all();
        let axioms = builder
            .with_proof(|a| a.suggest_proof_tactic())
            .build()
            .expect("Failed to generate axioms");

        (parsed_nodes, axioms, wrapper)
    }

    /// Validate generated axioms through Lean backend
    pub fn validate_axioms(parsed_nodes: Vec<AstNode>, axioms: Vec<Axiom>) {
        use crate::lean_backend::LeanContextBuilder;
        use crate::lean_validation::validate_lean_code;

        let mut builder = LeanContextBuilder::new();
        for type_decl in extract_type_decls(&parsed_nodes) {
            let theorems = type_decl.generate_complete_lawful_beq();
            builder = builder.with_type_theorems(&type_decl.name, theorems);
        }

        let lean_code = builder.with_nodes(parsed_nodes).with_axioms(axioms).build();

        validate_lean_code(&lean_code).unwrap_or_else(|e| {
            eprintln!("Generated Lean code:\n{}", lean_code);
            panic!("Generated axioms failed Lean validation:\n{}", e)
        });
    }
}

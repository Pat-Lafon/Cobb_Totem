pub mod axiom_generator;
pub mod free_variable_validation;
pub mod lean_backend;
pub mod lean_validation;
pub mod ocamlparser;
pub mod prog_ir;
pub mod spec_ir;

/// Trait for converting AST nodes to Lean syntax
pub trait ToLean {
    fn to_lean(&self) -> String;
}

pub mod axiom_generator;
pub mod free_variable_validation;
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

impl From<String> for VarName {
    fn from(s: String) -> Self {
        VarName(s)
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
            Literal::Bool(b) => if *b { "true" } else { "false" }.to_string(),
        }
    }
}

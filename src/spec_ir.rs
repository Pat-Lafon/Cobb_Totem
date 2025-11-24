use std::fmt;

use crate::{ToLean, prog_ir::{BinaryOp, Type, UnaryOp}};
#[cfg(test)]
use crate::lean_validation::validate_lean_code;

/// A specification axiom that can be translated to Lean theorems
#[derive(Debug, Clone)]
pub struct Axiom {
    pub name: String,
    pub params: Vec<Parameter>,
    pub body: Proposition,
}

/// Quantification mode for a parameter
#[derive(Debug, Clone, PartialEq)]
pub enum Quantifier {
    Universal,
    Existential,
}

impl ToLean for Quantifier {
    fn to_lean(&self) -> String {
        match self {
            Quantifier::Universal => "∀".to_string(),
            Quantifier::Existential => "∃".to_string(),
        }
    }
}

/// A parameter in an axiom with its quantification mode
#[derive(Debug, Clone)]
pub struct Parameter {
    pub name: String,
    pub typ: Type,
    pub quantifier: Quantifier,
}

/// A logical proposition that can appear in axiom bodies
#[derive(Debug, Clone)]
pub enum Proposition {
    /// A bare expression
    Expr(Expression),

    /// A predicate application: emp l, hd l x, tl l l1, len l n
    Predicate(String, Vec<Expression>),

    /// Implication: p #==> q
    Implication(Box<Proposition>, Box<Proposition>),

    /// Equality: p #== q
    Equality(Box<Proposition>, Box<Proposition>),

    /// Conjunction: p && q
    And(Box<Proposition>, Box<Proposition>),

    /// Disjunction: p || q
    Or(Box<Proposition>, Box<Proposition>),

    /// Negation: not p
    Not(Box<Proposition>),

    /// Bi-implication: iff p q
    Iff(Box<Proposition>, Box<Proposition>),
}

/// Expressions that appear as arguments to predicates
#[derive(Debug, Clone, PartialEq)]
pub enum Expression {
    /// Variable reference
    Variable(String),

    /// Integer literal
    Literal(i32),

    /// Binary arithmetic/comparison operators: >=, >, ==, <, <=, +, -, etc.
    BinaryOp(Box<Expression>, BinaryOp, Box<Expression>),

    /// Unary operators: negation, etc.
    UnaryOp(UnaryOp, Box<Expression>),
}

impl Parameter {
    pub fn universal(name: String, typ: Type) -> Self {
        Parameter {
            name,
            typ,
            quantifier: Quantifier::Universal,
        }
    }

    pub fn existential(name: String, typ: Type) -> Self {
        Parameter {
            name,
            typ,
            quantifier: Quantifier::Existential,
        }
    }
}

impl fmt::Display for Parameter {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.quantifier == Quantifier::Existential {
            write!(f, "(({} [@exists]) : {})", self.name, self.typ)
        } else {
            write!(f, "({} : {})", self.name, self.typ)
        }
    }
}

impl ToLean for Parameter {
    fn to_lean(&self) -> String {
        format!("{} {} : {}", self.quantifier.to_lean(), self.name, self.typ.to_lean())
    }
}

impl ToLean for Axiom {
    fn to_lean(&self) -> String {
        let mut body_str = self.body.to_lean();

        // Wrap body with all parameters (existential then universal)
        for param in self.params.iter().rev() {
            body_str = format!("{}, {}", param.to_lean(), body_str);
        }

        // TODO: add an actual proof using grind here?
        format!("theorem {} : {} := sorry", self.name, body_str)
    }
}



impl ToLean for Proposition {
    fn to_lean(&self) -> String {
        match self {
            Proposition::Expr(expr) => expr.to_lean(),
            Proposition::Predicate(name, args) => {
                let args_str = args
                    .iter()
                    .map(|e| e.to_lean())
                    .collect::<Vec<_>>()
                    .join(" ");
                if args.is_empty() {
                    name.clone()
                } else {
                    format!("({} {})", name, args_str)
                }
            }
            Proposition::Implication(p, q) => {
                format!("({}) → ({})", p.to_lean(), q.to_lean())
            }
            Proposition::Equality(p, q) => {
                format!("{} = {}", p.to_lean(), q.to_lean())
            }
            Proposition::And(p, q) => {
                format!("({} ∧ {})", p.to_lean(), q.to_lean())
            }
            Proposition::Or(p, q) => {
                format!("({} ∨ {})", p.to_lean(), q.to_lean())
            }
            Proposition::Not(p) => {
                format!("¬({})", p.to_lean())
            }
            Proposition::Iff(p, q) => {
                format!("({} ↔ {})", p.to_lean(), q.to_lean())
            }
        }
    }
}

impl ToLean for Expression {
    fn to_lean(&self) -> String {
        match self {
            Expression::Variable(name) => name.clone(),
            Expression::Literal(n) => n.to_string(),
            Expression::BinaryOp(left, op, right) => {
                format!("({} {} {})", left.to_lean(), op.to_lean(), right.to_lean())
            }
            Expression::UnaryOp(op, expr) => {
                format!("{}({})", op.to_lean(), expr.to_lean())
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;


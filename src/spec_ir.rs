use std::fmt;

use itertools::Itertools as _;

use crate::{
    ToLean,
    ocamlparser::OcamlParser,
    prog_ir::{self, BinaryOp, Type, UnaryOp},
};

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
        format!(
            "{} {} : {}",
            self.quantifier.to_lean(),
            self.name,
            self.typ.to_lean()
        )
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

/// Build Lean code context: axioms with type definitions and predicate definitions
pub fn build_lean_context(nodes: Vec<crate::prog_ir::AstNode>, axioms: Vec<Axiom>) -> String {
    nodes
        .iter()
        .map(|node| node.to_lean())
        .chain(axioms.iter().map(|axiom| axiom.to_lean()))
        .join("\n\n")
}

/// Helper functions to parse predicate definitions for the ilist datatype
pub mod predicates {
    use super::*;

    pub const PRELUDE: &str = "type ilist = Nil | Cons of int * ilist
let [@simp] [@grind] emp (l : ilist) : bool = match l with | Nil -> true | Cons (_, _) -> false
let [@simp] [@grind] hd (l : ilist) (x : int) : bool = match l with | Nil -> false | Cons (h, _) -> h = x
let [@simp] [@grind] tl (l : ilist) (xs : ilist) : bool = match l with | Nil -> false | Cons (_, t) -> t = xs
let [@simp] [@grind] rec len (l : ilist) (n : int) : bool = match l with | Nil -> n = 0 | Cons (_, xs) -> len xs (n - 1)
let [@simp] [@grind] rec sorted (l : ilist) : bool = match l with | Nil -> true | Cons (h, t) -> match t with | Nil -> true | Cons (h2, t2) -> (h <= h2) && sorted (Cons (h2, t2))";

    /// Parse all predicates and type definitions
    pub fn parse_all() -> Result<Vec<prog_ir::AstNode>, Box<dyn std::error::Error>> {
        OcamlParser::parse_nodes(PRELUDE)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::lean_validation::validate_lean_code;

    #[test]
    fn test_axiom_with_prelude() {
        // Load the prelude predicates
        let prelude_nodes = predicates::parse_all().expect("Failed to parse prelude");

        // Create an axiom: ∀ (l : ilist), (∀ (x : Int), ((emp l) → ¬(hd l x)))
        let axiom = Axiom {
            name: "list_emp_no_hd".to_string(),
            params: vec![
                Parameter::universal("l".to_string(), Type::Named("ilist".to_string())),
                Parameter::universal("x".to_string(), Type::Named("Int".to_string())),
            ],
            body: Proposition::Implication(
                Box::new(Proposition::Predicate(
                    "emp".to_string(),
                    vec![Expression::Variable("l".to_string())],
                )),
                Box::new(Proposition::Not(Box::new(Proposition::Predicate(
                    "hd".to_string(),
                    vec![
                        Expression::Variable("l".to_string()),
                        Expression::Variable("x".to_string()),
                    ],
                )))),
            ),
        };

        // Build the Lean context with prelude definitions and axiom
        let lean_code = build_lean_context(prelude_nodes, vec![axiom]);

        // Verify the code structure before validation
        assert!(!lean_code.is_empty());
        assert!(lean_code.contains("list_emp_no_hd"));
        assert!(lean_code.contains("theorem"));

        // Validate the generated Lean code using the Lean backend
        // This demonstrates the end-to-end flow from spec IR to Lean backend validation
        let result = validate_lean_code(&lean_code);
        // We expect this to succeed with properly typed axioms
        assert!(
            result.is_ok(),
            "Expected validation to succeed, but got: {:?}\nLean code:\n{}",
            result,
            lean_code
        );
    }

    #[test]
    fn test_axiom_list_emp_no_tl() {
        // Load the prelude predicates
        let prelude_nodes = predicates::parse_all().expect("Failed to parse prelude");

        // Create an axiom: ∀ (l : ilist), (∀ (l1 : ilist), ((emp l) → ¬(tl l l1)))
        let axiom = Axiom {
            name: "list_emp_no_tl".to_string(),
            params: vec![
                Parameter::universal("l".to_string(), Type::Named("ilist".to_string())),
                Parameter::universal("l1".to_string(), Type::Named("ilist".to_string())),
            ],
            body: Proposition::Implication(
                Box::new(Proposition::Predicate(
                    "emp".to_string(),
                    vec![Expression::Variable("l".to_string())],
                )),
                Box::new(Proposition::Not(Box::new(Proposition::Predicate(
                    "tl".to_string(),
                    vec![
                        Expression::Variable("l".to_string()),
                        Expression::Variable("l1".to_string()),
                    ],
                )))),
            ),
        };

        // Build the Lean context with prelude definitions and axiom
        let lean_code = build_lean_context(prelude_nodes, vec![axiom]);

        // Verify the code structure before validation
        assert!(!lean_code.is_empty());
        assert!(lean_code.contains("list_emp_no_tl"));
        assert!(lean_code.contains("theorem"));

        // Validate the generated Lean code using the Lean backend
        let result = validate_lean_code(&lean_code);
        // We expect this to succeed with properly typed axioms
        assert!(
            result.is_ok(),
            "Expected validation to succeed, but got: {:?}\nLean code:\n{}",
            result,
            lean_code
        );
    }

    #[test]
    fn test_axiom_list_hd_no_emp() {
        // Load the prelude predicates
        let prelude_nodes = predicates::parse_all().expect("Failed to parse prelude");

        // Create an axiom: ∀ (l : ilist), (∀ (x : Int), ((hd l x) → ¬(emp l)))
        let axiom = Axiom {
            name: "list_hd_no_emp".to_string(),
            params: vec![
                Parameter::universal("l".to_string(), Type::Named("ilist".to_string())),
                Parameter::universal("x".to_string(), Type::Named("Int".to_string())),
            ],
            body: Proposition::Implication(
                Box::new(Proposition::Predicate(
                    "hd".to_string(),
                    vec![
                        Expression::Variable("l".to_string()),
                        Expression::Variable("x".to_string()),
                    ],
                )),
                Box::new(Proposition::Not(Box::new(Proposition::Predicate(
                    "emp".to_string(),
                    vec![Expression::Variable("l".to_string())],
                )))),
            ),
        };

        // Build the Lean context with prelude definitions and axiom
        let lean_code = build_lean_context(prelude_nodes, vec![axiom]);

        // Verify the code structure before validation
        assert!(!lean_code.is_empty());
        assert!(lean_code.contains("list_hd_no_emp"));
        assert!(lean_code.contains("theorem"));

        // Validate the generated Lean code using the Lean backend
        let result = validate_lean_code(&lean_code);
        assert!(
            result.is_ok(),
            "Expected validation to succeed, but got: {:?}\nLean code:\n{}",
            result,
            lean_code
        );
    }

    #[test]
    fn test_axiom_list_tl_no_emp() {
        // Load the prelude predicates
        let prelude_nodes = predicates::parse_all().expect("Failed to parse prelude");

        // Create an axiom: ∀ (l : ilist), (∀ (l1 : ilist), ((tl l l1) → ¬(emp l)))
        let axiom = Axiom {
            name: "list_tl_no_emp".to_string(),
            params: vec![
                Parameter::universal("l".to_string(), Type::Named("ilist".to_string())),
                Parameter::universal("l1".to_string(), Type::Named("ilist".to_string())),
            ],
            body: Proposition::Implication(
                Box::new(Proposition::Predicate(
                    "tl".to_string(),
                    vec![
                        Expression::Variable("l".to_string()),
                        Expression::Variable("l1".to_string()),
                    ],
                )),
                Box::new(Proposition::Not(Box::new(Proposition::Predicate(
                    "emp".to_string(),
                    vec![Expression::Variable("l".to_string())],
                )))),
            ),
        };

        // Build the Lean context with prelude definitions and axiom
        let lean_code = build_lean_context(prelude_nodes, vec![axiom]);

        // Verify the code structure before validation
        assert!(!lean_code.is_empty());
        assert!(lean_code.contains("list_tl_no_emp"));
        assert!(lean_code.contains("theorem"));

        // Validate the generated Lean code using the Lean backend
        let result = validate_lean_code(&lean_code);
        assert!(
            result.is_ok(),
            "Expected validation to succeed, but got: {:?}\nLean code:\n{}",
            result,
            lean_code
        );
    }

    #[test]
    fn test_axiom_list_len_0_emp() {
        // Load the prelude predicates
        let prelude_nodes = predicates::parse_all().expect("Failed to parse prelude");

        // Create an axiom: ∀ (l : ilist), ((emp l) → (len l 0))
        let axiom = Axiom {
            name: "list_len_0_emp".to_string(),
            params: vec![Parameter::universal(
                "l".to_string(),
                Type::Named("ilist".to_string()),
            )],
            body: Proposition::Implication(
                Box::new(Proposition::Predicate(
                    "emp".to_string(),
                    vec![Expression::Variable("l".to_string())],
                )),
                Box::new(Proposition::Predicate(
                    "len".to_string(),
                    vec![
                        Expression::Variable("l".to_string()),
                        Expression::Literal(0),
                    ],
                )),
            ),
        };

        // Build the Lean context with prelude definitions and axiom
        let lean_code = build_lean_context(prelude_nodes, vec![axiom]);

        // Verify the code structure before validation
        assert!(!lean_code.is_empty());
        assert!(lean_code.contains("list_len_0_emp"));
        assert!(lean_code.contains("theorem"));

        // Validate the generated Lean code using the Lean backend
        let result = validate_lean_code(&lean_code);
        assert!(
            result.is_ok(),
            "Expected validation to succeed, but got: {:?}\nLean code:\n{}",
            result,
            lean_code
        );
    }

    #[test]
    fn test_axiom_list_positive_len_is_not_emp() {
        // Load the prelude predicates
        let prelude_nodes = predicates::parse_all().expect("Failed to parse prelude");

        // Create an axiom: ∀ (l : ilist), (∀ (n : Int), (((len l n) ∧ (n > 0)) → ¬(emp l)))
        let axiom = Axiom {
            name: "list_positive_len_is_not_emp".to_string(),
            params: vec![
                Parameter::universal("l".to_string(), Type::Named("ilist".to_string())),
                Parameter::universal("n".to_string(), Type::Named("Int".to_string())),
            ],
            body: Proposition::Implication(
                Box::new(Proposition::And(
                    Box::new(Proposition::Predicate(
                        "len".to_string(),
                        vec![
                            Expression::Variable("l".to_string()),
                            Expression::Variable("n".to_string()),
                        ],
                    )),
                    Box::new(Proposition::Expr(Expression::BinaryOp(
                        Box::new(Expression::Variable("n".to_string())),
                        BinaryOp::Gt,
                        Box::new(Expression::Literal(0)),
                    ))),
                )),
                Box::new(Proposition::Not(Box::new(Proposition::Predicate(
                    "emp".to_string(),
                    vec![Expression::Variable("l".to_string())],
                )))),
            ),
        };

        // Build the Lean context with prelude definitions and axiom
        let lean_code = build_lean_context(prelude_nodes, vec![axiom]);

        // Verify the code structure before validation
        assert!(!lean_code.is_empty());
        assert!(lean_code.contains("list_positive_len_is_not_emp"));
        assert!(lean_code.contains("theorem"));

        // Validate the generated Lean code using the Lean backend
        let result = validate_lean_code(&lean_code);
        assert!(
            result.is_ok(),
            "Expected validation to succeed, but got: {:?}\nLean code:\n{}",
            result,
            lean_code
        );
    }

    #[test]
    fn test_axiom_list_tl_len_plus_1() {
        // Load the prelude predicates
        let prelude_nodes = predicates::parse_all().expect("Failed to parse prelude");

        // Create an axiom: ∀ (l : ilist), (∀ (l1 : ilist), (∀ (n : Int), (((tl l l1) ∧ (len l1 n)) → (len l (n + 1)))))
        let axiom = Axiom {
            name: "list_tl_len_plus_1".to_string(),
            params: vec![
                Parameter::universal("l".to_string(), Type::Named("ilist".to_string())),
                Parameter::universal("l1".to_string(), Type::Named("ilist".to_string())),
                Parameter::universal("n".to_string(), Type::Named("Int".to_string())),
            ],
            body: Proposition::Implication(
                Box::new(Proposition::And(
                    Box::new(Proposition::Predicate(
                        "tl".to_string(),
                        vec![
                            Expression::Variable("l".to_string()),
                            Expression::Variable("l1".to_string()),
                        ],
                    )),
                    Box::new(Proposition::Predicate(
                        "len".to_string(),
                        vec![
                            Expression::Variable("l1".to_string()),
                            Expression::Variable("n".to_string()),
                        ],
                    )),
                )),
                Box::new(Proposition::Predicate(
                    "len".to_string(),
                    vec![
                        Expression::Variable("l".to_string()),
                        Expression::BinaryOp(
                            Box::new(Expression::Variable("n".to_string())),
                            BinaryOp::Add,
                            Box::new(Expression::Literal(1)),
                        ),
                    ],
                )),
            ),
        };

        // Build the Lean context with prelude definitions and axiom
        let lean_code = build_lean_context(prelude_nodes, vec![axiom]);

        // Verify the code structure before validation
        assert!(!lean_code.is_empty());
        assert!(lean_code.contains("list_tl_len_plus_1"));
        assert!(lean_code.contains("theorem"));

        // Validate the generated Lean code using the Lean backend
        let result = validate_lean_code(&lean_code);
        assert!(
            result.is_ok(),
            "Expected validation to succeed, but got: {:?}\nLean code:\n{}",
            result,
            lean_code
        );
    }

    #[test]
    fn test_axiom_list_tl_plus_1_len() {
        // Load the prelude predicates
        let prelude_nodes = predicates::parse_all().expect("Failed to parse prelude");

        // Create an axiom: ∀ (l : ilist), (∀ (l1 : ilist), (∀ (n : Int), (((tl l l1) ∧ (len l (n + 1))) → (len l1 n))))
        let axiom = Axiom {
            name: "list_tl_plus_1_len".to_string(),
            params: vec![
                Parameter::universal("l".to_string(), Type::Named("ilist".to_string())),
                Parameter::universal("l1".to_string(), Type::Named("ilist".to_string())),
                Parameter::universal("n".to_string(), Type::Named("Int".to_string())),
            ],
            body: Proposition::Implication(
                Box::new(Proposition::And(
                    Box::new(Proposition::Predicate(
                        "tl".to_string(),
                        vec![
                            Expression::Variable("l".to_string()),
                            Expression::Variable("l1".to_string()),
                        ],
                    )),
                    Box::new(Proposition::Predicate(
                        "len".to_string(),
                        vec![
                            Expression::Variable("l".to_string()),
                            Expression::BinaryOp(
                                Box::new(Expression::Variable("n".to_string())),
                                BinaryOp::Add,
                                Box::new(Expression::Literal(1)),
                            ),
                        ],
                    )),
                )),
                Box::new(Proposition::Predicate(
                    "len".to_string(),
                    vec![
                        Expression::Variable("l1".to_string()),
                        Expression::Variable("n".to_string()),
                    ],
                )),
            ),
        };

        // Build the Lean context with prelude definitions and axiom
        let lean_code = build_lean_context(prelude_nodes, vec![axiom]);

        // Verify the code structure before validation
        assert!(!lean_code.is_empty());
        assert!(lean_code.contains("list_tl_plus_1_len"));
        assert!(lean_code.contains("theorem"));

        // Validate the generated Lean code using the Lean backend
        let result = validate_lean_code(&lean_code);
        assert!(
            result.is_ok(),
            "Expected validation to succeed, but got: {:?}\nLean code:\n{}",
            result,
            lean_code
        );
    }

    #[test]
    fn test_axiom_list_emp_sorted() {
        // Load the prelude predicates
        let prelude_nodes = predicates::parse_all().expect("Failed to parse prelude");

        // Create an axiom: ∀ (l : ilist), ((emp l) → (sorted l))
        let axiom = Axiom {
            name: "list_emp_sorted".to_string(),
            params: vec![Parameter::universal(
                "l".to_string(),
                Type::Named("ilist".to_string()),
            )],
            body: Proposition::Implication(
                Box::new(Proposition::Predicate(
                    "emp".to_string(),
                    vec![Expression::Variable("l".to_string())],
                )),
                Box::new(Proposition::Predicate(
                    "sorted".to_string(),
                    vec![Expression::Variable("l".to_string())],
                )),
            ),
        };

        // Build the Lean context with prelude definitions and axiom
        let lean_code = build_lean_context(prelude_nodes, vec![axiom]);

        // Verify the code structure before validation
        assert!(!lean_code.is_empty());
        assert!(lean_code.contains("list_emp_sorted"));
        assert!(lean_code.contains("theorem"));

        // Validate the generated Lean code using the Lean backend
        let result = validate_lean_code(&lean_code);
        assert!(
            result.is_ok(),
            "Expected validation to succeed, but got: {:?}\nLean code:\n{}",
            result,
            lean_code
        );
    }

    #[test]
    fn test_axiom_list_single_sorted() {
        // Load the prelude predicates
        let prelude_nodes = predicates::parse_all().expect("Failed to parse prelude");

        // Create an axiom: ∀ (l : ilist), ((len l 1) → (sorted l))
        let axiom = Axiom {
            name: "list_single_sorted".to_string(),
            params: vec![Parameter::universal(
                "l".to_string(),
                Type::Named("ilist".to_string()),
            )],
            body: Proposition::Implication(
                Box::new(Proposition::Predicate(
                    "len".to_string(),
                    vec![
                        Expression::Variable("l".to_string()),
                        Expression::Literal(1),
                    ],
                )),
                Box::new(Proposition::Predicate(
                    "sorted".to_string(),
                    vec![Expression::Variable("l".to_string())],
                )),
            ),
        };

        // Build the Lean context with prelude definitions and axiom
        let lean_code = build_lean_context(prelude_nodes, vec![axiom]);

        // Verify the code structure before validation
        assert!(!lean_code.is_empty());
        assert!(lean_code.contains("list_single_sorted"));
        assert!(lean_code.contains("theorem"));

        // Validate the generated Lean code using the Lean backend
        let result = validate_lean_code(&lean_code);
        assert!(
            result.is_ok(),
            "Expected validation to succeed, but got: {:?}\nLean code:\n{}",
            result,
            lean_code
        );
    }

    #[test]
    fn test_axiom_list_tl_sorted() {
        // Load the prelude predicates
        let prelude_nodes = predicates::parse_all().expect("Failed to parse prelude");

        // Create an axiom: ∀ (l : ilist), (∀ (l1 : ilist), (((tl l l1) ∧ (sorted l)) → (sorted l1)))
        let axiom = Axiom {
            name: "list_tl_sorted".to_string(),
            params: vec![
                Parameter::universal("l".to_string(), Type::Named("ilist".to_string())),
                Parameter::universal("l1".to_string(), Type::Named("ilist".to_string())),
            ],
            body: Proposition::Implication(
                Box::new(Proposition::And(
                    Box::new(Proposition::Predicate(
                        "tl".to_string(),
                        vec![
                            Expression::Variable("l".to_string()),
                            Expression::Variable("l1".to_string()),
                        ],
                    )),
                    Box::new(Proposition::Predicate(
                        "sorted".to_string(),
                        vec![Expression::Variable("l".to_string())],
                    )),
                )),
                Box::new(Proposition::Predicate(
                    "sorted".to_string(),
                    vec![Expression::Variable("l1".to_string())],
                )),
            ),
        };

        // Build the Lean context with prelude definitions and axiom
        let lean_code = build_lean_context(prelude_nodes, vec![axiom]);

        // Verify the code structure before validation
        assert!(!lean_code.is_empty());
        assert!(lean_code.contains("list_tl_sorted"));
        assert!(lean_code.contains("theorem"));

        // Validate the generated Lean code using the Lean backend
        let result = validate_lean_code(&lean_code);
        assert!(
            result.is_ok(),
            "Expected validation to succeed, but got: {:?}\nLean code:\n{}",
            result,
            lean_code
        );
    }

    #[test]
    fn test_axiom_list_hd_sorted() {
        // Load the prelude predicates
        let prelude_nodes = predicates::parse_all().expect("Failed to parse prelude");

        // Create an axiom: ∀ (l : ilist), (∀ (l1 : ilist), (∀ (x : Int), (∀ (y : Int), (((tl l l1) ∧ (sorted l)) → ((emp l1) ∨ (((hd l1 y) ∧ (hd l x)) → (x <= y)))))))
        let axiom = Axiom {
            name: "list_hd_sorted".to_string(),
            params: vec![
                Parameter::universal("l".to_string(), Type::Named("ilist".to_string())),
                Parameter::universal("l1".to_string(), Type::Named("ilist".to_string())),
                Parameter::universal("x".to_string(), Type::Named("Int".to_string())),
                Parameter::universal("y".to_string(), Type::Named("Int".to_string())),
            ],
            body: Proposition::Implication(
                Box::new(Proposition::And(
                    Box::new(Proposition::Predicate(
                        "tl".to_string(),
                        vec![
                            Expression::Variable("l".to_string()),
                            Expression::Variable("l1".to_string()),
                        ],
                    )),
                    Box::new(Proposition::Predicate(
                        "sorted".to_string(),
                        vec![Expression::Variable("l".to_string())],
                    )),
                )),
                Box::new(Proposition::Or(
                    Box::new(Proposition::Predicate(
                        "emp".to_string(),
                        vec![Expression::Variable("l1".to_string())],
                    )),
                    Box::new(Proposition::Implication(
                        Box::new(Proposition::And(
                            Box::new(Proposition::Predicate(
                                "hd".to_string(),
                                vec![
                                    Expression::Variable("l1".to_string()),
                                    Expression::Variable("y".to_string()),
                                ],
                            )),
                            Box::new(Proposition::Predicate(
                                "hd".to_string(),
                                vec![
                                    Expression::Variable("l".to_string()),
                                    Expression::Variable("x".to_string()),
                                ],
                            )),
                        )),
                        Box::new(Proposition::Expr(Expression::BinaryOp(
                            Box::new(Expression::Variable("x".to_string())),
                            BinaryOp::Lte,
                            Box::new(Expression::Variable("y".to_string())),
                        ))),
                    )),
                )),
            ),
        };

        // Build the Lean context with prelude definitions and axiom
        let lean_code = build_lean_context(prelude_nodes, vec![axiom]);

        // Verify the code structure before validation
        assert!(!lean_code.is_empty());
        assert!(lean_code.contains("list_hd_sorted"));
        assert!(lean_code.contains("theorem"));

        // Validate the generated Lean code using the Lean backend
        let result = validate_lean_code(&lean_code);
        assert!(
            result.is_ok(),
            "Expected validation to succeed, but got: {:?}\nLean code:\n{}",
            result,
            lean_code
        );
    }

    #[test]
    fn test_axiom_list_sorted_hd() {
        // Load the prelude predicates
        let prelude_nodes = predicates::parse_all().expect("Failed to parse prelude");

        // Create an axiom: ∀ (l : ilist), (∀ (l1 : ilist), (∀ (x : Int), (∀ (y : Int), (((tl l l1) ∧ ((sorted l1) ∧ ((hd l y) ∧ ((hd l1 x) ∧ (y <= x))))) → (sorted l)))))
        let axiom = Axiom {
            name: "list_sorted_hd".to_string(),
            params: vec![
                Parameter::universal("l".to_string(), Type::Named("ilist".to_string())),
                Parameter::universal("l1".to_string(), Type::Named("ilist".to_string())),
                Parameter::universal("x".to_string(), Type::Named("Int".to_string())),
                Parameter::universal("y".to_string(), Type::Named("Int".to_string())),
            ],
            body: Proposition::Implication(
                Box::new(Proposition::And(
                    Box::new(Proposition::Predicate(
                        "tl".to_string(),
                        vec![
                            Expression::Variable("l".to_string()),
                            Expression::Variable("l1".to_string()),
                        ],
                    )),
                    Box::new(Proposition::And(
                        Box::new(Proposition::Predicate(
                            "sorted".to_string(),
                            vec![Expression::Variable("l1".to_string())],
                        )),
                        Box::new(Proposition::And(
                            Box::new(Proposition::Predicate(
                                "hd".to_string(),
                                vec![
                                    Expression::Variable("l".to_string()),
                                    Expression::Variable("y".to_string()),
                                ],
                            )),
                            Box::new(Proposition::And(
                                Box::new(Proposition::Predicate(
                                    "hd".to_string(),
                                    vec![
                                        Expression::Variable("l1".to_string()),
                                        Expression::Variable("x".to_string()),
                                    ],
                                )),
                                Box::new(Proposition::Expr(Expression::BinaryOp(
                                    Box::new(Expression::Variable("y".to_string())),
                                    BinaryOp::Lte,
                                    Box::new(Expression::Variable("x".to_string())),
                                ))),
                            )),
                        )),
                    )),
                )),
                Box::new(Proposition::Predicate(
                    "sorted".to_string(),
                    vec![Expression::Variable("l".to_string())],
                )),
            ),
        };

        // Build the Lean context with prelude definitions and axiom
        let lean_code = build_lean_context(prelude_nodes, vec![axiom]);

        // Verify the code structure before validation
        assert!(!lean_code.is_empty());
        assert!(lean_code.contains("list_sorted_hd"));
        assert!(lean_code.contains("theorem"));

        // Validate the generated Lean code using the Lean backend
        let result = validate_lean_code(&lean_code);
        assert!(
            result.is_ok(),
            "Expected validation to succeed, but got: {:?}\nLean code:\n{}",
            result,
            lean_code
        );
    }
}

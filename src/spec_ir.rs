use std::fmt;

use crate::{
    ToLean, VarName,
    ocamlparser::OcamlParser,
    prog_ir::{self, BinaryOp, ConstructorName, Type, UnaryOp},
};

/// A specification axiom that can be translated to Lean theorems
#[derive(Debug, Clone)]
pub struct Axiom {
    pub name: String,
    pub params: Vec<Parameter>,
    pub body: Proposition,
    pub proof: Option<String>,
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
    pub name: VarName,
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
    Variable(VarName),

    /// Literal values
    Literal(Literal),

    /// Binary arithmetic/comparison operators: >=, >, ==, <, <=, +, -, etc.
    BinaryOp(Box<Expression>, BinaryOp, Box<Expression>),

    /// Unary operators: negation, etc.
    UnaryOp(UnaryOp, Box<Expression>),

    /// Constructor application: .Cons x .Nil
    Constructor(ConstructorName, Vec<Expression>),
}

impl Parameter {
    pub fn universal(name: impl Into<VarName>, typ: Type) -> Self {
        Parameter {
            name: name.into(),
            typ,
            quantifier: Quantifier::Universal,
        }
    }

    pub fn existential(name: impl Into<VarName>, typ: Type) -> Self {
        Parameter {
            name: name.into(),
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

        let proof = match self.proof.as_deref() {
            Some("sorry") | None => "sorry".to_string(),
            Some(p) => format!("by {}", p),
        };
        format!("theorem {} : {} := {}", self.name, body_str, proof)
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
                format!("({} → {})", p.to_lean(), q.to_lean())
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
            Expression::Variable(name) => name.to_string(),
            Expression::Literal(n) => n.to_string(),
            Expression::BinaryOp(left, op, right) => {
                format!("({} {} {})", left.to_lean(), op.to_lean(), right.to_lean())
            }
            Expression::UnaryOp(op, expr) => {
                format!("{}({})", op.to_lean(), expr.to_lean())
            }
            Expression::Constructor(name, args) => {
                if args.is_empty() {
                    format!(".{}", name)
                } else {
                    let args_str = args
                        .iter()
                        .map(|arg| arg.to_lean())
                        .collect::<Vec<_>>()
                        .join(" ");
                    format!("(.{} {})", name, args_str)
                }
            }
        }
    }
}

/// Helper functions to parse predicate definitions for the ilist datatype
pub mod predicates {
    use super::*;

    pub const PRELUDE: &str = "type [@grind] ilist = Nil | Cons of int * ilist
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

/// Helper to create an ilist type definition
pub fn create_ilist_type() -> prog_ir::TypeDecl {
    prog_ir::TypeDecl {
        name: "ilist".to_string(),
        variants: vec![
            prog_ir::Variant {
                name: "Nil".to_string(),
                fields: vec![],
            },
            prog_ir::Variant {
                name: "Cons".to_string(),
                fields: vec![Type::Int, Type::Named("ilist".to_string())],
            },
        ],
        attributes: vec![],
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::lean_validation::validate_lean_code;

    #[test]
    fn test_axiom_with_prelude() {
        // Load the prelude predicates
        let prelude_nodes =
            predicates::parse_all().unwrap_or_else(|e| panic!("Failed to parse prelude: {}", e));

        // Create an axiom: ∀ (l : ilist), (∀ (x : Int), ((emp l) → ¬(hd l x)))
        let axiom = Axiom {
            name: "list_emp_no_hd".to_string(),
            params: vec![
                Parameter::universal("l", Type::Named("ilist".to_string())),
                Parameter::universal("x", Type::Named("Int".to_string())),
            ],
            body: Proposition::Implication(
                Box::new(Proposition::Predicate(
                    "emp".to_string(),
                    vec![Expression::Variable("l".into())],
                )),
                Box::new(Proposition::Not(Box::new(Proposition::Predicate(
                    "hd".to_string(),
                    vec![
                        Expression::Variable("l".into()),
                        Expression::Variable("x".into()),
                    ],
                )))),
            ),
            proof: Some("grind".to_string()),
        };

        // Build the Lean context with prelude definitions and axiom
        let lean_code = crate::lean_backend::LeanContextBuilder::new()
            .with_nodes(prelude_nodes)
            .with_axioms(vec![axiom])
            .build();

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
    fn test_axiom_with_type_theorems() {
        // Load the prelude predicates
        let prelude_nodes =
            predicates::parse_all().unwrap_or_else(|e| panic!("Failed to parse prelude: {}", e));

        // Create an axiom with BEq theorems
        let axiom = Axiom {
            name: "list_emp_no_hd_with_beq".to_string(),
            params: vec![
                Parameter::universal("l", Type::Named("ilist".to_string())),
                Parameter::universal("x", Type::Named("Int".to_string())),
            ],
            body: Proposition::Implication(
                Box::new(Proposition::Predicate(
                    "emp".to_string(),
                    vec![Expression::Variable("l".into())],
                )),
                Box::new(Proposition::Not(Box::new(Proposition::Predicate(
                    "hd".to_string(),
                    vec![
                        Expression::Variable("l".into()),
                        Expression::Variable("x".into()),
                    ],
                )))),
            ),
            proof: Some("grind".to_string()),
        };

        // Build context with automatic BEq theorem attachment using builder pattern
        let ilist_type = create_ilist_type();
        let lean_code = crate::lean_backend::LeanContextBuilder::new()
            .with_nodes(prelude_nodes)
            .with_axioms(vec![axiom])
            .with_type_theorems("ilist", ilist_type.generate_complete_lawful_beq())
            .build();

        // Verify the code structure
        assert!(!lean_code.is_empty());
        assert!(lean_code.contains("list_emp_no_hd_with_beq"));
        assert!(lean_code.contains("beq_nil_nil"));
        assert!(lean_code.contains("beq_cons_cons"));

        // Validate the generated Lean code
        let result = validate_lean_code(&lean_code);
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
        let prelude_nodes =
            predicates::parse_all().unwrap_or_else(|e| panic!("Failed to parse prelude: {}", e));

        // Create an axiom: ∀ (l : ilist), (∀ (l1 : ilist), ((emp l) → ¬(tl l l1)))
        let axiom = Axiom {
            name: "list_emp_no_tl".to_string(),
            params: vec![
                Parameter::universal("l", Type::Named("ilist".to_string())),
                Parameter::universal("l1", Type::Named("ilist".to_string())),
            ],
            body: Proposition::Implication(
                Box::new(Proposition::Predicate(
                    "emp".to_string(),
                    vec![Expression::Variable("l".into())],
                )),
                Box::new(Proposition::Not(Box::new(Proposition::Predicate(
                    "tl".to_string(),
                    vec![
                        Expression::Variable("l".into()),
                        Expression::Variable("l1".into()),
                    ],
                )))),
            ),
            proof: Some("grind".to_string()),
        };

        // Build the Lean context with prelude definitions and axiom
        let lean_code = crate::lean_backend::LeanContextBuilder::new()
            .with_nodes(prelude_nodes)
            .with_axioms(vec![axiom])
            .build();

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
        let prelude_nodes =
            predicates::parse_all().unwrap_or_else(|e| panic!("Failed to parse prelude: {}", e));

        // Create an axiom: ∀ (l : ilist), (∀ (x : Int), ((hd l x) → ¬(emp l)))
        let axiom = Axiom {
            name: "list_hd_no_emp".to_string(),
            params: vec![
                Parameter::universal("l", Type::Named("ilist".to_string())),
                Parameter::universal("x", Type::Named("Int".to_string())),
            ],
            body: Proposition::Implication(
                Box::new(Proposition::Predicate(
                    "hd".to_string(),
                    vec![
                        Expression::Variable("l".into()),
                        Expression::Variable("x".into()),
                    ],
                )),
                Box::new(Proposition::Not(Box::new(Proposition::Predicate(
                    "emp".to_string(),
                    vec![Expression::Variable("l".into())],
                )))),
            ),
            proof: Some("grind".to_string()),
        };

        // Build the Lean context with prelude definitions and axiom
        let lean_code = crate::lean_backend::LeanContextBuilder::new()
            .with_nodes(prelude_nodes)
            .with_axioms(vec![axiom])
            .build();

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
        let prelude_nodes =
            predicates::parse_all().unwrap_or_else(|e| panic!("Failed to parse prelude: {}", e));

        // Create an axiom: ∀ (l : ilist), (∀ (l1 : ilist), ((tl l l1) → ¬(emp l)))
        let axiom = Axiom {
            name: "list_tl_no_emp".to_string(),
            params: vec![
                Parameter::universal("l", Type::Named("ilist".to_string())),
                Parameter::universal("l1", Type::Named("ilist".to_string())),
            ],
            body: Proposition::Implication(
                Box::new(Proposition::Predicate(
                    "tl".to_string(),
                    vec![
                        Expression::Variable("l".into()),
                        Expression::Variable("l1".into()),
                    ],
                )),
                Box::new(Proposition::Not(Box::new(Proposition::Predicate(
                    "emp".to_string(),
                    vec![Expression::Variable("l".into())],
                )))),
            ),
            proof: Some("grind".to_string()),
        };

        // Build the Lean context with prelude definitions and axiom
        let lean_code = crate::lean_backend::LeanContextBuilder::new()
            .with_nodes(prelude_nodes)
            .with_axioms(vec![axiom])
            .build();

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
        let prelude_nodes =
            predicates::parse_all().unwrap_or_else(|e| panic!("Failed to parse prelude: {}", e));

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
                    vec![Expression::Variable("l".into())],
                )),
                Box::new(Proposition::Predicate(
                    "len".to_string(),
                    vec![Expression::Variable("l".into()), Expression::Literal(0)],
                )),
            ),
            proof: Some("grind".to_string()),
        };

        // Build the Lean context with prelude definitions and axiom
        let lean_code = crate::lean_backend::LeanContextBuilder::new()
            .with_nodes(prelude_nodes)
            .with_axioms(vec![axiom])
            .build();

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
        let prelude_nodes =
            predicates::parse_all().unwrap_or_else(|e| panic!("Failed to parse prelude: {}", e));

        // Create an axiom: ∀ (l : ilist), (∀ (n : Int), (((len l n) ∧ (n > 0)) → ¬(emp l)))
        let axiom = Axiom {
            name: "list_positive_len_is_not_emp".to_string(),
            params: vec![
                Parameter::universal("l", Type::Named("ilist".to_string())),
                Parameter::universal("n", Type::Named("Int".to_string())),
            ],
            body: Proposition::Implication(
                Box::new(Proposition::And(
                    Box::new(Proposition::Predicate(
                        "len".to_string(),
                        vec![
                            Expression::Variable("l".into()),
                            Expression::Variable("n".into()),
                        ],
                    )),
                    Box::new(Proposition::Expr(Expression::BinaryOp(
                        Box::new(Expression::Variable("n".into())),
                        BinaryOp::Gt,
                        Box::new(Expression::Literal(0)),
                    ))),
                )),
                Box::new(Proposition::Not(Box::new(Proposition::Predicate(
                    "emp".to_string(),
                    vec![Expression::Variable("l".into())],
                )))),
            ),
            proof: Some("grind".to_string()),
        };

        // Build the Lean context with prelude definitions and axiom
        let lean_code = crate::lean_backend::LeanContextBuilder::new()
            .with_nodes(prelude_nodes)
            .with_axioms(vec![axiom])
            .build();

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
        let prelude_nodes =
            predicates::parse_all().unwrap_or_else(|e| panic!("Failed to parse prelude: {}", e));

        // Create an axiom: ∀ (l : ilist), (∀ (l1 : ilist), (∀ (n : Int), (((tl l l1) ∧ (len l1 n)) → (len l (n + 1)))))
        let axiom = Axiom {
            name: "list_tl_len_plus_1".to_string(),
            params: vec![
                Parameter::universal("l", Type::Named("ilist".to_string())),
                Parameter::universal("l1", Type::Named("ilist".to_string())),
                Parameter::universal("n", Type::Named("Int".to_string())),
            ],
            body: Proposition::Implication(
                Box::new(Proposition::And(
                    Box::new(Proposition::Predicate(
                        "tl".to_string(),
                        vec![
                            Expression::Variable("l".into()),
                            Expression::Variable("l1".into()),
                        ],
                    )),
                    Box::new(Proposition::Predicate(
                        "len".to_string(),
                        vec![
                            Expression::Variable("l1".into()),
                            Expression::Variable("n".into()),
                        ],
                    )),
                )),
                Box::new(Proposition::Predicate(
                    "len".to_string(),
                    vec![
                        Expression::Variable("l".into()),
                        Expression::BinaryOp(
                            Box::new(Expression::Variable("n".into())),
                            BinaryOp::Add,
                            Box::new(Expression::Literal(1)),
                        ),
                    ],
                )),
            ),
            proof: Some("grind".to_string()),
        };

        // Build the Lean context with prelude definitions and axiom
        let ilist_type = create_ilist_type();
        let lean_code = crate::lean_backend::LeanContextBuilder::new()
            .with_nodes(prelude_nodes)
            .with_axioms(vec![axiom])
            .with_type_theorems("ilist", ilist_type.generate_complete_lawful_beq())
            .build();

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
        let prelude_nodes =
            predicates::parse_all().unwrap_or_else(|e| panic!("Failed to parse prelude: {}", e));

        // Create an axiom: ∀ (l : ilist), (∀ (l1 : ilist), (∀ (n : Int), (((tl l l1) ∧ (len l (n + 1))) → (len l1 n))))
        let axiom = Axiom {
            name: "list_tl_plus_1_len".to_string(),
            params: vec![
                Parameter::universal("l", Type::Named("ilist".to_string())),
                Parameter::universal("l1", Type::Named("ilist".to_string())),
                Parameter::universal("n", Type::Named("Int".to_string())),
            ],
            body: Proposition::Implication(
                Box::new(Proposition::And(
                    Box::new(Proposition::Predicate(
                        "tl".to_string(),
                        vec![
                            Expression::Variable("l".into()),
                            Expression::Variable("l1".into()),
                        ],
                    )),
                    Box::new(Proposition::Predicate(
                        "len".to_string(),
                        vec![
                            Expression::Variable("l".into()),
                            Expression::BinaryOp(
                                Box::new(Expression::Variable("n".into())),
                                BinaryOp::Add,
                                Box::new(Expression::Literal(1)),
                            ),
                        ],
                    )),
                )),
                Box::new(Proposition::Predicate(
                    "len".to_string(),
                    vec![
                        Expression::Variable("l1".into()),
                        Expression::Variable("n".into()),
                    ],
                )),
            ),
            proof: Some("grind".to_string()),
        };

        // Build the Lean context with prelude definitions and axiom
        let ilist_type = create_ilist_type();
        let lean_code = crate::lean_backend::LeanContextBuilder::new()
            .with_nodes(prelude_nodes)
            .with_axioms(vec![axiom])
            .with_type_theorems("ilist", ilist_type.generate_complete_lawful_beq())
            .build();

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
        let prelude_nodes =
            predicates::parse_all().unwrap_or_else(|e| panic!("Failed to parse prelude: {}", e));

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
                    vec![Expression::Variable("l".into())],
                )),
                Box::new(Proposition::Predicate(
                    "sorted".to_string(),
                    vec![Expression::Variable("l".into())],
                )),
            ),
            proof: Some("grind".to_string()),
        };

        // Build the Lean context with prelude definitions and axiom
        let ilist_type = create_ilist_type();
        let lean_code = crate::lean_backend::LeanContextBuilder::new()
            .with_nodes(prelude_nodes)
            .with_axioms(vec![axiom])
            .with_type_theorems("ilist", ilist_type.generate_complete_lawful_beq())
            .build();

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
        let prelude_nodes =
            predicates::parse_all().unwrap_or_else(|e| panic!("Failed to parse prelude: {}", e));

        // Create an axiom that matches the Lean theorem list_single_sorted_1:
        // ∀ (l : ilist), (∀ (x : Int), ((l == .Cons x .Nil) → (sorted l)))
        let axiom = Axiom {
            name: "list_single_sorted_1".to_string(),
            params: vec![
                Parameter::universal("l", Type::Named("ilist".to_string())),
                Parameter::universal("x", Type::Named("Int".to_string())),
            ],
            body: Proposition::Implication(
                Box::new(Proposition::Equality(
                    Box::new(Proposition::Expr(Expression::Variable("l".into()))),
                    Box::new(Proposition::Expr(Expression::Constructor(
                        ConstructorName::Simple("Cons".to_string()),
                        vec![
                            Expression::Variable("x".into()),
                            Expression::Constructor(
                                ConstructorName::Simple("Nil".to_string()),
                                vec![],
                            ),
                        ],
                    ))),
                )),
                Box::new(Proposition::Predicate(
                    "sorted".to_string(),
                    vec![Expression::Variable("l".into())],
                )),
            ),
            proof: Some("grind".to_string()),
        };

        // Build the Lean context with prelude definitions and axiom
        let ilist_type = create_ilist_type();
        let lean_code = crate::lean_backend::LeanContextBuilder::new()
            .with_nodes(prelude_nodes)
            .with_axioms(vec![axiom])
            .with_type_theorems("ilist", ilist_type.generate_complete_lawful_beq())
            .build();

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
        let prelude_nodes =
            predicates::parse_all().unwrap_or_else(|e| panic!("Failed to parse prelude: {}", e));

        // Create an axiom: ∀ (l : ilist), (∀ (l1 : ilist), (((tl l l1) ∧ (sorted l)) → (sorted l1)))
        let axiom = Axiom {
            name: "list_tl_sorted".to_string(),
            params: vec![
                Parameter::universal("l", Type::Named("ilist".to_string())),
                Parameter::universal("l1", Type::Named("ilist".to_string())),
            ],
            body: Proposition::Implication(
                Box::new(Proposition::And(
                    Box::new(Proposition::Predicate(
                        "tl".to_string(),
                        vec![
                            Expression::Variable("l".into()),
                            Expression::Variable("l1".into()),
                        ],
                    )),
                    Box::new(Proposition::Predicate(
                        "sorted".to_string(),
                        vec![Expression::Variable("l".into())],
                    )),
                )),
                Box::new(Proposition::Predicate(
                    "sorted".to_string(),
                    vec![Expression::Variable("l1".into())],
                )),
            ),
            proof: Some("grind".to_string()),
        };

        // Build the Lean context with prelude definitions and axiom
        let ilist_type = create_ilist_type();
        let lean_code = crate::lean_backend::LeanContextBuilder::new()
            .with_nodes(prelude_nodes)
            .with_axioms(vec![axiom])
            .with_type_theorems("ilist", ilist_type.generate_complete_lawful_beq())
            .build();

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
        let prelude_nodes =
            predicates::parse_all().unwrap_or_else(|e| panic!("Failed to parse prelude: {}", e));

        // Create an axiom: ∀ (l : ilist), (∀ (l1 : ilist), (∀ (x : Int), (∀ (y : Int), (((tl l l1) ∧ (sorted l)) → ((emp l1) ∨ (((hd l1 y) ∧ (hd l x)) → (x <= y)))))))
        let axiom = Axiom {
            name: "list_hd_sorted".to_string(),
            params: vec![
                Parameter::universal("l", Type::Named("ilist".to_string())),
                Parameter::universal("l1", Type::Named("ilist".to_string())),
                Parameter::universal("x", Type::Named("Int".to_string())),
                Parameter::universal("y", Type::Named("Int".to_string())),
            ],
            body: Proposition::Implication(
                Box::new(Proposition::And(
                    Box::new(Proposition::Predicate(
                        "tl".to_string(),
                        vec![
                            Expression::Variable("l".into()),
                            Expression::Variable("l1".into()),
                        ],
                    )),
                    Box::new(Proposition::Predicate(
                        "sorted".to_string(),
                        vec![Expression::Variable("l".into())],
                    )),
                )),
                Box::new(Proposition::Or(
                    Box::new(Proposition::Predicate(
                        "emp".to_string(),
                        vec![Expression::Variable("l1".into())],
                    )),
                    Box::new(Proposition::Implication(
                        Box::new(Proposition::And(
                            Box::new(Proposition::Predicate(
                                "hd".to_string(),
                                vec![
                                    Expression::Variable("l1".into()),
                                    Expression::Variable("y".into()),
                                ],
                            )),
                            Box::new(Proposition::Predicate(
                                "hd".to_string(),
                                vec![
                                    Expression::Variable("l".into()),
                                    Expression::Variable("x".into()),
                                ],
                            )),
                        )),
                        Box::new(Proposition::Expr(Expression::BinaryOp(
                            Box::new(Expression::Variable("x".into())),
                            BinaryOp::Lte,
                            Box::new(Expression::Variable("y".into())),
                        ))),
                    )),
                )),
            ),
            proof: Some("grind".to_string()),
        };

        // Build the Lean context with prelude definitions and axiom
        let ilist_type = create_ilist_type();
        let lean_code = crate::lean_backend::LeanContextBuilder::new()
            .with_nodes(prelude_nodes)
            .with_axioms(vec![axiom])
            .with_type_theorems("ilist", ilist_type.generate_complete_lawful_beq())
            .build();

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
        let prelude_nodes =
            predicates::parse_all().unwrap_or_else(|e| panic!("Failed to parse prelude: {}", e));

        // Create an axiom: ∀ (l : ilist), (∀ (l1 : ilist), (∀ (x : Int), (∀ (y : Int), (((tl l l1) ∧ ((sorted l1) ∧ ((hd l y) ∧ ((hd l1 x) ∧ (y <= x))))) → (sorted l)))))
        let axiom = Axiom {
            name: "list_sorted_hd".to_string(),
            params: vec![
                Parameter::universal("l", Type::Named("ilist".to_string())),
                Parameter::universal("l1", Type::Named("ilist".to_string())),
                Parameter::universal("x", Type::Named("Int".to_string())),
                Parameter::universal("y", Type::Named("Int".to_string())),
            ],
            body: Proposition::Implication(
                Box::new(Proposition::And(
                    Box::new(Proposition::Predicate(
                        "tl".to_string(),
                        vec![
                            Expression::Variable("l".into()),
                            Expression::Variable("l1".into()),
                        ],
                    )),
                    Box::new(Proposition::And(
                        Box::new(Proposition::Predicate(
                            "sorted".to_string(),
                            vec![Expression::Variable("l1".into())],
                        )),
                        Box::new(Proposition::And(
                            Box::new(Proposition::Predicate(
                                "hd".to_string(),
                                vec![
                                    Expression::Variable("l".into()),
                                    Expression::Variable("y".into()),
                                ],
                            )),
                            Box::new(Proposition::And(
                                Box::new(Proposition::Predicate(
                                    "hd".to_string(),
                                    vec![
                                        Expression::Variable("l1".into()),
                                        Expression::Variable("x".into()),
                                    ],
                                )),
                                Box::new(Proposition::Expr(Expression::BinaryOp(
                                    Box::new(Expression::Variable("y".into())),
                                    BinaryOp::Lte,
                                    Box::new(Expression::Variable("x".into())),
                                ))),
                            )),
                        )),
                    )),
                )),
                Box::new(Proposition::Predicate(
                    "sorted".to_string(),
                    vec![Expression::Variable("l".into())],
                )),
            ),
            proof: Some("grind".to_string()),
        };

        // Build the Lean context with prelude definitions and axiom
        let ilist_type = create_ilist_type();
        let lean_code = crate::lean_backend::LeanContextBuilder::new()
            .with_nodes(prelude_nodes)
            .with_axioms(vec![axiom])
            .with_type_theorems("ilist", ilist_type.generate_complete_lawful_beq())
            .build();

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

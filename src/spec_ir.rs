use std::fmt;

use crate::{
    Literal, ToLean, VarName,
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
#[derive(Debug, Clone, PartialEq)]
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

    /// Tuple expression: (e1, e2, e3, ...)
    Tuple(Vec<Expression>),

    /// If-then-else expression: ite cond then_expr else_expr
    IfThenElse {
        condition: Box<Expression>,
        then_branch: Box<Expression>,
        else_branch: Box<Expression>,
    },

    /// Logical negation: not expr
    Not(Box<Expression>),
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

    /// Convert a list of (VarName, Type) pairs into universal parameters
    pub fn from_vars(params: &[(VarName, Type)]) -> Vec<Parameter> {
        params
            .iter()
            .map(|(name, typ)| Parameter::universal(name.clone(), typ.clone()))
            .collect()
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

impl Axiom {
    /// Suggests an appropriate proof tactic based on axiom characteristics.
    /// Uses "aesop" for axioms with existential quantifiers, "grind" otherwise.
    pub fn suggest_proof_tactic(&self) -> String {
        // Count existential quantifiers
        let existential_count = self
            .params
            .iter()
            .filter(|p| p.quantifier == Quantifier::Existential)
            .count();

        if existential_count > 0 {
            let mut tactic =
                "\ntry aesop (config := { maxRuleHeartbeats := 20000 })\nintros\n".to_string();

            // Generate refine/rotate_left pairs for each existential
            for _ in 0..existential_count {
                tactic.push_str("refine ⟨?_, ?_⟩\nrotate_left\n");
            }

            tactic.push_str("all_goals try grind\nall_goals try aesop\n");

            tactic
        } else {
            "grind".to_string()
        }
    }
}

impl fmt::Display for Axiom {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "let[@axiom] {}", self.name)?;
        for param in &self.params {
            write!(f, " {}", param)?;
        }
        write!(f, " = {}", self.body)?;
        Ok(())
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

impl Proposition {
    /// Format a predicate for display (OCaml syntax), handling both empty and non-empty argument lists.
    fn format_predicate_display(name: &str, args: &[Expression]) -> String {
        if args.is_empty() {
            name.to_string()
        } else {
            let args_str = args
                .iter()
                .map(|e| e.to_string())
                .collect::<Vec<_>>()
                .join(" ");
            format!("({} {})", name, args_str)
        }
    }

    /// Format a predicate for Lean display, handling both empty and non-empty argument lists.
    fn format_predicate_lean(name: &str, args: &[Expression]) -> String {
        if args.is_empty() {
            name.to_string()
        } else {
            let args_str = args
                .iter()
                .map(|e| e.to_lean())
                .collect::<Vec<_>>()
                .join(" ");
            format!("({} {})", name, args_str)
        }
    }

    /// Format a constructor for OCaml display
    fn format_constructor_display(name: &ConstructorName, args: &[Expression]) -> String {
        let name_str = name.to_string();
        if args.is_empty() {
            name_str
        } else {
            let args_str = args
                .iter()
                .map(|e| e.to_string())
                .collect::<Vec<_>>()
                .join(", ");
            format!("({}({}))", name_str, args_str)
        }
    }

    /// Format a constructor for Lean display (with leading dot for Lean pattern syntax)
    fn format_constructor_lean(name: &ConstructorName, args: &[Expression]) -> String {
        let name_str = format!(".{}", name);
        if args.is_empty() {
            name_str
        } else {
            let args_str = args
                .iter()
                .map(|e| e.to_lean())
                .collect::<Vec<_>>()
                .join(" ");
            format!("({} {})", name_str, args_str)
        }
    }

    /// Fold over the structure of a proposition, applying a transformation function at each node.
    /// The transformation function receives the current proposition and must return the transformed result.
    /// This enables bottom-up structural transformations on the proposition tree.
    pub fn fold<F>(self, f: &F) -> Proposition
    where
        F: Fn(Proposition) -> Proposition,
    {
        let folded = match self {
            Proposition::Expr(expr) => Proposition::Expr(expr),
            Proposition::Predicate(name, args) => Proposition::Predicate(name, args),
            Proposition::Implication(ant, cons) => {
                Proposition::Implication(Box::new(ant.fold(f)), Box::new(cons.fold(f)))
            }
            Proposition::Equality(left, right) => {
                Proposition::Equality(Box::new(left.fold(f)), Box::new(right.fold(f)))
            }
            Proposition::And(left, right) => {
                Proposition::And(Box::new(left.fold(f)), Box::new(right.fold(f)))
            }
            Proposition::Or(left, right) => {
                Proposition::Or(Box::new(left.fold(f)), Box::new(right.fold(f)))
            }
            Proposition::Not(inner) => Proposition::Not(Box::new(inner.fold(f))),
            Proposition::Iff(left, right) => {
                Proposition::Iff(Box::new(left.fold(f)), Box::new(right.fold(f)))
            }
        };
        f(folded)
    }

    pub fn as_expr(&self) -> &Expression {
        match self {
            Proposition::Expr(expression) => expression,
            _ => panic!("Expected Proposition::Expr, got {:?}", self),
        }
    }

    /// Validate that this proposition does not contain Implication or Equality propositions.
    /// Panics with descriptive messages if violations are found.
    /// Assumes that step propositions should only contain: Expr, Predicate, And, Or, Not, Iff.
    pub fn assert_no_implications_or_equalities(&self) {
        match self {
            Proposition::Implication(_, _) => panic!(
                "Steps should not contain Implication propositions; these are composed after augmentation"
            ),
            Proposition::Equality(_, _) => panic!(
                "Steps should not contain Equality propositions; only expressions can be equalities"
            ),
            Proposition::And(left, right) => {
                left.assert_no_implications_or_equalities();
                right.assert_no_implications_or_equalities();
            }
            Proposition::Or(left, right) => {
                left.assert_no_implications_or_equalities();
                right.assert_no_implications_or_equalities();
            }
            Proposition::Not(inner) => inner.assert_no_implications_or_equalities(),
            Proposition::Iff(left, right) => {
                left.assert_no_implications_or_equalities();
                right.assert_no_implications_or_equalities();
            }
            _ => {}
        }
    }
}

impl fmt::Display for Proposition {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Proposition::Expr(expr) => write!(f, "{}", expr),
            Proposition::Predicate(name, args) => {
                write!(f, "{}", Proposition::format_predicate_display(name, args))
            }
            Proposition::Implication(p, q) => {
                write!(f, "({})#==>({})", p, q)
            }
            Proposition::Equality(p, q) => {
                write!(f, "({})#==({})", p, q)
            }
            Proposition::And(p, q) => {
                write!(f, "({} && {})", p, q)
            }
            Proposition::Or(p, q) => {
                write!(f, "({} || {})", p, q)
            }
            Proposition::Not(p) => {
                write!(f, "(not ({}))", p)
            }
            Proposition::Iff(p, q) => {
                write!(f, "(iff {} {})", p, q)
            }
        }
    }
}

impl ToLean for Proposition {
    fn to_lean(&self) -> String {
        match self {
            Proposition::Expr(expr) => expr.to_lean(),
            Proposition::Predicate(name, args) => Proposition::format_predicate_lean(name, args),
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

impl Expression {
    /// Check if an expression is a comparison/equality (pattern constraint), not arithmetic
    pub fn is_comparison(&self) -> bool {
        matches!(
            self,
            Expression::BinaryOp(_, op, _) if matches!(
                op,
                BinaryOp::Eq
                    | BinaryOp::Lt
                    | BinaryOp::Gt
                    | BinaryOp::Lte
                    | BinaryOp::Gte
            )
        )
    }
}

impl fmt::Display for Expression {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Expression::Variable(name) => write!(f, "{}", name),
            Expression::Literal(n) => write!(f, "{}", n),
            Expression::BinaryOp(left, op, right) => {
                write!(f, "({} {} {})", left, op, right)
            }
            Expression::UnaryOp(op, expr) => {
                write!(f, "{}({})", op, expr)
            }
            Expression::Constructor(name, args) => {
                write!(f, "{}", Proposition::format_constructor_display(name, args))
            }
            Expression::Tuple(elements) => {
                write!(
                    f,
                    "({})",
                    elements
                        .iter()
                        .map(|e| e.to_string())
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }
            Expression::IfThenElse {
                condition,
                then_branch,
                else_branch,
            } => {
                write!(f, "(ite {} {} {})", condition, then_branch, else_branch)
            }
            Expression::Not(expr) => {
                write!(f, "(not {})", expr)
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
            Expression::Constructor(name, args) => Proposition::format_constructor_lean(name, args),
            Expression::Tuple(elements) => {
                format!(
                    "({})",
                    elements
                        .iter()
                        .map(|e| e.to_lean())
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }
            Expression::IfThenElse {
                condition,
                then_branch,
                else_branch,
            } => {
                format!(
                    "(ite {} {} {})",
                    condition.to_lean(),
                    then_branch.to_lean(),
                    else_branch.to_lean()
                )
            }
            Expression::Not(expr) => {
                format!("(not {})", expr.to_lean())
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
let [@simp] [@grind] rec sorted (l : ilist) : bool = match l with | Nil -> true | Cons (h, t) -> match t with | Nil -> true | Cons (h2, t2) -> (h <= h2) && sorted (Cons (h2, t2))
let [@simp] [@grind] rec mem (x : int) (l : ilist) : bool = match l with | Nil -> false | Cons (h, t) -> (h = x) || mem x t
let [@simp] [@grind] rec all_eq (l : ilist) (x : int) : bool = match l with | Nil -> true | Cons (h, t) -> (h = x) && all_eq t x";

    /// Parse all predicates and type definitions
    pub fn parse_all() -> Result<Vec<prog_ir::AstNode>, Box<dyn std::error::Error>> {
        OcamlParser::parse_nodes(PRELUDE)
    }
}

/// Helper to create an ilist type definition with @[grind] annotation
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
        attributes: vec!["grind".to_string()],
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::lean_validation::validate_lean_code;

    /// Helper function to set up common test fixtures
    fn setup_ilist_context() -> (Vec<prog_ir::AstNode>, prog_ir::TypeDecl) {
        let prelude_nodes =
            predicates::parse_all().unwrap_or_else(|e| panic!("Failed to parse prelude: {}", e));
        let ilist_type = create_ilist_type();
        (prelude_nodes, ilist_type)
    }

    #[test]
    fn test_axiom_with_prelude() {
        // Load the prelude predicates
        let (prelude_nodes, _) = setup_ilist_context();

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
            params: vec![Parameter::universal("l", Type::Named("ilist".to_string()))],
            body: Proposition::Implication(
                Box::new(Proposition::Predicate(
                    "emp".to_string(),
                    vec![Expression::Variable("l".into())],
                )),
                Box::new(Proposition::Predicate(
                    "len".to_string(),
                    vec![
                        Expression::Variable("l".into()),
                        Expression::Literal(Literal::Int(0)),
                    ],
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
                        Box::new(Expression::Literal(Literal::Int(0))),
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
                            Box::new(Expression::Literal(Literal::Int(1))),
                        ),
                    ],
                )),
            ),
            proof: Some("grind".to_string()),
        };

        // Build the Lean context with prelude definitions and axiom
        let (prelude_nodes, ilist_type) = setup_ilist_context();
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
                                Box::new(Expression::Literal(Literal::Int(1))),
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
            params: vec![Parameter::universal("l", Type::Named("ilist".to_string()))],
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
        let (prelude_nodes, ilist_type) = setup_ilist_context();

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
        let (prelude_nodes, ilist_type) = setup_ilist_context();

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
        let (prelude_nodes, ilist_type) = setup_ilist_context();

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
        let (prelude_nodes, ilist_type) = setup_ilist_context();

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

    #[test]
    fn test_axiom_list_mem() {
        let (prelude_nodes, ilist_type) = setup_ilist_context();

        // Create an axiom: ∀ (l : ilist), (∀ (x : Int), ((mem x l) → ¬(emp l)))
        let axiom = Axiom {
            name: "list_mem_not_emp".to_string(),
            params: vec![
                Parameter::universal("l", Type::Named("ilist".to_string())),
                Parameter::universal("x", Type::Named("Int".to_string())),
            ],
            body: Proposition::Implication(
                Box::new(Proposition::Predicate(
                    "mem".to_string(),
                    vec![
                        Expression::Variable("x".into()),
                        Expression::Variable("l".into()),
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
            .with_type_theorems("ilist", ilist_type.generate_complete_lawful_beq())
            .build();

        // Verify the code structure before validation
        assert!(!lean_code.is_empty());
        assert!(lean_code.contains("list_mem_not_emp"));
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
    fn test_axiom_list_all_eq() {
        let (prelude_nodes, ilist_type) = setup_ilist_context();

        // Create an axiom: ∀ (l : ilist), (∀ (x : Int), ((all_eq l x) → (emp l ∨ (hd l x))))
        let axiom = Axiom {
            name: "list_all_eq_hd".to_string(),
            params: vec![
                Parameter::universal("l", Type::Named("ilist".to_string())),
                Parameter::universal("x", Type::Named("Int".to_string())),
            ],
            body: Proposition::Implication(
                Box::new(Proposition::Predicate(
                    "all_eq".to_string(),
                    vec![
                        Expression::Variable("l".into()),
                        Expression::Variable("x".into()),
                    ],
                )),
                Box::new(Proposition::Or(
                    Box::new(Proposition::Predicate(
                        "emp".to_string(),
                        vec![Expression::Variable("l".into())],
                    )),
                    Box::new(Proposition::Predicate(
                        "hd".to_string(),
                        vec![
                            Expression::Variable("l".into()),
                            Expression::Variable("x".into()),
                        ],
                    )),
                )),
            ),
            proof: Some("grind".to_string()),
        };

        // Build the Lean context with prelude definitions and axiom
        let lean_code = crate::lean_backend::LeanContextBuilder::new()
            .with_nodes(prelude_nodes)
            .with_axioms(vec![axiom])
            .with_type_theorems("ilist", ilist_type.generate_complete_lawful_beq())
            .build();

        // Verify the code structure before validation
        assert!(!lean_code.is_empty());
        assert!(lean_code.contains("list_all_eq_hd"));
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
    fn test_axiom_display_format() {
        // Create a simple axiom to test Display formatting
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

        let display_output = axiom.to_string();
        assert_eq!(
            display_output,
            "let[@axiom] list_emp_no_hd (l : ilist) (x : Int) = ((emp l))#==>((not ((hd l x))))"
        );
    }

    #[test]
    fn test_axiom_display_with_existential() {
        // Test formatting with existential parameters and complex boolean logic
        let axiom = Axiom {
            name: "tree_leaf_depth_0_disjoint".to_string(),
            params: vec![
                Parameter::universal("l", Type::Named("tree".to_string())),
                Parameter::existential("n", Type::Named("int".to_string())),
            ],
            body: Proposition::Or(
                Box::new(Proposition::And(
                    Box::new(Proposition::And(
                        Box::new(Proposition::Predicate(
                            "depth".to_string(),
                            vec![
                                Expression::Variable("l".into()),
                                Expression::Variable("n".into()),
                            ],
                        )),
                        Box::new(Proposition::Equality(
                            Box::new(Proposition::Expr(Expression::Variable("n".into()))),
                            Box::new(Proposition::Expr(Expression::Literal(Literal::Int(0)))),
                        )),
                    )),
                    Box::new(Proposition::Predicate(
                        "leaf".to_string(),
                        vec![Expression::Variable("l".into())],
                    )),
                )),
                Box::new(Proposition::And(
                    Box::new(Proposition::And(
                        Box::new(Proposition::Predicate(
                            "depth".to_string(),
                            vec![
                                Expression::Variable("l".into()),
                                Expression::Variable("n".into()),
                            ],
                        )),
                        Box::new(Proposition::Expr(Expression::BinaryOp(
                            Box::new(Expression::Variable("n".into())),
                            BinaryOp::Gt,
                            Box::new(Expression::Literal(Literal::Int(0))),
                        ))),
                    )),
                    Box::new(Proposition::Not(Box::new(Proposition::Predicate(
                        "leaf".to_string(),
                        vec![Expression::Variable("l".into())],
                    )))),
                )),
            ),
            proof: Some("grind".to_string()),
        };

        let display_output = axiom.to_string();
        assert_eq!(
            display_output,
            "let[@axiom] tree_leaf_depth_0_disjoint (l : tree) ((n [@exists]) : int) = ((((depth l n) && (n)#==(0)) && (leaf l)) || (((depth l n) && (n > 0)) && (not ((leaf l)))))"
        );
    }
}

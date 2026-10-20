use std::fmt;

use crate::{
    Literal, VarName,
    prog_ir::{BinaryOp, ConstructorName, Type},
};

/// Suffix for domain-specific axioms (e.g., non-negativity constraints)
pub(crate) const DOMAIN_AXIOM_SUFFIX: &str = "_geq_0";

/// Standard result parameter name for axioms (e.g., "res" in `len l res`)
pub(crate) const RESULT_PARAM: &str = "res";

/// A specification axiom, rendered as a `let[@axiom]` declaration by its `Display` impl
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

/// A parameter in an axiom with its quantification mode
#[derive(Debug, Clone, PartialEq)]
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

    /// A predicate application: is_nil l, hd l x, tl l l1, len l res
    Predicate(String, Vec<Expression>),

    /// Implication: p #==> q
    Implication(Box<Proposition>, Box<Proposition>),

    /// Equality: p #== q
    Equality(Box<Proposition>, Box<Proposition>),

    /// Conjunction: p && q && ...
    And(Vec<Proposition>),

    /// Disjunction: p || q
    Or(Box<Proposition>, Box<Proposition>),

    /// Negation: not p
    Not(Box<Proposition>),

    /// Bi-implication: iff p q
    Iff(Box<Proposition>, Box<Proposition>),

    /// Existential quantification: ∃ x : type, body
    Existential(Parameter, Box<Proposition>),
}

/// Expressions that appear as arguments to predicates
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Expression {
    /// Variable reference
    Variable(VarName),

    /// Literal values
    Literal(Literal),

    /// Binary arithmetic/comparison operators: >=, >, ==, <, <=, +, -, etc.
    BinaryOp(Box<Expression>, BinaryOp, Box<Expression>),

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

    /// Field accessor: head l, tail l, field_0 t, etc.
    /// First arg is the accessor name (e.g., "head", "tail")
    /// Second arg is the expression to access (e.g., a list variable)
    FieldAccess(String, Box<Expression>),
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

impl From<String> for Expression {
    fn from(s: String) -> Self {
        Expression::Variable(VarName::new(&s))
    }
}

impl From<&str> for Expression {
    fn from(s: &str) -> Self {
        Expression::Variable(VarName::new(s))
    }
}

impl From<i32> for Expression {
    fn from(value: i32) -> Self {
        Expression::Literal(Literal::Int(value))
    }
}

impl From<i64> for Expression {
    fn from(value: i64) -> Self {
        Expression::Literal(Literal::Int(value as i32))
    }
}

impl Expression {
    /// Check if an expression is a boolean-valued comparison or logical operation
    pub(crate) fn is_boolean_expr(&self) -> bool {
        matches!(
            self,
            Expression::BinaryOp(_, op, _) if matches!(op, BinaryOp::Lt | BinaryOp::Lte | BinaryOp::Gt | BinaryOp::Gte | BinaryOp::Eq | BinaryOp::Neq | BinaryOp::And | BinaryOp::Or)
        )
    }

    /// Fold over the expression tree, visiting all sub-expressions
    pub(crate) fn fold<T, F>(&self, init: T, f: &F) -> T
    where
        F: Fn(T, &Expression) -> T,
    {
        let t = match self {
            Expression::BinaryOp(left, _, right) => {
                let t = left.fold(init, f);
                right.fold(t, f)
            }
            Expression::Constructor(_, args) => args.iter().fold(init, |t, arg| arg.fold(t, f)),
            Expression::Tuple(args) => args.iter().fold(init, |t, arg| arg.fold(t, f)),
            Expression::IfThenElse {
                condition,
                then_branch,
                else_branch,
            } => {
                let t = condition.fold(init, f);
                let t = then_branch.fold(t, f);
                else_branch.fold(t, f)
            }
            Expression::Not(e) => e.fold(init, f),
            Expression::FieldAccess(_, e) => e.fold(init, f),
            _ => init,
        };
        f(t, self)
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

impl Axiom {
    /// Check if this is a domain-specific axiom (e.g., non-negativity constraint)
    pub fn is_domain_specific(&self) -> bool {
        self.name.ends_with(DOMAIN_AXIOM_SUFFIX)
    }

    /// Create a new axiom with the given name, parameters, and body.
    pub(crate) fn new(name: String, params: Vec<Parameter>, body: Proposition) -> Self {
        Axiom { name, params, body }
    }

    /// Create an axiom with parameters built from a let binding and an explicit result type.
    pub(crate) fn from_let_binding(
        name: String,
        binding: &crate::prog_ir::LetBinding,
        return_type: crate::prog_ir::Type,
        uni_params: &[Parameter],
        result_param: &str,
        body: Proposition,
    ) -> Self {
        let mut params = Parameter::from_vars(&binding.params);
        params.extend_from_slice(uni_params);
        params.push(Parameter::universal(result_param, return_type));
        Self::new(name, params, body)
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

    pub(crate) fn as_expr(&self) -> &Expression {
        match self {
            Proposition::Expr(expression) => expression,
            _ => panic!("Expected Proposition::Expr, got {:?}", self),
        }
    }

    /// Create a conjunction from propositions if there are multiple, otherwise return the single proposition.
    /// Panics on empty input: an empty `And` is vacuously true and would make any antecedent that uses it
    /// admit every result, breaking determinism downstream.
    pub(crate) fn optional_conjunction(propositions: Vec<Proposition>) -> Proposition {
        match propositions.len() {
            0 => panic!("Proposition::optional_conjunction called with no propositions"),
            1 => propositions.into_iter().next().unwrap(),
            _ => Proposition::And(propositions),
        }
    }

    /// Map a transformation function over a proposition, recursing post-order through the tree.
    /// Post-order: children are recursively transformed before applying `f`.
    pub(crate) fn map<F>(self, f: &F) -> Proposition
    where
        F: Fn(Proposition) -> Proposition,
    {
        let recursed = match self {
            Proposition::Implication(p, q) => {
                Proposition::Implication(Box::new((*p).map(f)), Box::new((*q).map(f)))
            }
            Proposition::And(props) => {
                Proposition::And(props.into_iter().map(|p| p.map(f)).collect())
            }
            Proposition::Or(p, q) => Proposition::Or(Box::new((*p).map(f)), Box::new((*q).map(f))),
            Proposition::Not(p) => Proposition::Not(Box::new((*p).map(f))),
            Proposition::Iff(p, q) => {
                Proposition::Iff(Box::new((*p).map(f)), Box::new((*q).map(f)))
            }
            Proposition::Existential(param, body) => {
                Proposition::Existential(param, Box::new((*body).map(f)))
            }
            other => other,
        };

        f(recursed)
    }

    /// Fold a proposition into an accumulated value, recursing post-order through the tree.
    /// Post-order: children are folded before applying `f`.
    pub(crate) fn fold<T, F>(&self, init: T, f: &F) -> T
    where
        F: Fn(T, &Proposition) -> T,
    {
        let t = match self {
            Proposition::Implication(p, q) => {
                let t = p.fold(init, f);
                q.fold(t, f)
            }
            Proposition::And(props) => props.iter().fold(init, |t, p| p.fold(t, f)),
            Proposition::Or(p, q) => {
                let t = p.fold(init, f);
                q.fold(t, f)
            }
            Proposition::Not(p) => p.fold(init, f),
            Proposition::Iff(p, q) => {
                let t = p.fold(init, f);
                q.fold(t, f)
            }
            Proposition::Existential(_, body) => body.fold(init, f),
            _ => init,
        };
        f(t, self)
    }

    /// Collect all variable references that appear in this proposition.
    /// Includes variables in expressions, predicate arguments, and existential binders.
    pub(crate) fn collect_variables(&self) -> std::collections::HashSet<VarName> {
        self.fold(
            std::collections::HashSet::new(),
            &|mut vars, prop| match prop {
                Proposition::Expr(expr) => {
                    vars = expr.fold(vars, &|mut vars, e| {
                        if let Expression::Variable(v) = e {
                            vars.insert(v.clone());
                        }
                        vars
                    });
                    vars
                }
                Proposition::Predicate(_, args) => {
                    for arg in args {
                        vars = arg.fold(vars, &|mut vars, e| {
                            if let Expression::Variable(v) = e {
                                vars.insert(v.clone());
                            }
                            vars
                        });
                    }
                    vars
                }
                Proposition::Existential(param, _) => {
                    vars.insert(param.name.clone());
                    vars
                }
                _ => vars,
            },
        )
    }

    /// Collect all existentially-bound variables in this proposition, preserving duplicates.
    /// Returns a vector of all existential variables (including duplicates).
    /// Use `.into_iter().collect::<HashSet<_>>()` if deduplication is needed.
    pub(crate) fn collect_existential_variables(&self) -> Vec<VarName> {
        self.fold(Vec::new(), &|mut vars, prop| {
            if let Proposition::Existential(param, _) = prop {
                vars.push(param.name.clone());
            }
            vars
        })
    }

    /// Build a relation predicate from function inputs and a result variable
    ///
    /// For example, with function `len(l)` and result param `res`:
    /// Produces `Predicate("len", [Variable("l"), Variable("res")])`
    pub(crate) fn build_relation_predicate(
        binding: &crate::prog_ir::LetBinding,
        result_param: &str,
    ) -> Proposition {
        let mut args = binding
            .params
            .iter()
            .map(|p| Expression::Variable(p.0.clone()))
            .collect::<Vec<_>>();
        args.push(Expression::Variable(VarName(result_param.to_string())));
        Proposition::Predicate(binding.name.0.clone(), args)
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
            Proposition::And(props) => {
                if props.len() == 1 {
                    // Single element: just display it without extra wrapping
                    write!(f, "{}", props[0])
                } else {
                    let formatted = props
                        .iter()
                        .map(|p| format!("{}", p))
                        .collect::<Vec<_>>()
                        .join(" && ");
                    write!(f, "({})", formatted)
                }
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
            Proposition::Existential(param, body) => {
                write!(
                    f,
                    "fun (({} [@exists]) : {}) -> {}",
                    param.name, param.typ, body
                )
            }
        }
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
            Expression::FieldAccess(accessor, expr) => {
                write!(f, "({} {})", accessor, expr)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_axiom_display_format() {
        // Create a simple axiom to test Display formatting
        let axiom = Axiom {
            name: "list_is_nil_no_hd".to_string(),
            params: vec![
                Parameter::universal("l", Type::Named("ilist".to_string())),
                Parameter::universal("x", Type::Named("Int".to_string())),
            ],
            body: Proposition::Implication(
                Box::new(Proposition::Predicate(
                    "is_nil".to_string(),
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
        };

        let display_output = axiom.to_string();
        assert_eq!(
            display_output,
            "let[@axiom] list_is_nil_no_hd (l : ilist) (x : Int) = ((is_nil l))#==>((not ((hd l x))))"
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
                Box::new(Proposition::And(vec![
                    Proposition::Predicate(
                        "depth".to_string(),
                        vec![
                            Expression::Variable("l".into()),
                            Expression::Variable("n".into()),
                        ],
                    ),
                    Proposition::Equality(
                        Box::new(Proposition::Expr(Expression::Variable("n".into()))),
                        Box::new(Proposition::Expr(Expression::Literal(Literal::Int(0)))),
                    ),
                    Proposition::Predicate(
                        "leaf".to_string(),
                        vec![Expression::Variable("l".into())],
                    ),
                ])),
                Box::new(Proposition::And(vec![
                    Proposition::Predicate(
                        "depth".to_string(),
                        vec![
                            Expression::Variable("l".into()),
                            Expression::Variable("n".into()),
                        ],
                    ),
                    Proposition::Expr(Expression::BinaryOp(
                        Box::new(Expression::Variable("n".into())),
                        BinaryOp::Gt,
                        Box::new(Expression::Literal(Literal::Int(0))),
                    )),
                    Proposition::Not(Box::new(Proposition::Predicate(
                        "leaf".to_string(),
                        vec![Expression::Variable("l".into())],
                    ))),
                ])),
            ),
        };

        let display_output = axiom.to_string();
        assert_eq!(
            display_output,
            "let[@axiom] tree_leaf_depth_0_disjoint (l : tree) ((n [@exists]) : int) = (((depth l n) && (n)#==(0) && (leaf l)) || ((depth l n) && (n > 0) && (not ((leaf l)))))"
        );
    }

    #[test]
    fn test_build_relation_predicate_includes_result_param() {
        use crate::prog_ir::Type;

        let binding = crate::prog_ir::LetBinding {
            name: crate::VarName("len".into()),
            params: vec![
                (crate::VarName("l".into()), Type::Int),
                (crate::VarName("x".into()), Type::Bool),
            ],
            body: crate::prog_ir::Expression::Literal(crate::Literal::Int(0)),
            return_type: Some(Type::Int),
            is_recursive: false,
        };

        let pred = Proposition::build_relation_predicate(&binding, "res");

        match pred {
            Proposition::Predicate(name, args) => {
                assert_eq!(name, "len", "Predicate name should match function name");
                assert_eq!(
                    args.len(),
                    3,
                    "Should have input params (l, x) plus result param"
                );
                // Verify the last argument is the result variable
                if let Expression::Variable(res_name) = &args[2] {
                    assert_eq!(
                        res_name.0, "res",
                        "Last argument should be result parameter"
                    );
                } else {
                    panic!("Expected result parameter to be a variable");
                }
            }
            _ => panic!("Expected predicate, got different proposition type"),
        }
    }
}

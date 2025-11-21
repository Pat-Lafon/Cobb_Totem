use std::fmt;
use std::str::FromStr;

pub mod ocamlparser;
pub mod lean_backend;

/// Validates that a name is a valid constructor identifier.
///
/// A valid constructor name must:
/// - Start with an uppercase letter
/// - Contain only alphanumeric characters or underscores
fn is_valid_constructor_name(name: &str) -> bool {
    name.chars().next().map_or(false, |c| c.is_uppercase())
        && name.chars().all(|c| c.is_alphanumeric() || c == '_')
}

#[derive(Debug, Clone, PartialEq)]
pub enum ConstructorName {
    Simple(String),
    Qualified { module: String, name: String },
}

impl FromStr for ConstructorName {
    type Err = String;

    fn from_str(text: &str) -> Result<Self, Self::Err> {
        let parts: Vec<&str> = text.split('.').collect();

        match parts.as_slice() {
            [name] => {
                // Simple constructor
                if is_valid_constructor_name(name) {
                    Ok(ConstructorName::Simple(name.to_string()))
                } else {
                    Err(format!("Invalid simple constructor name: '{}'", text))
                }
            }
            [module, name] => {
                // Qualified constructor
                if is_valid_constructor_name(module) && is_valid_constructor_name(name) {
                    Ok(ConstructorName::Qualified {
                        module: module.to_string(),
                        name: name.to_string(),
                    })
                } else {
                    Err(format!("Invalid qualified constructor name: '{}'", text))
                }
            }
            _ => Err(format!(
                "Constructor name can have at most one dot separator, got '{}'",
                text
            )),
        }
    }
}

impl fmt::Display for ConstructorName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ConstructorName::Simple(name) => write!(f, "{}", name),
            ConstructorName::Qualified { module, name } => write!(f, "{}.{}", module, name),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Type {
    Int,
    Bool,
    Unit,
    Named(String),
    Function(Box<Type>, Box<Type>),
}

impl FromStr for Type {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let s = s.trim();

        // Look for the rightmost arrow to handle right-associativity
        if let Some(arrow_pos) = s.rfind("->") {
            let left = s[..arrow_pos].trim();
            let right = s[arrow_pos + 2..].trim();

            let left_type = left.parse()?;
            let right_type = right.parse()?;

            Ok(Type::Function(Box::new(left_type), Box::new(right_type)))
        } else {
            match s {
                "int" => Ok(Type::Int),
                "bool" => Ok(Type::Bool),
                "unit" => Ok(Type::Unit),
                name if name.is_ascii() => Ok(Type::Named(name.to_string())),
                name => Err(format!("{name} is not a valid type")),
            }
        }
    }
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Type::Int => write!(f, "int"),
            Type::Bool => write!(f, "bool"),
            Type::Unit => write!(f, "unit"),
            Type::Named(name) => write!(f, "{}", name),
            Type::Function(from, to) => write!(f, "{} -> {}", from, to),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypeDecl {
    pub name: String,
    pub variants: Vec<Variant>,
}

impl fmt::Display for TypeDecl {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "type {} = {}",
            self.name,
            self.variants
                .iter()
                .map(|v| v.to_string())
                .collect::<Vec<_>>()
                .join(" | ")
        )
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Variant {
    pub name: String,
    pub fields: Vec<Type>,
}

impl fmt::Display for Variant {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.fields.is_empty() {
            write!(f, "{}", self.name)
        } else {
            write!(
                f,
                "{} of {}",
                self.name,
                self.fields
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join(" * ")
            )
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Literal {
    Int(i32),
    Bool(bool),
}

impl fmt::Display for Literal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Literal::Int(n) => write!(f, "{}", n),
            Literal::Bool(b) => write!(f, "{}", b),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum BinaryOp {
    Add,
    Sub,
    Mul,
    Div,
    Eq,
    Neq,
    Lt,
    Lte,
    Gt,
    Gte,
    And,
    Or,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum UnaryOp {
    Neg,
    Not,
}

impl FromStr for UnaryOp {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let s = s.trim();

        match s {
            "-" => Ok(UnaryOp::Neg),
            "!" => Ok(UnaryOp::Not),
            op => Err(format!("Unknown unary operator: {}", op)),
        }
    }
}

impl fmt::Display for UnaryOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            UnaryOp::Neg => write!(f, "-"),
            UnaryOp::Not => write!(f, "!"),
        }
    }
}

impl FromStr for BinaryOp {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let s = s.trim();

        match s {
            "+" => Ok(BinaryOp::Add),
            "-" => Ok(BinaryOp::Sub),
            "*" => Ok(BinaryOp::Mul),
            "/" => Ok(BinaryOp::Div),
            "=" => Ok(BinaryOp::Eq),
            "==" => Err("Use '=' for equality, not '=='".to_string()),
            "<>" => Ok(BinaryOp::Neq),
            "<" => Ok(BinaryOp::Lt),
            "<=" => Ok(BinaryOp::Lte),
            ">" => Ok(BinaryOp::Gt),
            ">=" => Ok(BinaryOp::Gte),
            "&&" => Ok(BinaryOp::And),
            "||" => Ok(BinaryOp::Or),
            op => Err(format!("Unknown binary operator: {}", op)),
        }
    }
}

impl fmt::Display for BinaryOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BinaryOp::Add => write!(f, "+"),
            BinaryOp::Sub => write!(f, "-"),
            BinaryOp::Mul => write!(f, "*"),
            BinaryOp::Div => write!(f, "/"),
            BinaryOp::Eq => write!(f, "="),
            BinaryOp::Neq => write!(f, "<>"),
            BinaryOp::Lt => write!(f, "<"),
            BinaryOp::Lte => write!(f, "<="),
            BinaryOp::Gt => write!(f, ">"),
            BinaryOp::Gte => write!(f, ">="),
            BinaryOp::And => write!(f, "&&"),
            BinaryOp::Or => write!(f, "||"),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Pattern {
    Variable(String),
    Constructor(ConstructorName, Vec<Pattern>),
    Literal(Literal),
    Wildcard,
}

impl fmt::Display for Pattern {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Pattern::Variable(name) => write!(f, "{}", name),
            Pattern::Constructor(name, patterns) => {
                if patterns.is_empty() {
                    write!(f, "{}", name)
                } else {
                    write!(
                        f,
                        "{}({})",
                        name,
                        patterns
                            .iter()
                            .map(ToString::to_string)
                            .collect::<Vec<_>>()
                            .join(", ")
                    )
                }
            }
            Pattern::Literal(lit) => write!(f, "{}", lit),
            Pattern::Wildcard => write!(f, "_"),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Expression {
    Variable(String),
    Constructor(ConstructorName, Vec<Expression>),
    Literal(Literal),
    UnaryOp(UnaryOp, Box<Expression>),
    BinaryOp(Box<Expression>, BinaryOp, Box<Expression>),
    Application(Box<Expression>, Vec<Expression>),
    Match(Box<Expression>, Vec<(Pattern, Expression)>),
    Tuple(Vec<Expression>),
}

impl fmt::Display for Expression {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Expression::Variable(name) => write!(f, "{}", name),
            Expression::Constructor(name, args) => {
                if args.is_empty() {
                    write!(f, "{}", name)
                } else {
                    write!(
                        f,
                        "{}({})",
                        name,
                        args.iter()
                            .map(ToString::to_string)
                            .collect::<Vec<_>>()
                            .join(", ")
                    )
                }
            }
            Expression::Literal(lit) => write!(f, "{}", lit),
            Expression::UnaryOp(op, expr) => {
                let op_str = match op {
                    UnaryOp::Neg => "-",
                    UnaryOp::Not => "!",
                };
                write!(f, "({}{})", op_str, expr)
            }
            Expression::BinaryOp(left, op, right) => {
                write!(f, "({} {} {})", left, op, right)
            }
            Expression::Application(func, args) => {
                write!(f, "({}", func)?;
                for arg in args {
                    write!(f, " {}", arg)?;
                }
                write!(f, ")")
            }
            Expression::Match(scrutinee, cases) => {
                write!(f, "match {} with", scrutinee)?;
                for (pattern, expr) in cases {
                    write!(f, "\n  | {} -> {}", pattern, expr)?;
                }
                Ok(())
            }
            Expression::Tuple(elements) => {
                if elements.len() == 1 {
                    write!(f, "({},)", elements[0])
                } else {
                    write!(
                        f,
                        "({})",
                        elements
                            .iter()
                            .map(ToString::to_string)
                            .collect::<Vec<_>>()
                            .join(", ")
                    )
                }
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct LetBinding {
    pub name: String,
    pub attributes: Vec<String>,
    pub is_recursive: bool,
    pub params: Vec<(String, Type)>,
    pub return_type: Option<Type>,
    pub body: Expression,
}

impl fmt::Display for LetBinding {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "let {}", if self.is_recursive { "rec " } else { "" })?;
        write!(f, "{}", self.name)?;
        for (param, ty) in &self.params {
            write!(f, " ({} : {})", param, ty)?;
        }
        if let Some(ty) = &self.return_type {
            write!(f, ": {}", ty)?;
        }
        write!(f, " = {}", self.body)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum AstNode {
    TypeDeclaration(TypeDecl),
    LetBinding(LetBinding),
}

impl fmt::Display for AstNode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            AstNode::TypeDeclaration(td) => write!(f, "{}", td),
            AstNode::LetBinding(lb) => write!(f, "{}", lb),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{ConstructorName, Expression, Literal, Pattern, Type, TypeDecl, Variant};

    #[test]
    fn test_variant_display() {
        let nil = Variant {
            name: "Nil".to_string(),
            fields: vec![],
        };
        assert_eq!(nil.to_string(), "Nil");

        let cons = Variant {
            name: "Cons".to_string(),
            fields: vec![Type::Int, Type::Named("int list".to_string())],
        };
        assert_eq!(cons.to_string(), "Cons of int * int list");
    }

    #[test]
    fn test_type_decl_display() {
        let ilist = TypeDecl {
            name: "ilist".to_string(),
            variants: vec![
                Variant {
                    name: "Nil".to_string(),
                    fields: vec![],
                },
                Variant {
                    name: "Cons".to_string(),
                    fields: vec![Type::Int, Type::Named("int list".to_string())],
                },
            ],
        };
        assert_eq!(
            ilist.to_string(),
            "type ilist = Nil | Cons of int * int list"
        );
    }

    #[test]
    fn test_expression_display() {
        let int_lit = Expression::Literal(Literal::Int(42));
        assert_eq!(int_lit.to_string(), "42");

        let bool_lit = Expression::Literal(Literal::Bool(true));
        assert_eq!(bool_lit.to_string(), "true");

        let var = Expression::Variable("x".to_string());
        assert_eq!(var.to_string(), "x");
    }

    #[test]
    fn test_pattern_display() {
        let wildcard = Pattern::Wildcard;
        assert_eq!(wildcard.to_string(), "_");

        let var = Pattern::Variable("x".to_string());
        assert_eq!(var.to_string(), "x");

        let int_lit = Pattern::Literal(Literal::Int(0));
        assert_eq!(int_lit.to_string(), "0");

        let constructor = Pattern::Constructor(
            ConstructorName::Simple("Cons".to_string()),
            vec![Pattern::Wildcard, Pattern::Variable("rest".to_string())],
        );
        assert_eq!(constructor.to_string(), "Cons(_, rest)");
    }
}

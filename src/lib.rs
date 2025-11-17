use std::fmt;
use std::str::FromStr;

pub mod ocamlparser;

#[derive(Debug, Clone)]
pub enum Type {
    Int,
    Bool,
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
            Type::Named(name) => write!(f, "{}", name),
            Type::Function(from, to) => write!(f, "{} -> {}", from, to),
        }
    }
}

#[derive(Debug, Clone)]
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

#[derive(Debug, Clone)]
pub struct Variant {
    pub name: String,
    pub fields: Vec<Type>,
}

impl fmt::Display for Variant {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name)?;
        if !self.fields.is_empty() {
            write!(f, " of ")?;
            for (i, field) in self.fields.iter().enumerate() {
                if i > 0 {
                    write!(f, " * ")?;
                }
                write!(f, "{}", field)?;
            }
        }
        Ok(())
    }
}

#[derive(Debug, Clone)]
pub struct PatternCase {
    pub pattern: String,
    pub body: String,
}

#[derive(Debug, Clone)]
pub enum LetBindingBody {
    Expression(String),
    PatternMatch(String, Vec<PatternCase>),
}

#[derive(Debug, Clone)]
pub struct LetBinding {
    pub name: String,
    pub attributes: Vec<String>,
    pub is_recursive: bool,
    pub params: Vec<(String, Option<Type>)>,
    pub return_type: Option<Type>,
    pub body: LetBindingBody,
}

impl fmt::Display for LetBinding {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "let {} ", if self.is_recursive { "rec " } else { "" })?;
        write!(f, "{}", self.name)?;
        for (param, ty) in &self.params {
            write!(f, " {}", param)?;
            if let Some(ty) = ty {
                write!(f, ": {}", ty)?;
            }
        }
        if let Some(ty) = &self.return_type {
            write!(f, ": {}", ty)?;
        }
        write!(f, " = ")?;
        match &self.body {
            LetBindingBody::Expression(expr) => write!(f, "{}", expr),
            LetBindingBody::PatternMatch(scrutinee, cases) => {
                write!(f, "match {} with", scrutinee)?;
                for case in cases {
                    write!(f, "\n  | {} -> {}", case.pattern, case.body)?;
                }
                Ok(())
            }
        }
    }
}

#[derive(Debug, Clone)]
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
    use crate::{Type, TypeDecl, Variant};

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
}

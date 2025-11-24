/// Lean backend for outputting AST to Lean 4 syntax
///
use crate::{
    ToLean,
    prog_ir::{AstNode, BinaryOp, Expression, LetBinding, UnaryOp},
};

// TypeDecl, Variant, and Type ToLean implementations are in lib.rs

impl ToLean for LetBinding {
    fn to_lean(&self) -> String {
        let def_keyword = "def";
        let params_str = self
            .params
            .iter()
            .map(|(name, ty)| format!("({} : {})", name, ty.to_lean()))
            .collect::<Vec<_>>()
            .join(" ");

        let return_type_str = if let Some(ty) = &self.return_type {
            format!(" : {}", ty.to_lean())
        } else {
            String::new()
        };

        let attrs_str = if self.attributes.is_empty() {
            String::new()
        } else {
            format!("@[{}]\n", self.attributes.join(", "))
        };

        format!(
            "{}{} {} {}{} := {}",
            attrs_str,
            def_keyword,
            self.name,
            params_str,
            return_type_str,
            self.body.to_lean()
        )
    }
}

impl ToLean for Expression {
    fn to_lean(&self) -> String {
        match self {
            Expression::Variable(name) => name.clone(),
            Expression::Constructor(name, args) => {
                if args.is_empty() {
                    name.to_string()
                } else {
                    format!(
                        "{}({})",
                        name,
                        args.iter()
                            .map(|e| e.to_lean())
                            .collect::<Vec<_>>()
                            .join(", ")
                    )
                }
            }
            Expression::Literal(lit) => lit.to_lean(),
            Expression::UnaryOp(op, expr) => {
                let op_str = match op {
                    UnaryOp::Neg => "-",
                    UnaryOp::Not => "!",
                };
                format!("({}{})", op_str, expr.to_lean())
            }
            Expression::BinaryOp(left, op, right) => {
                let op_str = match op {
                    BinaryOp::Add => "+",
                    BinaryOp::Sub => "-",
                    BinaryOp::Mul => "*",
                    BinaryOp::Div => "/",
                    BinaryOp::Eq => "==",
                    BinaryOp::Neq => "!=",
                    BinaryOp::Lt => "<",
                    BinaryOp::Lte => "<=",
                    BinaryOp::Gt => ">",
                    BinaryOp::Gte => ">=",
                    BinaryOp::And => "&&",
                    BinaryOp::Or => "||",
                };
                format!("({} {} {})", left.to_lean(), op_str, right.to_lean())
            }
            Expression::Application(func, args) => {
                format!(
                    "{} {}",
                    func.to_lean(),
                    args.iter()
                        .map(|e| e.to_lean())
                        .collect::<Vec<_>>()
                        .join(" ")
                )
            }
            Expression::Match(scrutinee, cases) => {
                let cases_str = cases
                    .iter()
                    .map(|(pattern, expr)| {
                        format!("  | {} => {}", pattern.to_lean(), expr.to_lean())
                    })
                    .collect::<Vec<_>>()
                    .join("\n");

                format!("match {} with\n{}", scrutinee.to_lean(), cases_str)
            }
            Expression::Tuple(elements) => {
                if elements.len() == 1 {
                    format!("({})", elements[0].to_lean())
                } else {
                    format!(
                        "({})",
                        elements
                            .iter()
                            .map(|e| e.to_lean())
                            .collect::<Vec<_>>()
                            .join(", ")
                    )
                }
            }
        }
    }
}

// Literal and Pattern ToLean implementations are in lib.rs

impl ToLean for AstNode {
    fn to_lean(&self) -> String {
        match self {
            AstNode::TypeDeclaration(td) => td.to_lean(),
            AstNode::LetBinding(lb) => lb.to_lean(),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        lean_validation::validate_lean_code,
        prog_ir::{ConstructorName, Literal, Pattern, Type, TypeDecl, Variant},
    };

    use super::*;

    #[test]
    fn test_simple_bool_type() {
        let bool_type = TypeDecl {
            name: "MyBool".to_string(),
            variants: vec![
                Variant {
                    name: "True".to_string(),
                    fields: vec![],
                },
                Variant {
                    name: "False".to_string(),
                    fields: vec![],
                },
            ],
            attributes: vec![],
        };

        let lean_output = bool_type.to_lean();
        assert_eq!(lean_output, "inductive MyBool where\n  | True\n  | False\nderiving BEq, Repr");
        assert!(
            validate_lean_code(&lean_output).is_ok(),
            "Generated Lean code failed validation"
        );
    }

    #[test]
    fn test_list_type() {
        let list_type = TypeDecl {
            name: "List".to_string(),
            variants: vec![
                Variant {
                    name: "Nil".to_string(),
                    fields: vec![],
                },
                Variant {
                    name: "Cons".to_string(),
                    fields: vec![Type::Int, Type::Named("List".to_string())],
                },
            ],
            attributes: vec![],
        };

        let lean_output = list_type.to_lean();
        assert_eq!(
            lean_output,
            "inductive List where\n  | Nil\n  | Cons : Int → List → List\nderiving BEq, Repr"
        );
        assert!(
            validate_lean_code(&lean_output).is_ok(),
            "Generated Lean code failed validation"
        );
    }

    #[test]
    fn test_ilist_type() {
        let ilist_type = TypeDecl {
            name: "ilist".to_string(),
            variants: vec![
                Variant {
                    name: "Nil".to_string(),
                    fields: vec![],
                },
                Variant {
                    name: "Cons".to_string(),
                    fields: vec![Type::Int, Type::Named("ilist".to_string())],
                },
            ],
            attributes: vec![],
        };

        let lean_code = ilist_type.to_lean();
        assert_eq!(
            lean_code,
            "inductive ilist where\n  | Nil\n  | Cons : Int → ilist → ilist\nderiving BEq, Repr"
        );
        assert!(
            validate_lean_code(&lean_code).is_ok(),
            "Generated Lean code failed validation"
        );
    }

    #[test]
    fn test_len_function() {
        let ilist_type = TypeDecl {
            name: "ilist".to_string(),
            variants: vec![
                Variant {
                    name: "Nil".to_string(),
                    fields: vec![],
                },
                Variant {
                    name: "Cons".to_string(),
                    fields: vec![Type::Int, Type::Named("ilist".to_string())],
                },
            ],
            attributes: vec![],
        };

        let len_function = LetBinding {
            name: "len".to_string(),
            is_recursive: true,
            params: vec![
                ("l".to_string(), Type::Named("ilist".to_string())),
                ("n".to_string(), Type::Int),
            ],
            return_type: Some(Type::Bool),
            body: Expression::Match(
                Box::new(Expression::Variable("l".to_string())),
                vec![
                    (
                        Pattern::Constructor(ConstructorName::Simple("Nil".to_string()), vec![]),
                        Expression::BinaryOp(
                            Box::new(Expression::Variable("n".to_string())),
                            BinaryOp::Eq,
                            Box::new(Expression::Literal(Literal::Int(0))),
                        ),
                    ),
                    (
                        Pattern::Constructor(
                            ConstructorName::Simple("Cons".to_string()),
                            vec![Pattern::Wildcard, Pattern::Variable("rest".to_string())],
                        ),
                        Expression::Application(
                            Box::new(Expression::Variable("len".to_string())),
                            vec![
                                Expression::Variable("rest".to_string()),
                                Expression::BinaryOp(
                                    Box::new(Expression::Variable("n".to_string())),
                                    BinaryOp::Sub,
                                    Box::new(Expression::Literal(Literal::Int(1))),
                                ),
                            ],
                        ),
                    ),
                ],
            ),
            attributes: Vec::new(),
        };

        let lean_code = format!("{}\n\n{}", ilist_type.to_lean(), len_function.to_lean());
        assert_eq!(
            lean_code,
            "inductive ilist where\n  | Nil\n  | Cons : Int → ilist → ilist\nderiving BEq, Repr\n\ndef len (l : ilist) (n : Int) : Bool := match l with\n  | .Nil => (n == 0)\n  | .Cons _ rest => len rest (n - 1)"
        );
        validate_lean_code(&lean_code).unwrap();
    }

    #[test]
    fn test_function_with_one_attribute() {
        let func = LetBinding {
            name: "foo".to_string(),
            is_recursive: false,
            params: vec![("x".to_string(), Type::Int)],
            return_type: Some(Type::Int),
            body: Expression::Variable("x".to_string()),
            attributes: vec!["simp".to_string()],
        };

        let lean_code = func.to_lean();
        assert_eq!(lean_code, "@[simp]\ndef foo (x : Int) : Int := x");
        validate_lean_code(&lean_code).unwrap();
    }

    #[test]
    fn test_function_with_two_attributes() {
        let func = LetBinding {
            name: "bar".to_string(),
            is_recursive: false,
            params: vec![("y".to_string(), Type::Bool)],
            return_type: Some(Type::Bool),
            body: Expression::Variable("y".to_string()),
            attributes: vec!["simp".to_string(), "grind".to_string()],
        };

        let lean_code = func.to_lean();
        assert!(lean_code.contains("@[simp, grind]"), "Expected attribute annotation @[simp, grind] in output, got: {}", lean_code);
        assert!(lean_code.starts_with("@[simp, grind]"), "Attributes should be at the start, got: {}", lean_code);
        validate_lean_code(&lean_code).unwrap();
    }
}

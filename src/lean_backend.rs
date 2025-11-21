/// Lean backend for outputting AST to Lean 4 syntax
///
use crate::{
    AstNode, BinaryOp, Expression, LetBinding, Literal, Pattern, Type, TypeDecl, UnaryOp, Variant,
};

/// Trait for converting AST nodes to Lean syntax
pub trait ToLean {
    fn to_lean(&self) -> String;
}

impl ToLean for TypeDecl {
    fn to_lean(&self) -> String {
        let variants_str = self
            .variants
            .iter()
            .map(|v| v.to_lean_with_type(&self.name))
            .collect::<Vec<_>>()
            .join("\n  | ");

        format!("inductive {} where\n  | {}", self.name, variants_str)
    }
}

impl Variant {
    /// Convert variant to Lean syntax with the return type
    pub fn to_lean_with_type(&self, return_type: &str) -> String {
        if self.fields.is_empty() {
            self.name.clone()
        } else {
            let mut field_strs = self.fields.iter().map(|f| f.to_lean()).collect::<Vec<_>>();
            field_strs.push(return_type.to_string());
            let type_sig = field_strs.join(" → ");
            format!("{} : {}", self.name, type_sig)
        }
    }
}

impl ToLean for Variant {
    fn to_lean(&self) -> String {
        self.name.clone()
    }
}

impl ToLean for Type {
    fn to_lean(&self) -> String {
        match self {
            Type::Int => "Int".to_string(),
            Type::Bool => "Bool".to_string(),
            Type::Unit => "Unit".to_string(),
            Type::Named(name) => name.clone(),
            Type::Function(from, to) => format!("{} → {}", from.to_lean(), to.to_lean()),
        }
    }
}

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

        format!(
            "{} {} {}{} := {}",
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

impl ToLean for Literal {
    fn to_lean(&self) -> String {
        match self {
            Literal::Int(n) => n.to_string(),
            Literal::Bool(b) => if *b { "true" } else { "false" }.to_string(),
        }
    }
}

impl ToLean for Pattern {
    fn to_lean(&self) -> String {
        match self {
            Pattern::Variable(name) => name.clone(),
            Pattern::Constructor(name, patterns) => {
                if patterns.is_empty() {
                    format!(".{}", name)
                } else {
                    format!(
                        ".{} {}",
                        name,
                        patterns
                            .iter()
                            .map(|p| p.to_lean())
                            .collect::<Vec<_>>()
                            .join(" ")
                    )
                }
            }
            Pattern::Literal(lit) => lit.to_lean(),
            Pattern::Wildcard => "_".to_string(),
        }
    }
}

impl ToLean for AstNode {
    fn to_lean(&self) -> String {
        match self {
            AstNode::TypeDeclaration(td) => td.to_lean(),
            AstNode::LetBinding(lb) => lb.to_lean(),
        }
    }
}

/// Validation module for Lean code
pub mod validation {
    use std::io::Write;
    use std::process::Command;

    /// Check if debug output is enabled via feature flag
    fn debug_enabled() -> bool {
        cfg!(feature = "debug")
    }

    /// Validate generated Lean code by running the lean type checker via stdin
    pub fn validate_lean_code(code: &str) -> Result<(), String> {
        // Wrap in namespace for recursive types and to isolate scope
        let wrapped_code = format!("namespace GeneratedCode\n\n{}\n\nend GeneratedCode\n", code);

        if debug_enabled() {
            debug_print_lean(code);
        }

        // Run lean with code piped via stdin
        let mut child = Command::new("lean")
            .arg("--stdin")
            .stdin(std::process::Stdio::piped())
            .stdout(std::process::Stdio::piped())
            .stderr(std::process::Stdio::piped())
            .spawn()
            .map_err(|e| format!("Failed to spawn lean: {}", e))?;

        // Write code to stdin
        if let Some(mut stdin) = child.stdin.take() {
            stdin
                .write_all(wrapped_code.as_bytes())
                .map_err(|e| format!("Failed to write to stdin: {}", e))?;
        }

        let output = child
            .wait_with_output()
            .map_err(|e| format!("Failed to run lean: {}", e))?;

        if output.status.success() {
            Ok(())
        } else {
            Err(String::from_utf8_lossy(&output.stdout).to_string())
        }
    }

    /// Print generated Lean code for debugging
    pub fn debug_print_lean(code: &str) {
        eprintln!("\n=== Generated Lean Code ===");
        for line in code.lines() {
            eprintln!("{}", line);
        }
        eprintln!("===========================\n");
    }
}

#[cfg(test)]
mod tests {
    use super::validation::*;
    use super::*;
    use crate::BinaryOp;
    use crate::ConstructorName;
    use crate::Expression;
    use crate::LetBinding;
    use crate::Literal;
    use crate::Pattern;
    use crate::{Type, TypeDecl, Variant};

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
        };

        let lean_output = bool_type.to_lean();
        assert_eq!(
            lean_output,
            "inductive MyBool where\n  | True\n  | False"
        );
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
        };

        let lean_output = list_type.to_lean();
        assert_eq!(
            lean_output,
            "inductive List where\n  | Nil\n  | Cons : Int → List → List"
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
        };

        let lean_code = ilist_type.to_lean();
        assert_eq!(
            lean_code,
            "inductive ilist where\n  | Nil\n  | Cons : Int → ilist → ilist"
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
            "inductive ilist where\n  | Nil\n  | Cons : Int → ilist → ilist\n\ndef len (l : ilist) (n : Int) : Bool := match l with\n  | .Nil => (n == 0)\n  | .Cons _ rest => len rest (n - 1)"
        );
        validate_lean_code(&lean_code).unwrap_or_else(|e| {
            panic!(
                "Lean code validation failed:\n{}\n\nError: {}",
                lean_code, e
            )
        });
    }
}

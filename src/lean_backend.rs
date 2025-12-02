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
            Expression::Variable(name) => name.to_string(),
            Expression::Constructor(name, args) => {
                if args.is_empty() {
                    format!(".{}", name)
                } else {
                    format!(
                        "(.{} {})",
                        name,
                        args.iter()
                            .map(|e| e.to_lean())
                            .collect::<Vec<_>>()
                            .join(" ")
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

/// Builder for constructing Lean code with automatic theorem attachment to types
#[derive(Default)]
pub struct LeanContextBuilder {
    nodes: Vec<AstNode>,
    axioms: Vec<crate::spec_ir::Axiom>,
    types_with_theorems: std::collections::HashMap<String, String>, // type_name -> theorems
}

impl LeanContextBuilder {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn with_nodes(mut self, nodes: Vec<AstNode>) -> Self {
        self.nodes = nodes;
        self
    }

    pub fn with_axioms(mut self, axioms: Vec<crate::spec_ir::Axiom>) -> Self {
        self.axioms = axioms;
        self
    }

    /// Attach BEq theorems to a specific type by name
    pub fn with_type_theorems(mut self, type_name: &str, theorems: String) -> Self {
        self.types_with_theorems
            .insert(type_name.to_string(), theorems);
        self
    }

    /// Build the final Lean code
    pub fn build(self) -> String {
        self.nodes
            .iter()
            .map(|node| match node {
                AstNode::TypeDeclaration(type_decl) => {
                    match self.types_with_theorems.get(&type_decl.name) {
                        Some(theorems) => {
                            format!("{}\n\n{}", type_decl.to_lean(), theorems)
                        }
                        None => type_decl.to_lean(),
                    }
                }
                other => other.to_lean(),
            })
            .chain(self.axioms.iter().map(|axiom| axiom.to_lean()))
            .collect::<Vec<_>>()
            .join("\n\n")
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        Literal, VarName,
        lean_validation::validate_lean_code,
        prog_ir::{ConstructorName, Pattern, Type, TypeDecl, Variant},
    };

    use super::*;
    use crate::spec_ir;

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
        assert_eq!(
            lean_output,
            "inductive MyBool where\n  | True\n  | False\nderiving BEq, Repr"
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
        let ilist_type = spec_ir::create_ilist_type();

        let lean_code = ilist_type.to_lean();
        assert_eq!(
            lean_code,
            "@[grind]\ninductive ilist where\n  | Nil\n  | Cons : Int → ilist → ilist\nderiving BEq, Repr"
        );
        assert!(
            validate_lean_code(&lean_code).is_ok(),
            "Generated Lean code failed validation"
        );
    }

    #[test]
    fn test_len_function() {
        let ilist_type = spec_ir::create_ilist_type();

        let len_function = LetBinding {
            name: VarName::new("len"),
            is_recursive: true,
            params: vec![
                (VarName::new("l"), Type::Named("ilist".to_string())),
                (VarName::new("n"), Type::Int),
            ],
            return_type: Some(Type::Bool),
            body: Expression::Match(
                Box::new(Expression::Variable("l".into())),
                vec![
                    (
                        Pattern::Constructor(ConstructorName::Simple("Nil".to_string()), vec![]),
                        Expression::BinaryOp(
                            Box::new(Expression::Variable("n".into())),
                            BinaryOp::Eq,
                            Box::new(Expression::Literal(Literal::Int(0))),
                        ),
                    ),
                    (
                        Pattern::Constructor(
                            ConstructorName::Simple("Cons".to_string()),
                            vec![Pattern::Wildcard, Pattern::Variable("rest".into())],
                        ),
                        Expression::Application(
                            Box::new(Expression::Variable("len".into())),
                            vec![
                                Expression::Variable("rest".into()),
                                Expression::BinaryOp(
                                    Box::new(Expression::Variable("n".into())),
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
            "@[grind]\ninductive ilist where\n  | Nil\n  | Cons : Int → ilist → ilist\nderiving BEq, Repr\n\ndef len (l : ilist) (n : Int) : Bool := match l with\n  | .Nil => (n == 0)\n  | .Cons _ rest => len rest (n - 1)"
        );
        validate_lean_code(&lean_code).unwrap();
    }

    #[test]
    fn test_function_with_one_attribute() {
        let func = LetBinding {
            name: VarName::new("foo"),
            is_recursive: false,
            params: vec![(VarName::new("x"), Type::Int)],
            return_type: Some(Type::Int),
            body: Expression::Variable("x".into()),
            attributes: vec!["simp".to_string()],
        };

        let lean_code = func.to_lean();
        assert_eq!(lean_code, "@[simp]\ndef foo (x : Int) : Int := x");
        validate_lean_code(&lean_code).unwrap();
    }

    #[test]
    fn test_function_with_two_attributes() {
        let func = LetBinding {
            name: VarName::new("bar"),
            is_recursive: false,
            params: vec![(VarName::new("y"), Type::Bool)],
            return_type: Some(Type::Bool),
            body: Expression::Variable("y".into()),
            attributes: vec!["simp".to_string(), "grind".to_string()],
        };

        let lean_code = func.to_lean();
        assert!(
            lean_code.contains("@[simp, grind]"),
            "Expected attribute annotation @[simp, grind] in output, got: {}",
            lean_code
        );
        assert!(
            lean_code.starts_with("@[simp, grind]"),
            "Attributes should be at the start, got: {}",
            lean_code
        );
        validate_lean_code(&lean_code).unwrap();
    }

    #[test]
    fn test_ilist_with_lawful_beq() {
        let mut ilist_type = spec_ir::create_ilist_type();
        ilist_type.attributes = vec!["grind".to_string()];

        let inductive_def = ilist_type.to_lean();
        let lawful_support = ilist_type.generate_complete_lawful_beq();
        let full_code = format!("{}\n\n{}", inductive_def, lawful_support);

        // Verify the code validates
        validate_lean_code(&full_code)
            .unwrap_or_else(|e| panic!("Generated LawfulBEq code failed validation: {}", e));
    }
}

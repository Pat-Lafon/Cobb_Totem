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
            Expression::IfThenElse {
                condition,
                then_branch,
                else_branch,
            } => {
                format!(
                    "(ite ({}) ({}) ({}))",
                    condition.to_lean(),
                    then_branch.to_lean(),
                    else_branch.to_lean()
                )
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
    types_with_theorems: TypeTheorems,
}

type TypeTheorems = std::collections::HashMap<String, String>;

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
        // Check if any axiom uses the aesop tactic
        let needs_aesop = self
            .axioms
            .iter()
            .any(|axiom| axiom.proof.as_ref().is_some_and(|s| s.contains("aesop")));

        let mut output = String::new();
        if needs_aesop {
            output.push_str("import Aesop\n\n");
        }

        for node in &self.nodes {
            match node {
                AstNode::TypeDeclaration(type_decl) => {
                    output.push_str(&type_decl.to_lean());
                    if let Some(theorems) = self.types_with_theorems.get(&type_decl.name) {
                        output.push_str("\n\n");
                        output.push_str(theorems);
                    }
                }
                other => output.push_str(&other.to_lean()),
            }
            output.push_str("\n\n");
        }

        for axiom in &self.axioms {
            output.push_str(&axiom.to_lean());
            output.push_str("\n\n");
        }

        output
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        VarName,
        lean_validation::validate_lean_code,
        prog_ir::{Type, TypeDecl, Variant},
    };

    use super::*;
    use crate::spec_ir;

    fn create_len_function() -> LetBinding {
        let code = r#"
            let rec len (l : ilist) (n : int) : bool = match l with
              | Nil -> n = 0
              | Cons (_, rest) -> len rest (n - 1)
        "#;

        let nodes = crate::ocamlparser::OcamlParser::parse_nodes(code)
            .expect("Failed to parse len function");

        nodes
            .iter()
            .find_map(|node| match node {
                AstNode::LetBinding(binding) if binding.name == VarName::new("len") => {
                    Some(binding.clone())
                }
                _ => None,
            })
            .expect("Failed to find len function in parsed nodes")
    }

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
        validate_lean_code(&lean_output)
            .unwrap_or_else(|e| panic!("Generated Lean code failed validation: {}", e));
    }

    #[test]
    fn test_ilist_type() {
        let ilist_type = spec_ir::create_ilist_type();

        let lean_code = ilist_type.to_lean();
        assert_eq!(
            lean_code,
            "@[grind]\ninductive ilist where\n  | Nil\n  | Cons : Int → ilist → ilist\nderiving BEq, Repr"
        );
        validate_lean_code(&lean_code)
            .unwrap_or_else(|e| panic!("Generated Lean code failed validation: {}", e));
    }

    #[test]
    fn test_len_function() {
        let ilist_type = spec_ir::create_ilist_type();
        let len_function = create_len_function();

        let lean_code = format!("{}\n\n{}", ilist_type.to_lean(), len_function.to_lean());
        assert_eq!(
            lean_code,
            "@[grind]\ninductive ilist where\n  | Nil\n  | Cons : Int → ilist → ilist\nderiving BEq, Repr\n\ndef len (l : ilist) (n : Int) : Bool := match l with\n  | .Nil => (n == 0)\n  | .Cons _ rest => len rest (n - 1)"
        );
        validate_lean_code(&lean_code)
            .unwrap_or_else(|e| panic!("Generated Lean code failed validation: {}", e));
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
        validate_lean_code(&lean_code)
            .unwrap_or_else(|e| panic!("Generated Lean code failed validation: {}", e));
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
        assert_eq!(lean_code, "@[simp, grind]\ndef bar (y : Bool) : Bool := y");
        validate_lean_code(&lean_code)
            .unwrap_or_else(|e| panic!("Generated Lean code failed validation: {}", e));
    }

    #[test]
    fn test_ilist_with_lawful_beq() {
        let ilist_type = spec_ir::create_ilist_type();

        let inductive_def = ilist_type.to_lean();
        let lawful_support = ilist_type.generate_complete_lawful_beq();
        let full_code = format!("{}\n\n{}", inductive_def, lawful_support);

        // Verify the code validates
        validate_lean_code(&full_code)
            .unwrap_or_else(|e| panic!("Generated LawfulBEq code failed validation: {}", e));
    }

    #[test]
    fn test_context_builder_with_ilist_and_functions() {
        let ilist_type = spec_ir::create_ilist_type();
        let len_function = create_len_function();

        let builder = LeanContextBuilder::new().with_nodes(vec![
            AstNode::TypeDeclaration(ilist_type.clone()),
            AstNode::LetBinding(len_function),
        ]);

        let lean_code = builder.build();

        // Verify the generated code validates
        validate_lean_code(&lean_code)
            .unwrap_or_else(|e| panic!("Context builder generated code failed validation: {}", e));
    }

    #[test]
    fn test_context_builder_with_multiple_types() {
        let ilist_type = spec_ir::create_ilist_type();

        let tree_type = TypeDecl {
            name: "tree".to_string(),
            variants: vec![
                Variant {
                    name: "Leaf".to_string(),
                    fields: vec![],
                },
                Variant {
                    name: "Node".to_string(),
                    fields: vec![
                        Type::Int,
                        Type::Named("tree".to_string()),
                        Type::Named("tree".to_string()),
                    ],
                },
            ],
            attributes: vec!["grind".to_string()],
        };

        let builder = LeanContextBuilder::new().with_nodes(vec![
            AstNode::TypeDeclaration(ilist_type),
            AstNode::TypeDeclaration(tree_type),
        ]);

        let lean_code = builder.build();

        // Verify the generated code validates
        validate_lean_code(&lean_code)
            .unwrap_or_else(|e| panic!("Multiple types code failed validation: {}", e));
    }
}

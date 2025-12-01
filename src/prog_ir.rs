use std::fmt;
use std::str::FromStr;

use crate::{ToLean, VarName};

#[derive(Debug, Clone, PartialEq)]
pub enum ConstructorName {
    Simple(String),
    Qualified { module: String, name: String },
}

impl ConstructorName {
    /// Validates that a name is a valid constructor identifier.
    ///
    /// A valid constructor name must:
    /// - Start with an uppercase letter
    /// - Contain only alphanumeric characters or underscores
    fn is_valid_name(name: &str) -> bool {
        name.chars().next().is_some_and(|c| c.is_uppercase())
            && name.chars().all(|c| c.is_alphanumeric() || c == '_')
    }
}

impl FromStr for ConstructorName {
    type Err = String;

    fn from_str(text: &str) -> Result<Self, Self::Err> {
        let parts: Vec<&str> = text.split('.').collect();

        match parts.as_slice() {
            [name] => {
                // Simple constructor
                if Self::is_valid_name(name) {
                    Ok(ConstructorName::Simple(name.to_string()))
                } else {
                    Err(format!("Invalid simple constructor name: '{}'", text))
                }
            }
            [module, name] => {
                // Qualified constructor
                if Self::is_valid_name(module) && Self::is_valid_name(name) {
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

#[derive(Debug, Clone, PartialEq)]
pub struct TypeDecl {
    pub name: String,
    pub variants: Vec<Variant>,
    pub attributes: Vec<String>,
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

impl ToLean for TypeDecl {
    fn to_lean(&self) -> String {
        let variants_str = self
            .variants
            .iter()
            .map(|v| v.to_lean_with_type(&self.name))
            .collect::<Vec<_>>()
            .join("\n  | ");

        let attrs_str = if self.attributes.is_empty() {
            String::new()
        } else {
            format!("@[{}]\n", self.attributes.join(", "))
        };

        format!(
            "{}inductive {} where\n  | {}\nderiving BEq, Repr",
            attrs_str, self.name, variants_str
        )
    }
}

impl TypeDecl {
    /// Generate parameter names with a given prefix and count
    fn generate_param_names(count: usize, prefix: &str) -> Vec<String> {
        (0..count).map(|i| format!("{}{}", prefix, i)).collect()
    }

    /// Generate LawfulBEq helper theorems for beq behavior on constructor combinations
    fn generate_beq_theorems(&self) -> String {
        let mut theorems = Vec::new();

        for variant1 in &self.variants {
            for variant2 in &self.variants {
                if variant1.name == variant2.name {
                    // Same constructors - generates (beq_cons_cons style)
                    if variant1.fields.is_empty() {
                        // Both are nullary constructors
                        let theorem_name = format!(
                            "{}.beq_{}_{}",
                            self.name,
                            variant1.name.to_lowercase(),
                            variant2.name.to_lowercase()
                        );
                        let theorem = format!(
                            "@[simp, grind =] theorem {} : ({}.{} == {}.{}) = true := rfl",
                            theorem_name, self.name, variant1.name, self.name, variant2.name
                        );
                        theorems.push(theorem);
                    } else {
                        // Both are n-ary constructors - need parameters
                        let param_names1 = Self::generate_param_names(variant1.fields.len(), "x");
                        let param_names2 = Self::generate_param_names(variant2.fields.len(), "y");

                        let params1 = param_names1.join(" ");
                        let params2 = param_names2.join(" ");

                        let eq_checks = param_names1
                            .iter()
                            .zip(param_names2.iter())
                            .map(|(x, y)| format!("{} == {}", x, y))
                            .collect::<Vec<_>>()
                            .join(" && ");

                        let theorem_name = format!(
                            "{}.beq_{}_{}",
                            self.name,
                            variant1.name.to_lowercase(),
                            variant2.name.to_lowercase()
                        );
                        let theorem = format!(
                            "@[simp, grind =] theorem {} :\n  ({}.{} {} == {}.{} {}) = ({}) := rfl",
                            theorem_name,
                            self.name,
                            variant1.name,
                            params1,
                            self.name,
                            variant2.name,
                            params2,
                            eq_checks
                        );
                        theorems.push(theorem);
                    }
                } else {
                    // Different constructors - always false
                    let theorem_name = format!(
                        "{}.beq_{}_{}",
                        self.name,
                        variant1.name.to_lowercase(),
                        variant2.name.to_lowercase()
                    );
                    let params1 = if variant1.fields.is_empty() {
                        String::new()
                    } else {
                        let vars = Self::generate_param_names(variant1.fields.len(), "x");
                        format!(" {}", vars.join(" "))
                    };
                    let params2 = if variant2.fields.is_empty() {
                        String::new()
                    } else {
                        let vars = Self::generate_param_names(variant2.fields.len(), "y");
                        format!(" {}", vars.join(" "))
                    };
                    let theorem = format!(
                        "@[simp, grind =] theorem {} : ({}.{}{} == {}.{}{}) = false := rfl",
                        theorem_name,
                        self.name,
                        variant1.name,
                        params1,
                        self.name,
                        variant2.name,
                        params2
                    );
                    theorems.push(theorem);
                }
            }
        }

        theorems.join("\n")
    }

    /// Generate LawfulBEq instance for this type
    fn generate_lawful_beq_instance(&self) -> String {
        // For eq_of_beq, use induction on `a` generalizing `b` and use grind for each case
        let eq_of_beq_cases = {
            let mut cases = Vec::new();
            for v in &self.variants {
                let params = if v.fields.is_empty() {
                    String::new()
                } else {
                    let vars = Self::generate_param_names(v.fields.len(), "x");
                    format!(" {}", vars.join(" "))
                };
                cases.push(format!("    | {}{} => grind", v.name, params));
            }
            cases.join("\n")
        };

        let rfl_cases = self
            .variants
            .iter()
            .map(|v| {
                if v.fields.is_empty() {
                    format!("    | {} => grind", v.name)
                } else {
                    // Generate parameter names and include the inductive hypothesis
                    let vars = Self::generate_param_names(v.fields.len(), "x");
                    let params_str = vars.join(" ");
                    // The inductive hypothesis is automatically added by Lean as 'ih'
                    format!("    | {} {} ih => grind", v.name, params_str)
                }
            })
            .collect::<Vec<_>>()
            .join("\n");

        format!(
            "@[grind ., simp]\ninstance : LawfulBEq {} where\n  eq_of_beq {{a b}} h := by\n    induction a generalizing b with\n{}\n  rfl {{a}} := by\n    induction a with\n{}",
            self.name, eq_of_beq_cases, rfl_cases
        )
    }

    /// Generate complete LawfulBEq support (theorems + instance) for this type
    pub fn generate_complete_lawful_beq(&self) -> String {
        format!(
            "{}\n\n{}",
            self.generate_beq_theorems(),
            self.generate_lawful_beq_instance()
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

impl ToLean for Literal {
    fn to_lean(&self) -> String {
        match self {
            Literal::Int(n) => n.to_string(),
            Literal::Bool(b) => if *b { "true" } else { "false" }.to_string(),
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

impl ToLean for UnaryOp {
    fn to_lean(&self) -> String {
        match self {
            UnaryOp::Neg => "-".to_string(),
            UnaryOp::Not => "¬".to_string(),
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

impl ToLean for BinaryOp {
    fn to_lean(&self) -> String {
        match self {
            BinaryOp::Eq => "=".to_string(),
            BinaryOp::Neq => "≠".to_string(),
            BinaryOp::Gte => "≥".to_string(),
            BinaryOp::Gt => ">".to_string(),
            BinaryOp::Lte => "≤".to_string(),
            BinaryOp::Lt => "<".to_string(),
            BinaryOp::Add => "+".to_string(),
            BinaryOp::Sub => "-".to_string(),
            BinaryOp::Mul => "*".to_string(),
            BinaryOp::Div => "/".to_string(),
            BinaryOp::And => "∧".to_string(),
            BinaryOp::Or => "∨".to_string(),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Pattern {
    Variable(VarName),
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

impl ToLean for Pattern {
    fn to_lean(&self) -> String {
        match self {
            Pattern::Variable(name) => name.to_string(),
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

#[derive(Debug, Clone, PartialEq)]
pub enum Expression {
    Variable(VarName),
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
    pub name: VarName,
    pub attributes: Vec<String>,
    pub is_recursive: bool,
    pub params: Vec<(VarName, Type)>,
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
    use crate::VarName;
    use crate::ocamlparser::OcamlParser;
    use crate::prog_ir::{
        AstNode, BinaryOp, ConstructorName, Expression, Literal, Pattern, Type, TypeDecl, Variant,
    };

    #[test]
    fn test_parse_sorted_predicate() {
        // Define the sorted predicate with nested matches
        let sorted_def = "let [@simp] [@grind] rec sorted (l : ilist) : bool = match l with | Nil -> true | Cons (h, t) -> match t with | Nil -> true | Cons (h2, t2) -> (h <= h2) && sorted (Cons (h2, t2))";

        // Parse the sorted predicate
        let nodes = OcamlParser::parse_nodes(sorted_def)
            .unwrap_or_else(|e| panic!("Failed to parse sorted predicate: {}", e));

        // Verify that the predicate parsed successfully
        assert_eq!(nodes.len(), 1, "Expected exactly one node");

        // Construct the expected AST
        let expected = AstNode::LetBinding(crate::prog_ir::LetBinding {
            name: VarName::new("sorted"),
            attributes: vec!["simp".to_string(), "grind".to_string()],
            is_recursive: true,
            params: vec![(VarName::new("l"), Type::Named("ilist".to_string()))],
            return_type: Some(Type::Bool),
            body: Expression::Match(
                Box::new(Expression::Variable("l".into())),
                vec![
                    (
                        Pattern::Constructor(ConstructorName::Simple("Nil".to_string()), vec![]),
                        Expression::Literal(Literal::Bool(true)),
                    ),
                    (
                        Pattern::Constructor(
                            ConstructorName::Simple("Cons".to_string()),
                            vec![Pattern::Variable("h".into()), Pattern::Variable("t".into())],
                        ),
                        Expression::Match(
                            Box::new(Expression::Variable("t".into())),
                            vec![
                                (
                                    Pattern::Constructor(
                                        ConstructorName::Simple("Nil".to_string()),
                                        vec![],
                                    ),
                                    Expression::Literal(Literal::Bool(true)),
                                ),
                                (
                                    Pattern::Constructor(
                                        ConstructorName::Simple("Cons".to_string()),
                                        vec![
                                            Pattern::Variable("h2".into()),
                                            Pattern::Variable("t2".into()),
                                        ],
                                    ),
                                    Expression::BinaryOp(
                                        Box::new(Expression::BinaryOp(
                                            Box::new(Expression::Variable("h".into())),
                                            BinaryOp::Lte,
                                            Box::new(Expression::Variable("h2".into())),
                                        )),
                                        BinaryOp::And,
                                        Box::new(Expression::Application(
                                            Box::new(Expression::Variable("sorted".into())),
                                            vec![Expression::Constructor(
                                                ConstructorName::Simple("Cons".to_string()),
                                                vec![
                                                    Expression::Variable("h2".into()),
                                                    Expression::Variable("t2".into()),
                                                ],
                                            )],
                                        )),
                                    ),
                                ),
                            ],
                        ),
                    ),
                ],
            ),
        });

        assert_eq!(nodes[0], expected);
    }

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
            attributes: vec![],
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

        let var = Expression::Variable("x".into());
        assert_eq!(var.to_string(), "x");
    }

    #[test]
    fn test_pattern_display() {
        let wildcard = Pattern::Wildcard;
        assert_eq!(wildcard.to_string(), "_");

        let var = Pattern::Variable("x".into());
        assert_eq!(var.to_string(), "x");

        let int_lit = Pattern::Literal(Literal::Int(0));
        assert_eq!(int_lit.to_string(), "0");

        let constructor = Pattern::Constructor(
            ConstructorName::Simple("Cons".to_string()),
            vec![Pattern::Wildcard, Pattern::Variable("rest".into())],
        );
        assert_eq!(constructor.to_string(), "Cons(_, rest)");
    }

    #[test]
    fn test_complete_lawful_beq_simple() {
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
            attributes: vec!["grind".to_string()],
        };

        // Verify theorem generation
        let theorems = bool_type.generate_beq_theorems();
        let expected = "@[simp, grind =] theorem MyBool.beq_true_true : (MyBool.True == MyBool.True) = true := rfl\n\
                       @[simp, grind =] theorem MyBool.beq_true_false : (MyBool.True == MyBool.False) = false := rfl\n\
                       @[simp, grind =] theorem MyBool.beq_false_true : (MyBool.False == MyBool.True) = false := rfl\n\
                       @[simp, grind =] theorem MyBool.beq_false_false : (MyBool.False == MyBool.False) = true := rfl";
        assert_eq!(theorems, expected);

        // Verify instance structure
        let instance = bool_type.generate_lawful_beq_instance();
        assert!(instance.contains("instance : LawfulBEq MyBool"));
        assert!(instance.contains("eq_of_beq"));
        assert!(instance.contains("induction a generalizing b with"));
        assert!(instance.contains("| True => grind"));
        assert!(instance.contains("| False => grind"));

        // Validate complete lawful beq (theorems + instance) with Lean code
        let complete = bool_type.generate_complete_lawful_beq();
        let lean_code = crate::lean_backend::LeanContextBuilder::new()
            .with_nodes(vec![AstNode::TypeDeclaration(bool_type)])
            .with_type_theorems("MyBool", complete)
            .build();
        crate::lean_validation::validate_lean_code(&lean_code).unwrap_or_else(|e| {
            panic!(
                "Generated complete lawful beq should be valid Lean code, but got error: {}",
                e
            )
        });
    }

    #[test]
    fn test_complete_lawful_beq_ilist() {
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
            attributes: vec!["grind".to_string()],
        };

        // Verify theorem generation
        let theorems = ilist_type.generate_beq_theorems();
        // Should have theorems for Nil-Nil, Nil-Cons, Cons-Nil, Cons-Cons
        assert!(theorems.contains("beq_nil_nil"));
        assert!(theorems.contains("beq_nil_cons"));
        assert!(theorems.contains("beq_cons_nil"));
        assert!(theorems.contains("beq_cons_cons"));
        // Cons-Cons should have parameter checking
        assert!(theorems.contains("x0 == y0"));

        // Verify instance structure
        let instance = ilist_type.generate_lawful_beq_instance();
        assert!(instance.contains("instance : LawfulBEq ilist"));
        assert!(instance.contains("induction a generalizing b with"));
        assert!(instance.contains("| Nil => grind"));
        assert!(instance.contains("| Cons x0 x1 => grind"));

        // Validate complete lawful beq (theorems + instance) with Lean code
        let complete = ilist_type.generate_complete_lawful_beq();
        let lean_code = crate::lean_backend::LeanContextBuilder::new()
            .with_nodes(vec![AstNode::TypeDeclaration(ilist_type)])
            .with_type_theorems("ilist", complete)
            .build();
        crate::lean_validation::validate_lean_code(&lean_code).unwrap_or_else(|e| {
            panic!(
                "Generated complete lawful beq should be valid Lean code, but got error: {}",
                e
            )
        });
    }

    #[test]
    fn test_output_ilist() {
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

        let beq_theorems = ilist_type.generate_beq_theorems();
        let expected_beq = "@[simp, grind =] theorem ilist.beq_nil_nil : (ilist.Nil == ilist.Nil) = true := rfl\n\
                            @[simp, grind =] theorem ilist.beq_nil_cons : (ilist.Nil == ilist.Cons y0 y1) = false := rfl\n\
                            @[simp, grind =] theorem ilist.beq_cons_nil : (ilist.Cons x0 x1 == ilist.Nil) = false := rfl\n\
                            @[simp, grind =] theorem ilist.beq_cons_cons :\n  (ilist.Cons x0 x1 == ilist.Cons y0 y1) = (x0 == y0 && x1 == y1) := rfl";
        assert_eq!(beq_theorems, expected_beq);

        let lawful_beq = ilist_type.generate_lawful_beq_instance();
        let expected_lawful = "@[grind ., simp]\ninstance : LawfulBEq ilist where\n  eq_of_beq {a b} h := by\n    induction a generalizing b with\n    | Nil => grind\n    | Cons x0 x1 => grind\n  rfl {a} := by\n    induction a with\n    | Nil => grind\n    | Cons x0 x1 ih => grind";
        assert_eq!(lawful_beq, expected_lawful);
    }

    #[test]
    fn test_complete_lawful_beq() {
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

        let complete = ilist_type.generate_complete_lawful_beq();
        let expected_complete = "@[simp, grind =] theorem ilist.beq_nil_nil : (ilist.Nil == ilist.Nil) = true := rfl\n\
                                 @[simp, grind =] theorem ilist.beq_nil_cons : (ilist.Nil == ilist.Cons y0 y1) = false := rfl\n\
                                 @[simp, grind =] theorem ilist.beq_cons_nil : (ilist.Cons x0 x1 == ilist.Nil) = false := rfl\n\
                                 @[simp, grind =] theorem ilist.beq_cons_cons :\n  (ilist.Cons x0 x1 == ilist.Cons y0 y1) = (x0 == y0 && x1 == y1) := rfl\n\
                                 \n\
                                 @[grind ., simp]\ninstance : LawfulBEq ilist where\n  eq_of_beq {a b} h := by\n    induction a generalizing b with\n    | Nil => grind\n    | Cons x0 x1 => grind\n  rfl {a} := by\n    induction a with\n    | Nil => grind\n    | Cons x0 x1 ih => grind";
        assert_eq!(complete, expected_complete);
    }
}

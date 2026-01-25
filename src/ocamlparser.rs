use crate::{
    Literal, VarName,
    prog_ir::{
        AstNode, BinaryOp, ConstructorName, Expression, LetBinding, Pattern, Type, TypeDecl,
        Variant,
    },
};
use tree_sitter::Node;

pub struct OcamlParser {
    source: String,
}

impl OcamlParser {
    pub(crate) fn new(source: String) -> Self {
        OcamlParser { source }
    }

    pub(crate) fn parse_source(
        source: &str,
    ) -> Result<(Self, tree_sitter::Tree), Box<dyn std::error::Error>> {
        let mut parser = tree_sitter::Parser::new();
        let lang = tree_sitter_ocaml::LANGUAGE_OCAML.into();
        parser.set_language(&lang)?;
        let tree = parser
            .parse(source, None)
            .ok_or("Failed to parse OCaml source")?;
        let ocaml_parser = OcamlParser::new(source.to_string());
        Ok((ocaml_parser, tree))
    }

    /// Parse OCaml source code and return all AstNodes
    pub(crate) fn parse_nodes(source: &str) -> Result<Vec<AstNode>, Box<dyn std::error::Error>> {
        let (parser, tree) = Self::parse_source(source)?;
        parser.parse(&tree)
    }

    // Example: "int", "int list", "string * bool"
    fn parse_type(&self, node: Node) -> Type {
        let text = node
            .utf8_text(self.source.as_bytes())
            .unwrap_or_else(|e| panic!("Failed to extract text from type node: {}", e));
        text.parse()
            .unwrap_or_else(|e| panic!("Failed to parse type: {}", e))
    }

    /// Helper: moves cursor to parent and asserts success.
    fn restore_cursor(cursor: &mut tree_sitter::TreeCursor, context: &str) {
        assert!(
            cursor.goto_parent(),
            "Failed to restore cursor to {} parent",
            context
        );
    }

    /// Parse a record_declaration node to extract field names and types.
    /// Example: "{ value : int; left : tree; right : tree }"
    /// Returns a vector of (field_name, Type) pairs.
    fn parse_record_declaration(&self, record_node: Node) -> Vec<(String, Type)> {
        let mut fields = Vec::new();
        let mut cursor = record_node.walk();
        assert!(
            cursor.goto_first_child(),
            "record_declaration has no children"
        );

        // Skip opening brace
        assert_eq!(cursor.node().kind(), "{");
        assert!(cursor.goto_next_sibling(), "record_declaration is empty");

        loop {
            let node = cursor.node();
            match node.kind() {
                "field_declaration" => {
                    // Parse field_declaration: name : type
                    let mut field_cursor = node.walk();
                    assert!(
                        field_cursor.goto_first_child(),
                        "field_declaration has no children"
                    );

                    let field_name_node = field_cursor.node();
                    assert_eq!(field_name_node.kind(), "field_name");
                    let field_name = field_name_node
                        .utf8_text(self.source.as_bytes())
                        .unwrap_or_else(|e| panic!("Failed to extract field name: {}", e))
                        .to_string();

                    assert!(
                        field_cursor.goto_next_sibling(),
                        "field_declaration missing ':'"
                    );
                    assert_eq!(field_cursor.node().kind(), ":");

                    assert!(
                        field_cursor.goto_next_sibling(),
                        "field_declaration missing type"
                    );
                    let type_node = field_cursor.node();
                    assert!(
                        type_node.kind() == "type_constructor_path"
                            || type_node.kind() == "constructed_type",
                        "Expected type in field_declaration, got '{}'",
                        type_node.kind()
                    );
                    let field_type = self.parse_type(type_node);
                    fields.push((field_name, field_type));
                }
                "}" => {
                    break;
                }
                ";" => {
                    // Separator, move to next field
                    assert!(cursor.goto_next_sibling(), "Expected field after semicolon");
                    continue;
                }
                kind => {
                    panic!("Unexpected node in record_declaration: '{}'", kind);
                }
            }
            if !cursor.goto_next_sibling() {
                break;
            }
        }

        fields
    }

    /// Helper: parse attributes from the current node and advance cursor.
    /// Returns a vector of cleaned attribute names (without [@...] brackets).
    /// Assumes cursor is at an "attribute" node; after execution, cursor is at the next sibling.
    fn parse_attributes(&self, cursor: &mut tree_sitter::TreeCursor) -> Vec<String> {
        let mut attributes = Vec::new();
        while cursor.node().kind() == "attribute" {
            let attr_text = cursor
                .node()
                .utf8_text(self.source.as_bytes())
                .expect("Failed to extract attribute")
                .to_string();
            // Remove surrounding [@...] brackets
            let cleaned = attr_text
                .trim_matches(|c| c == '@' || c == '[' || c == ']')
                .to_string();
            attributes.push(cleaned);
            assert!(
                cursor.goto_next_sibling(),
                "Failed to advance cursor past attribute"
            );
        }
        attributes
    }

    /// Parse a parameter node to extract name and required type annotation.
    /// Example: "(x : int)" -> ("x", Type::Int)
    /// Special case: unit parameter -> ("()", Type::Unit)
    /// Panics if parameter lacks type annotation (except for unit).
    fn parse_parameter(&self, param_node: Node) -> (VarName, Type) {
        let mut cursor = param_node.walk();
        assert!(cursor.goto_first_child(), "Parameter has no children");

        let pattern_node = cursor.node();

        match pattern_node.kind() {
            "typed_pattern" => {
                // Pattern with type annotation: name : type
                // typed_pattern includes the parens: ( name : type )
                let mut pattern_cursor = pattern_node.walk();
                assert!(
                    pattern_cursor.goto_first_child(),
                    "typed_pattern has no children: {}",
                    pattern_node.kind()
                );

                // Skip opening paren
                assert_eq!(pattern_cursor.node().kind(), "(");

                assert!(
                    pattern_cursor.goto_next_sibling(),
                    "typed_pattern missing value_pattern"
                );
                let pattern_node_inner = pattern_cursor.node();
                assert_eq!(
                    pattern_node_inner.kind(),
                    "value_pattern",
                    "Expected value_pattern in typed_pattern"
                );

                // value_pattern is a leaf containing the variable name
                let name = pattern_node_inner
                    .utf8_text(self.source.as_bytes())
                    .unwrap_or_else(|e| panic!("Failed to extract parameter name: {}", e))
                    .to_string();

                assert!(
                    pattern_cursor.goto_next_sibling(),
                    "typed_pattern missing ':'"
                );
                assert_eq!(pattern_cursor.node().kind(), ":");

                assert!(
                    pattern_cursor.goto_next_sibling(),
                    "typed_pattern missing type"
                );
                let type_node = pattern_cursor.node();
                assert!(
                    type_node.kind() == "type_constructor_path"
                        || type_node.kind() == "constructed_type",
                    "Expected type in typed_pattern, got '{}'",
                    type_node.kind()
                );
                let ty = self.parse_type(type_node);

                (VarName::new(name), ty)
            }
            "unit" => {
                // Unit parameter: represented as "()" with type Unit
                (VarName::new("()"), Type::Unit)
            }
            kind => {
                panic!(
                    "Parameter must have a type annotation. Expected 'typed_pattern' or 'unit', got '{}'",
                    kind
                );
            }
        }
    }

    pub fn parse(
        &self,
        tree: &tree_sitter::Tree,
    ) -> Result<Vec<AstNode>, Box<dyn std::error::Error>> {
        let mut nodes = Vec::new();
        let mut cursor = tree.walk();

        assert!(cursor.goto_first_child(), "Tree has no root node");
        loop {
            let child = cursor.node();
            match child.kind() {
                "type_definition" => {
                    let type_decl = self.parse_type_definition(&mut cursor);
                    nodes.push(AstNode::TypeDeclaration(type_decl));
                }
                "value_definition" => {
                    let let_binding = self.parse_value_definition(&mut cursor);
                    nodes.push(AstNode::LetBinding(let_binding));
                }
                "comment" => {
                    // Skip comments
                }
                kind => {
                    panic!(
                        "Unexpected top-level node: '{}' (expected 'type_definition' or 'value_definition')",
                        kind
                    );
                }
            }

            if !cursor.goto_next_sibling() {
                break;
            }
        }

        Ok(nodes)
    }

    // Example: "type ilist = Nil | Cons of int * int list"
    // Example with attribute: "type[@simp] ilist = Nil | Cons of int * int list"
    fn parse_type_definition(&self, cursor: &mut tree_sitter::TreeCursor) -> TypeDecl {
        assert!(cursor.goto_first_child(), "Type definition has no children");

        let type_keyword = cursor.node();
        assert_eq!(type_keyword.kind(), "type");

        assert!(
            cursor.goto_next_sibling(),
            "Type definition missing children after 'type'"
        );

        // Step 1: Collect optional attributes (may be multiple)
        let attributes = self.parse_attributes(cursor);

        // Step 2: Parse type_binding
        let type_binding = cursor.node();
        assert_eq!(type_binding.kind(), "type_binding");

        let mut result = self.parse_type_binding(cursor);
        result.attributes = attributes;

        // After parse_type_binding, cursor is at type_binding
        // Verify no extra children after type_binding
        assert!(
            !cursor.goto_next_sibling(),
            "Unexpected children after type_binding"
        );

        // Restore cursor to parent (type_definition)
        Self::restore_cursor(cursor, "type_definition");
        result
    }

    // Example: "ilist = Nil | Cons of int * int list"
    fn parse_type_binding(&self, cursor: &mut tree_sitter::TreeCursor) -> TypeDecl {
        assert!(cursor.goto_first_child(), "Type binding has no children");

        let type_constructor = cursor.node();
        assert_eq!(type_constructor.kind(), "type_constructor");

        let name = type_constructor
            .utf8_text(self.source.as_bytes())
            .expect("Failed to extract type constructor name")
            .to_string();

        assert!(cursor.goto_next_sibling(), "Type binding missing '='");
        let equals = cursor.node();
        assert_eq!(equals.kind(), "=");

        assert!(
            cursor.goto_next_sibling(),
            "Type binding missing variant_declaration"
        );
        let variant_decl = cursor.node();
        assert_eq!(variant_decl.kind(), "variant_declaration");

        let mut variants = Vec::new();
        if cursor.goto_first_child() {
            let mut expect_constructor = cursor.node().kind() != "|";

            loop {
                let variant_child = cursor.node();
                match variant_child.kind() {
                    "|" => {
                        if expect_constructor {
                            panic!("Unexpected '|': expected constructor_declaration");
                        }
                        expect_constructor = true;
                    }
                    "constructor_declaration" => {
                        if !expect_constructor {
                            panic!("Unexpected constructor_declaration: expected '|'");
                        }
                        variants.push(self.parse_constructor_declaration(cursor));
                        expect_constructor = false;
                    }
                    kind => {
                        panic!("Expected 'constructor_declaration' or '|', got '{}'", kind);
                    }
                }

                if !cursor.goto_next_sibling() {
                    break;
                }
            }
            Self::restore_cursor(cursor, "variant_declaration");
        }

        // Verify no extra children
        assert!(
            !cursor.goto_next_sibling(),
            "Unexpected children after variant_declaration"
        );

        // Restore cursor to type_binding node
        Self::restore_cursor(cursor, "type_binding");
        TypeDecl {
            name,
            variants,
            attributes: Vec::new(),
        }
    }

    // Example: "Nil" or "Cons of int * int list"
    fn parse_constructor_declaration(&self, cursor: &mut tree_sitter::TreeCursor) -> Variant {
        assert!(
            cursor.goto_first_child(),
            "Constructor declaration has no children"
        );

        let constructor_name = cursor.node();
        assert_eq!(constructor_name.kind(), "constructor_name");

        let name = constructor_name
            .utf8_text(self.source.as_bytes())
            .expect("Failed to extract constructor name")
            .to_string();

        if !cursor.goto_next_sibling() {
            // No fields, just the constructor name
            Self::restore_cursor(cursor, "constructor_declaration");
            return Variant {
                name,
                fields: vec![],
            };
        }

        let next = cursor.node();
        assert_eq!(
            next.kind(),
            "of",
            "Expected 'of' node in constructor_declaration, got '{}'",
            next.kind()
        );

        // Has 'of' keyword, now process fields
        let mut fields = Vec::new();
        assert!(
            cursor.goto_next_sibling(),
            "Expected at least one field in constructor"
        );

        let child = cursor.node();
        match child.kind() {
            "record_declaration" => {
                // Record-style fields: { name : type; ... }
                fields = self.parse_record_declaration(child);
            }
            "type_constructor_path" | "constructed_type" => {
                // Tuple-style fields: type * type * ...
                let field_type = self.parse_type(child);
                fields.push((fields.len().to_string(), field_type));

                // Parse remaining fields with separators
                while cursor.goto_next_sibling() {
                    let child = cursor.node();
                    match child.kind() {
                        "*" => {
                            assert!(cursor.goto_next_sibling(), "Expected field after separator");
                            let field = cursor.node();
                            assert!(
                                field.kind() == "type_constructor_path"
                                    || field.kind() == "constructed_type",
                                "Expected field after separator, got '{}'",
                                field.kind()
                            );
                            let field_type = self.parse_type(field);
                            fields.push((fields.len().to_string(), field_type));
                        }
                        kind => {
                            panic!("Expected separator, got '{}'", kind);
                        }
                    }
                }
            }
            kind => {
                panic!("Expected field or record_declaration, got '{}'", kind);
            }
        }

        // Restore cursor to constructor_declaration
        Self::restore_cursor(cursor, "constructor_declaration");
        Variant { name, fields }
    }

    // Example: "let rec len (l : ilist) (n : int) : bool = match l with ..."
    fn parse_value_definition(&self, cursor: &mut tree_sitter::TreeCursor) -> LetBinding {
        let mut params = Vec::new();

        assert!(
            cursor.goto_first_child(),
            "Value definition has no children"
        );

        // Step 0: Skip 'let' keyword (first child in value_definition)
        let let_keyword = cursor.node();
        assert_eq!(let_keyword.kind(), "let");
        assert!(
            cursor.goto_next_sibling(),
            "Value definition missing children after 'let'"
        );

        // Step 1: Collect optional attributes (may be multiple)
        let attributes = self.parse_attributes(cursor);

        // Step 2: Check for 'rec' keyword (optional)
        let is_recursive = if cursor.node().kind() == "rec" {
            assert!(
                cursor.goto_next_sibling(),
                "Value definition missing let_binding after 'rec'"
            );
            true
        } else {
            false
        };

        // Step 3: Parse let_binding
        assert_eq!(
            cursor.node().kind(),
            "let_binding",
            "Expected let_binding in value_definition"
        );
        assert!(cursor.goto_first_child(), "Let binding has no children");

        // Step 3a: Parse value_name
        let value_name_node = cursor.node();
        assert_eq!(value_name_node.kind(), "value_name");
        let name = value_name_node
            .utf8_text(self.source.as_bytes())
            .expect("Failed to extract value name")
            .to_string();

        // Step 3b: Collect all parameters (including unit parameters)
        while cursor.goto_next_sibling() && cursor.node().kind() == "parameter" {
            let node = cursor.node();
            params.push(self.parse_parameter(node));
        }

        // Step 3c: Handle optional return type annotation (preceded by ':')
        let return_type = if cursor.node().kind() == ":" {
            assert!(
                cursor.goto_next_sibling(),
                "Return type annotation missing type after ':'"
            );

            let type_node = cursor.node();
            assert!(
                type_node.kind() == "type_constructor_path"
                    || type_node.kind() == "constructed_type",
                "Expected type after ':', got '{}'",
                type_node.kind()
            );
            let return_type = Some(self.parse_type(type_node));

            assert!(cursor.goto_next_sibling(), "Expected '=' after return type");
            return_type
        } else {
            None
        };

        assert_eq!(cursor.node().kind(), "=");

        // Step 3e: Parse body expression
        assert!(
            cursor.goto_next_sibling(),
            "Let binding missing body expression"
        );

        let body_node = cursor.node();
        let body = self.parse_expression(body_node);

        Self::restore_cursor(cursor, "let_binding");
        Self::restore_cursor(cursor, "value_definition");

        LetBinding {
            name: VarName::new(name),
            attributes,
            is_recursive,
            params,
            return_type,
            body,
        }
    }

    fn parse_number_from_node(&self, node: Node) -> Literal {
        let text = node
            .utf8_text(self.source.as_bytes())
            .unwrap_or_else(|e| panic!("Failed to extract number text: {}", e));
        text.trim()
            .parse::<i32>()
            .map(Literal::Int)
            .unwrap_or_else(|e| panic!("Failed to parse number '{}': {}", text, e))
    }

    fn parse_boolean_from_node(&self, node: Node) -> Literal {
        let text = node
            .utf8_text(self.source.as_bytes())
            .unwrap_or_else(|e| panic!("Failed to extract boolean text: {}", e));
        match text.trim() {
            "true" => Literal::Bool(true),
            "false" => Literal::Bool(false),
            s => panic!("Expected 'true' or 'false', got '{}'", s),
        }
    }

    fn parse_expression(&self, node: Node) -> Expression {
        match node.kind() {
            "match_expression" => self.parse_match_expression_node(node),
            "if_expression" => self.parse_if_expression(node),
            "fun_expression" => self.parse_fun_expression(node),
            "parenthesized_expression" => {
                let mut cursor = node.walk();
                assert!(
                    cursor.goto_first_child(),
                    "parenthesized_expression has no children"
                );

                assert_eq!(
                    cursor.node().kind(),
                    "(",
                    "Expected opening parenthesis in parenthesized_expression"
                );

                assert!(
                    cursor.goto_next_sibling(),
                    "parenthesized_expression missing inner expression"
                );

                let inner_node = cursor.node();
                // Check if inner is a tuple expression or a single expression
                let result = if inner_node.kind() == "tuple_expression" {
                    Expression::Tuple(self.parse_tuple_elements(inner_node))
                } else {
                    self.parse_expression(inner_node)
                };

                assert!(
                    cursor.goto_next_sibling(),
                    "parenthesized_expression missing closing parenthesis"
                );

                assert_eq!(
                    cursor.node().kind(),
                    ")",
                    "Expected closing parenthesis in parenthesized_expression"
                );

                result
            }
            "value_path" => {
                // Extract identifier text
                let text = node
                    .utf8_text(self.source.as_bytes())
                    .expect("Failed to extract identifier text");
                let valid_var = text
                    .chars()
                    .all(|c| c.is_alphanumeric() || c == '_' || c == '\'')
                    && text
                        .chars()
                        .next()
                        .is_some_and(|c| c.is_alphabetic() || c == '_');
                assert!(valid_var, "Expected valid variable name, got '{}'", text);
                Expression::Variable(VarName::new(text))
            }
            "constructor_path" => {
                // Extract constructor name
                let text = node
                    .utf8_text(self.source.as_bytes())
                    .expect("Failed to extract constructor name");
                let name = text
                    .parse::<ConstructorName>()
                    .unwrap_or_else(|e| panic!("{}", e));

                Expression::Constructor(name, vec![])
            }
            "infix_expression" => self.parse_infix_operation(node),
            "prefix_expression" => self.parse_prefix_expression(node),
            "application_expression" => self.parse_application_expression(node),
            "number" => Expression::Literal(self.parse_number_from_node(node)),
            "boolean" => Expression::Literal(self.parse_boolean_from_node(node)),
            kind => {
                unimplemented!("Unhandled expression node kind: '{}'", kind)
            }
        }
    }

    fn parse_infix_operation(&self, node: Node) -> Expression {
        let mut cursor = node.walk();
        assert!(
            cursor.goto_first_child(),
            "Binary operation has no children"
        );

        let left = self.parse_expression(cursor.node());

        assert!(
            cursor.goto_next_sibling(),
            "Binary operation missing operator"
        );
        let op_node = cursor.node();
        let op = self.parse_binary_op(op_node);

        assert!(
            cursor.goto_next_sibling(),
            "Binary operation missing right operand"
        );
        let right = self.parse_expression(cursor.node());

        Expression::BinaryOp(Box::new(left), op, Box::new(right))
    }

    fn parse_binary_op(&self, node: Node) -> BinaryOp {
        let text = node
            .utf8_text(self.source.as_bytes())
            .expect("Failed to extract operator text");

        text.parse().expect("Failed to parse binary operator")
    }

    /// Extract expressions from a comma-separated sequence within parentheses.
    /// Precondition: cursor positioned at the opening "(" of a parenthesized list.
    /// Extract comma-separated expressions from a tuple_expression node.
    /// Precondition: node is a tuple_expression.
    /// Enforces pattern: expression (comma expression)*
    fn parse_tuple_elements(&self, node: Node) -> Vec<Expression> {
        let mut cursor = node.walk();
        let mut elements = Vec::new();

        if !cursor.goto_first_child() {
            return elements;
        }

        let mut expect_expression = true;
        loop {
            let current = cursor.node();
            if expect_expression {
                assert_ne!(current.kind(), ",", "Expected expression, got comma");
                elements.push(self.parse_expression(current));
                expect_expression = false;
            } else {
                assert_eq!(
                    current.kind(),
                    ",",
                    "Expected comma, got '{}'",
                    current.kind()
                );
                expect_expression = true;
            }

            if !cursor.goto_next_sibling() {
                break;
            }
        }

        assert!(!expect_expression, "Tuple ended with comma");
        elements
    }

    fn parse_prefix_expression(&self, node: Node) -> Expression {
        let mut cursor = node.walk();
        assert!(
            cursor.goto_first_child(),
            "Prefix expression has no children"
        );

        let op_node = cursor.node();
        let op_text = op_node
            .utf8_text(self.source.as_bytes())
            .expect("Failed to extract prefix operator");

        let op = op_text.parse().unwrap();

        assert!(
            cursor.goto_next_sibling(),
            "Prefix expression missing operand"
        );
        let operand = self.parse_expression(cursor.node());

        Expression::UnaryOp(op, Box::new(operand))
    }

    fn parse_application_expression(&self, node: Node) -> Expression {
        let mut cursor = node.walk();
        assert!(
            cursor.goto_first_child(),
            "Application expression has no children"
        );

        let func_node = cursor.node();
        let func = self.parse_expression(func_node);

        assert!(
            cursor.goto_next_sibling(),
            "Application expression missing argument"
        );

        let mut args = Vec::new();
        let arg_node = cursor.node();
        let arg = self.parse_expression(arg_node);
        args.push(arg);

        while cursor.goto_next_sibling() {
            let arg_node = cursor.node();
            let arg = self.parse_expression(arg_node);
            args.push(arg);
        }

        // Flatten Application(Constructor(name, []), args) into Constructor(name, args)
        // Also flatten tuple arguments into the constructor argument list
        match func {
            Expression::Constructor(name, constructor_args) => {
                assert!(
                    constructor_args.is_empty(),
                    "constructor_path should not have arguments"
                );
                let flattened_args = match args.as_slice() {
                    [Expression::Tuple(tuple_elements)] => tuple_elements.clone(),
                    _ => panic!("Constructor application should have exactly one tuple argument"),
                };
                Expression::Constructor(name, flattened_args)
            }
            Expression::Variable(ref name) => {
                // Special handling for ite as a variable being applied
                if &**name == "ite" {
                    assert_eq!(
                        args.len(),
                        3,
                        "ite requires exactly 3 arguments, got {}",
                        args.len()
                    );
                    Expression::IfThenElse {
                        condition: Box::new(args[0].clone()),
                        then_branch: Box::new(args[1].clone()),
                        else_branch: Box::new(args[2].clone()),
                    }
                } else if &**name == "not" {
                    assert_eq!(
                        args.len(),
                        1,
                        "not requires exactly 1 argument, got {}",
                        args.len()
                    );
                    Expression::Not(Box::new(args[0].clone()))
                } else {
                    Expression::Application(Box::new(func), args)
                }
            }
            Expression::Application(_, _) | Expression::Match(_, _) => {
                Expression::Application(Box::new(func), args)
            }
            Expression::Literal(_)
            | Expression::UnaryOp(_, _)
            | Expression::BinaryOp(_, _, _)
            | Expression::Tuple(_)
            | Expression::IfThenElse { .. }
            | Expression::Not(_) => {
                panic!("Cannot apply non-function expression as a function")
            }
        }
    }

    fn parse_pattern(&self, node: Node) -> Pattern {
        match node.kind() {
            "constructor_path" => {
                // constructor_path nodes are leaf nodes (no children to recurse into)
                let text = node
                    .utf8_text(self.source.as_bytes())
                    .expect("Failed to extract constructor name");

                let name = text
                    .parse::<ConstructorName>()
                    .unwrap_or_else(|e| panic!("{}", e));
                Pattern::Constructor(name, vec![])
            }
            "constructor_pattern" => {
                let mut cursor = node.walk();
                assert!(
                    cursor.goto_first_child(),
                    "constructor_pattern has no children"
                );

                let constructor_name = cursor.node();
                let text = constructor_name
                    .utf8_text(self.source.as_bytes())
                    .expect("Failed to extract constructor name");
                let name = text
                    .parse::<ConstructorName>()
                    .unwrap_or_else(|e| panic!("{}", e));

                // Move to next sibling to find parenthesized_pattern
                let subpatterns = if cursor.goto_next_sibling()
                    && cursor.node().kind() == "parenthesized_pattern"
                {
                    self.parse_parenthesized_pattern(cursor.node())
                } else {
                    Vec::new()
                };

                Pattern::Constructor(name, subpatterns)
            }
            "value_pattern" => {
                let text = node
                    .utf8_text(self.source.as_bytes())
                    .expect("Failed to extract value pattern");
                if text == "_" {
                    Pattern::Wildcard
                } else {
                    Pattern::Variable(VarName::new(text))
                }
            }
            "number" => Pattern::Literal(self.parse_number_from_node(node)),
            "boolean" => Pattern::Literal(self.parse_boolean_from_node(node)),
            "parenthesized_pattern" => {
                let patterns = self.parse_parenthesized_pattern(node);
                assert_eq!(
                    patterns.len(),
                    1,
                    "Expected single pattern in parenthesized_pattern"
                );
                patterns.into_iter().next().unwrap()
            }
            "tuple_pattern" => {
                // Handle tuple patterns that appear at top-level (not wrapped in parens)
                let patterns = self.parse_tuple_pattern(node);
                if patterns.len() == 1 {
                    patterns.into_iter().next().unwrap()
                } else {
                    // Multiple patterns in a tuple
                    Pattern::Tuple(patterns)
                }
            }
            kind => {
                panic!("Unexpected pattern node kind: '{}'", kind);
            }
        }
    }

    fn parse_parenthesized_pattern(&self, node: Node) -> Vec<Pattern> {
        let mut cursor = node.walk();
        assert!(
            cursor.goto_first_child(),
            "parenthesized_pattern has no children"
        );

        assert_eq!(
            cursor.node().kind(),
            "(",
            "Expected opening parenthesis in parenthesized_pattern"
        );

        assert!(
            cursor.goto_next_sibling(),
            "parenthesized_pattern missing inner pattern"
        );

        let inner_node = cursor.node();
        let patterns = if inner_node.kind() == "tuple_pattern" {
            self.parse_tuple_pattern(inner_node)
        } else {
            vec![self.parse_pattern(inner_node)]
        };

        assert!(
            cursor.goto_next_sibling(),
            "parenthesized_pattern missing closing parenthesis"
        );

        assert_eq!(
            cursor.node().kind(),
            ")",
            "Expected closing parenthesis in parenthesized_pattern"
        );

        Self::restore_cursor(&mut cursor, "parenthesized_pattern");
        patterns
    }

    fn parse_tuple_pattern(&self, node: Node) -> Vec<Pattern> {
        let mut cursor = node.walk();
        let mut patterns = Vec::new();

        assert!(cursor.goto_first_child(), "Tuple pattern has no children");

        let mut expect_pattern = true;
        loop {
            let current = cursor.node();
            if expect_pattern {
                assert_ne!(current.kind(), ",", "Expected pattern, got comma");
                patterns.push(self.parse_pattern(current));
                expect_pattern = false;
            } else {
                assert_eq!(
                    current.kind(),
                    ",",
                    "Expected comma, got '{}'",
                    current.kind()
                );
                expect_pattern = true;
            }

            if !cursor.goto_next_sibling() {
                break;
            }
        }

        patterns
    }

    fn parse_if_expression(&self, node: Node) -> Expression {
        let mut cursor = node.walk();
        assert!(cursor.goto_first_child(), "If expression has no children");

        let if_keyword = cursor.node();
        assert_eq!(if_keyword.kind(), "if");

        // Next should be the condition expression
        assert!(
            cursor.goto_next_sibling(),
            "If expression missing condition"
        );
        let condition_node = cursor.node();
        let condition = self.parse_expression(condition_node);

        // Next should be 'then_clause'
        assert!(
            cursor.goto_next_sibling(),
            "If expression missing 'then_clause'"
        );
        let then_clause = cursor.node();
        assert_eq!(then_clause.kind(), "then_clause");

        // Parse the then_clause to get the expression
        let mut then_cursor = then_clause.walk();
        assert!(
            then_cursor.goto_first_child(),
            "then_clause has no children"
        );

        let then_keyword = then_cursor.node();
        assert_eq!(then_keyword.kind(), "then");

        assert!(
            then_cursor.goto_next_sibling(),
            "then_clause missing expression after 'then'"
        );
        let then_branch_node = then_cursor.node();
        let then_branch = self.parse_expression(then_branch_node);

        // Next should be 'else_clause'
        assert!(
            cursor.goto_next_sibling(),
            "If expression missing 'else_clause'"
        );
        let else_clause = cursor.node();
        assert_eq!(else_clause.kind(), "else_clause");

        // Parse the else_clause to get the expression
        let mut else_cursor = else_clause.walk();
        assert!(
            else_cursor.goto_first_child(),
            "else_clause has no children"
        );

        let else_keyword = else_cursor.node();
        assert_eq!(else_keyword.kind(), "else");

        assert!(
            else_cursor.goto_next_sibling(),
            "else_clause missing expression after 'else'"
        );
        let else_branch_node = else_cursor.node();
        let else_branch = self.parse_expression(else_branch_node);

        Expression::IfThenElse {
            condition: Box::new(condition),
            then_branch: Box::new(then_branch),
            else_branch: Box::new(else_branch),
        }
    }

    fn parse_fun_expression(&self, node: Node) -> Expression {
        // fun_expression has structure: fun param1 param2 ... -> body
        // We extract the body and skip parameters since they're handled at LetBinding level
        let mut cursor = node.walk();
        assert!(cursor.goto_first_child(), "Fun expression has no children");

        let fun_keyword = cursor.node();
        assert_eq!(fun_keyword.kind(), "fun");

        // Skip all parameters until we reach the arrow
        while cursor.goto_next_sibling() && cursor.node().kind() != "->" {
            // Skip parameter nodes
        }

        assert_eq!(
            cursor.node().kind(),
            "->",
            "Expected '->' in fun expression, got '{}'",
            cursor.node().kind()
        );

        // Now advance to the body expression
        assert!(
            cursor.goto_next_sibling(),
            "Fun expression missing body after '->'"
        );

        let body_node = cursor.node();

        // Reject nested fun expressions - they're not currently supported
        if body_node.kind() == "fun_expression" {
            panic!(
                "Nested fun expressions (e.g., 'fun x -> fun y -> body') are not supported. \
                Use standard let-binding parameter syntax instead: 'let f (x) (y) = body'. \
                Nested lambdas require a Lambda variant in the Expression enum to preserve curried structure."
            );
        }

        self.parse_expression(body_node)
    }

    fn parse_match_expression_node(&self, node: Node) -> Expression {
        let mut cursor = node.walk();
        assert!(
            cursor.goto_first_child(),
            "Match expression has no children"
        );

        let match_keyword = cursor.node();
        assert_eq!(match_keyword.kind(), "match");

        // Next should be the scrutinee (value being matched)
        assert!(
            cursor.goto_next_sibling(),
            "Match expression missing scrutinee"
        );
        let scrutinee_node = cursor.node();
        let scrutinee = self.parse_expression(scrutinee_node);

        assert!(
            cursor.goto_next_sibling(),
            "Match expression missing 'with' keyword"
        );
        let with_keyword = cursor.node();
        assert_eq!(with_keyword.kind(), "with");

        let mut cases = Vec::new();

        // Collect all match cases
        // First case may or may not have a leading '|' (depending on formatting)
        while cursor.goto_next_sibling() {
            let child = cursor.node();
            match child.kind() {
                "|" => {
                    // Skip the pipe separator and move to the next match_case
                    assert!(cursor.goto_next_sibling(), "Expected match_case after '|'");
                    let case_node = cursor.node();
                    assert_eq!(
                        case_node.kind(),
                        "match_case",
                        "Expected 'match_case', got '{}'",
                        case_node.kind()
                    );
                    let case = self.parse_match_case(&mut cursor);
                    cases.push(case);
                }
                "match_case" => {
                    // First case without leading '|' (valid OCaml syntax)
                    let case = self.parse_match_case(&mut cursor);
                    cases.push(case);
                }
                kind => {
                    panic!("Expected '|' or 'match_case', got '{}'", kind);
                }
            }
        }

        Expression::Match(Box::new(scrutinee), cases)
    }

    fn parse_match_case(&self, cursor: &mut tree_sitter::TreeCursor) -> (Pattern, Expression) {
        assert!(cursor.goto_first_child(), "Match case has no children");

        // Pattern is the first child (could be various types)
        let pattern_node = cursor.node();
        let pattern = self.parse_pattern(pattern_node);

        // Look for the arrow
        assert!(cursor.goto_next_sibling(), "Match case missing '->'");
        let arrow = cursor.node();
        assert_eq!(arrow.kind(), "->");

        // Body is the remaining text after the arrow
        assert!(cursor.goto_next_sibling(), "Match case missing body");
        let body_node = cursor.node();
        let body = self.parse_expression(body_node);

        // Restore cursor to match_case node
        assert!(
            cursor.goto_parent(),
            "Failed to restore cursor to match_case parent"
        );
        (pattern, body)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::VarName;

    fn assert_parse(source: &str, expected: Vec<AstNode>) {
        let (parser, tree) = OcamlParser::parse_source(source).unwrap();
        assert_eq!(parser.parse(&tree).unwrap(), expected);
    }

    fn let_binding(
        name: &str,
        params: Vec<(&str, Type)>,
        return_type: Option<Type>,
        body: Expression,
    ) -> AstNode {
        AstNode::LetBinding(LetBinding {
            name: VarName::new(name),
            attributes: vec![],
            is_recursive: false,
            params: params
                .into_iter()
                .map(|(n, t)| (VarName::new(n), t))
                .collect(),
            return_type,
            body,
        })
    }

    fn let_binding_rec(
        name: &str,
        attrs: Vec<&str>,
        params: Vec<(&str, Type)>,
        return_type: Option<Type>,
        body: Expression,
    ) -> AstNode {
        AstNode::LetBinding(LetBinding {
            name: VarName::new(name),
            attributes: attrs.into_iter().map(|s| s.to_string()).collect(),
            is_recursive: true,
            params: params
                .into_iter()
                .map(|(n, t)| (VarName::new(n), t))
                .collect(),
            return_type,
            body,
        })
    }

    #[test]
    fn test_parse_simple_type_definition() {
        let source = "type ilist = Nil | Cons of int * int list";
        let (parser, tree) = OcamlParser::parse_source(source).unwrap();

        let expected = vec![AstNode::TypeDeclaration(TypeDecl {
            name: "ilist".to_string(),
            variants: vec![
                Variant {
                    name: "Nil".to_string(),
                    fields: vec![],
                },
                Variant {
                    name: "Cons".to_string(),
                    fields: vec![
                        ("0".to_string(), Type::Int),
                        ("1".to_string(), Type::Named("int list".to_string())),
                    ],
                },
            ],
            attributes: vec![],
        })];

        assert_eq!(parser.parse(&tree).unwrap(), expected);
    }

    #[test]
    fn test_parse_type_definition_with_attribute() {
        let source = "type[@simp] ilist = Nil | Cons of int * int list";
        let (parser, tree) = OcamlParser::parse_source(source).unwrap();

        let expected = vec![AstNode::TypeDeclaration(TypeDecl {
            name: "ilist".to_string(),
            variants: vec![
                Variant {
                    name: "Nil".to_string(),
                    fields: vec![],
                },
                Variant {
                    name: "Cons".to_string(),
                    fields: vec![
                        ("0".to_string(), Type::Int),
                        ("1".to_string(), Type::Named("int list".to_string())),
                    ],
                },
            ],
            attributes: vec!["simp".to_string()],
        })];

        assert_eq!(parser.parse(&tree).unwrap(), expected);
    }

    #[test]
    fn test_parse_type_definition_with_multiple_attributes() {
        let source = "type[@simp][@reflect] ilist = Nil | Cons of int * int list";
        let (parser, tree) = OcamlParser::parse_source(source).unwrap();

        let expected = vec![AstNode::TypeDeclaration(TypeDecl {
            name: "ilist".to_string(),
            variants: vec![
                Variant {
                    name: "Nil".to_string(),
                    fields: vec![],
                },
                Variant {
                    name: "Cons".to_string(),
                    fields: vec![
                        ("0".to_string(), Type::Int),
                        ("1".to_string(), Type::Named("int list".to_string())),
                    ],
                },
            ],
            attributes: vec!["simp".to_string(), "reflect".to_string()],
        })];

        assert_eq!(parser.parse(&tree).unwrap(), expected);
    }

    #[test]
    fn test_parse_type_constructor_with_multiple_fields() {
        let source = "type triple = Triple of int * ilist * bool";
        let (parser, tree) = OcamlParser::parse_source(source).unwrap();

        let expected = vec![AstNode::TypeDeclaration(TypeDecl {
            name: "triple".to_string(),
            variants: vec![Variant {
                name: "Triple".to_string(),
                fields: vec![
                    ("0".to_string(), Type::Int),
                    ("1".to_string(), Type::Named("ilist".to_string())),
                    ("2".to_string(), Type::Bool),
                ],
            }],
            attributes: vec![],
        })];

        assert_eq!(parser.parse(&tree).unwrap(), expected);
    }

    #[test]
    fn test_parse_type_constructor_with_record_fields() {
        let source = "type node = Node of { value : int; left : tree; right : tree }";
        let (parser, tree) = OcamlParser::parse_source(source).unwrap();

        let expected = vec![AstNode::TypeDeclaration(TypeDecl {
            name: "node".to_string(),
            variants: vec![Variant {
                name: "Node".to_string(),
                fields: vec![
                    ("value".to_string(), Type::Int),
                    ("left".to_string(), Type::Named("tree".to_string())),
                    ("right".to_string(), Type::Named("tree".to_string())),
                ],
            }],
            attributes: vec![],
        })];

        assert_eq!(parser.parse(&tree).unwrap(), expected);
    }

    #[test]
    fn test_parse_mixed_constructors_record_and_tuple() {
        let source = "type expr = Const of int | BinOp of { left : expr; op : string; right : expr } | FuncCall of { name : string; args : expr list }";
        let (parser, tree) = OcamlParser::parse_source(source).unwrap();

        let expected = vec![AstNode::TypeDeclaration(TypeDecl {
            name: "expr".to_string(),
            variants: vec![
                Variant {
                    name: "Const".to_string(),
                    fields: vec![("0".to_string(), Type::Int)],
                },
                Variant {
                    name: "BinOp".to_string(),
                    fields: vec![
                        ("left".to_string(), Type::Named("expr".to_string())),
                        ("op".to_string(), Type::Named("string".to_string())),
                        ("right".to_string(), Type::Named("expr".to_string())),
                    ],
                },
                Variant {
                    name: "FuncCall".to_string(),
                    fields: vec![
                        ("name".to_string(), Type::Named("string".to_string())),
                        ("args".to_string(), Type::Named("expr list".to_string())),
                    ],
                },
            ],
            attributes: vec![],
        })];

        assert_eq!(parser.parse(&tree).unwrap(), expected);
    }

    #[test]
    fn test_parse_let_binding_single_parameter() {
        assert_parse(
            "let f (x : int) : bool = true",
            vec![let_binding(
                "f",
                vec![("x", Type::Int)],
                Some(Type::Bool),
                Expression::Literal(Literal::Bool(true)),
            )],
        );
    }

    #[test]
    fn test_parse_let_binding_unit_parameter() {
        assert_parse(
            "let f () : bool = true",
            vec![let_binding(
                "f",
                vec![("()", Type::Unit)],
                Some(Type::Bool),
                Expression::Literal(Literal::Bool(true)),
            )],
        );
    }

    #[test]
    fn test_parse_let_binding_multiple_parameters() {
        assert_parse(
            "let add (x : int) (y : int) : int = x + y",
            vec![let_binding(
                "add",
                vec![("x", Type::Int), ("y", Type::Int)],
                Some(Type::Int),
                Expression::BinaryOp(
                    Box::new(Expression::Variable("x".into())),
                    BinaryOp::Add,
                    Box::new(Expression::Variable("y".into())),
                ),
            )],
        );
    }

    #[test]
    fn test_parse_mixed_unit_and_regular_parameters() {
        assert_parse(
            "let f () (x : int) : int = x",
            vec![let_binding(
                "f",
                vec![("()", Type::Unit), ("x", Type::Int)],
                Some(Type::Int),
                Expression::Variable("x".into()),
            )],
        );
    }

    #[test]
    fn test_parse_recursive_let() {
        assert_parse(
            "let rec factorial (n : int) : int = match n with | 0 -> 1 | x -> x * factorial (x - 1)",
            vec![let_binding_rec(
                "factorial",
                vec![],
                vec![("n", Type::Int)],
                Some(Type::Int),
                Expression::Match(
                    Box::new(Expression::Variable("n".into())),
                    vec![
                        (
                            Pattern::Literal(Literal::Int(0)),
                            Expression::Literal(Literal::Int(1)),
                        ),
                        (
                            Pattern::Variable("x".into()),
                            Expression::BinaryOp(
                                Box::new(Expression::Variable("x".into())),
                                BinaryOp::Mul,
                                Box::new(Expression::Application(
                                    Box::new(Expression::Variable("factorial".into())),
                                    vec![Expression::BinaryOp(
                                        Box::new(Expression::Variable("x".into())),
                                        BinaryOp::Sub,
                                        Box::new(Expression::Literal(Literal::Int(1))),
                                    )],
                                )),
                            ),
                        ),
                    ],
                ),
            )],
        );
    }

    #[test]
    fn test_parse_let_with_attribute() {
        assert_parse(
            "let[@reflect] rec len (l : ilist) (n : int) : bool = n = 0",
            vec![let_binding_rec(
                "len",
                vec!["reflect"],
                vec![("l", Type::Named("ilist".to_string())), ("n", Type::Int)],
                Some(Type::Bool),
                Expression::BinaryOp(
                    Box::new(Expression::Variable("n".into())),
                    BinaryOp::Eq,
                    Box::new(Expression::Literal(Literal::Int(0))),
                ),
            )],
        );
    }

    #[test]
    fn test_parse_match_expression() {
        assert_parse(
            "let test (x : int) : bool = match x with | 0 -> true | _ -> false",
            vec![AstNode::LetBinding(LetBinding {
                name: VarName::new("test"),
                attributes: vec![],
                is_recursive: false,
                params: vec![(VarName::new("x"), Type::Int)],
                return_type: Some(Type::Bool),
                body: Expression::Match(
                    Box::new(Expression::Variable("x".into())),
                    vec![
                        (
                            Pattern::Literal(Literal::Int(0)),
                            Expression::Literal(Literal::Bool(true)),
                        ),
                        (Pattern::Wildcard, Expression::Literal(Literal::Bool(false))),
                    ],
                ),
            })],
        );
    }

    #[test]
    fn test_parse_complete_list_len_example() {
        let source = "type ilist = Nil | Cons of int * int list

    let[@reflect] rec len (l : ilist) (n : int) : bool =
    match l with
    | Nil -> n = 0
    | Cons (_, rest) -> len rest (n - 1)";

        let expected = vec![
            AstNode::TypeDeclaration(TypeDecl {
                name: "ilist".to_string(),
                variants: vec![
                    Variant {
                        name: "Nil".to_string(),
                        fields: vec![],
                    },
                    Variant {
                        name: "Cons".to_string(),
                        fields: vec![
                            ("0".to_string(), Type::Int),
                            ("1".to_string(), Type::Named("int list".to_string())),
                        ],
                    },
                ],
                attributes: vec![],
            }),
            AstNode::LetBinding(LetBinding {
                name: VarName::new("len"),
                attributes: vec!["reflect".to_string()],
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
                            Pattern::Constructor(
                                ConstructorName::Simple("Nil".to_string()),
                                vec![],
                            ),
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
            }),
        ];

        assert_parse(source, expected);
    }

    #[test]
    fn test_parse_addition_operator() {
        assert_parse(
            "let test = x + y",
            vec![let_binding(
                "test",
                vec![],
                None,
                Expression::BinaryOp(
                    Box::new(Expression::Variable("x".into())),
                    BinaryOp::Add,
                    Box::new(Expression::Variable("y".into())),
                ),
            )],
        );
    }

    #[test]
    fn test_parse_equality_operator() {
        assert_parse(
            "let test = n = 0",
            vec![let_binding(
                "test",
                vec![],
                None,
                Expression::BinaryOp(
                    Box::new(Expression::Variable("n".into())),
                    BinaryOp::Eq,
                    Box::new(Expression::Literal(Literal::Int(0))),
                ),
            )],
        );
    }

    #[test]
    fn test_parse_inequality_operator() {
        assert_parse(
            "let test = a <> b",
            vec![let_binding(
                "test",
                vec![],
                None,
                Expression::BinaryOp(
                    Box::new(Expression::Variable("a".into())),
                    BinaryOp::Neq,
                    Box::new(Expression::Variable("b".into())),
                ),
            )],
        );
    }

    #[test]
    fn test_parse_function_call_expression() {
        assert_parse(
            "let test = len rest (n - 1)",
            vec![let_binding(
                "test",
                vec![],
                None,
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
            )],
        );
    }

    #[test]
    fn test_parse_parenthesized_expression() {
        assert_parse(
            "let test = (x + y) * z",
            vec![let_binding(
                "test",
                vec![],
                None,
                Expression::BinaryOp(
                    Box::new(Expression::BinaryOp(
                        Box::new(Expression::Variable("x".into())),
                        BinaryOp::Add,
                        Box::new(Expression::Variable("y".into())),
                    )),
                    BinaryOp::Mul,
                    Box::new(Expression::Variable("z".into())),
                ),
            )],
        );
    }

    #[test]
    fn test_parse_variable_expression() {
        assert_parse(
            "let test = myVar",
            vec![let_binding(
                "test",
                vec![],
                None,
                Expression::Variable("myVar".into()),
            )],
        );
    }

    #[test]
    fn test_parse_nullary_constructor_expression() {
        assert_parse(
            "let test = Nil",
            vec![let_binding(
                "test",
                vec![],
                None,
                Expression::Constructor(ConstructorName::Simple("Nil".to_string()), vec![]),
            )],
        );
    }

    #[test]
    fn test_parse_constructor_with_arguments_expression() {
        assert_parse(
            "let test = Cons (1, rest)",
            vec![let_binding(
                "test",
                vec![],
                None,
                Expression::Constructor(
                    ConstructorName::Simple("Cons".to_string()),
                    vec![
                        Expression::Literal(Literal::Int(1)),
                        Expression::Variable("rest".into()),
                    ],
                ),
            )],
        );
    }

    #[test]
    fn test_parse_constructor_patterns() {
        let source =
            "let test (x : ilist) : bool = match x with | Nil -> true | Cons (_, _) -> false";
        let expected = vec![AstNode::LetBinding(LetBinding {
            name: VarName::new("test"),
            attributes: vec![],
            is_recursive: false,
            params: vec![(VarName::new("x"), Type::Named("ilist".to_string()))],
            return_type: Some(Type::Bool),
            body: Expression::Match(
                Box::new(Expression::Variable("x".into())),
                vec![
                    (
                        Pattern::Constructor(ConstructorName::Simple("Nil".to_string()), vec![]),
                        Expression::Literal(Literal::Bool(true)),
                    ),
                    (
                        Pattern::Constructor(
                            ConstructorName::Simple("Cons".to_string()),
                            vec![Pattern::Wildcard, Pattern::Wildcard],
                        ),
                        Expression::Literal(Literal::Bool(false)),
                    ),
                ],
            ),
        })];
        assert_parse(source, expected);
    }

    #[test]
    fn test_parse_lowercase_variable_pattern() {
        let source = "let test (x : int) : bool = match x with | n -> n = 0";

        let expected = vec![AstNode::LetBinding(LetBinding {
            name: VarName::new("test"),
            attributes: vec![],
            is_recursive: false,
            params: vec![(VarName::new("x"), Type::Int)],
            return_type: Some(Type::Bool),
            body: Expression::Match(
                Box::new(Expression::Variable("x".into())),
                vec![(
                    Pattern::Variable("n".into()),
                    Expression::BinaryOp(
                        Box::new(Expression::Variable("n".into())),
                        BinaryOp::Eq,
                        Box::new(Expression::Literal(Literal::Int(0))),
                    ),
                )],
            ),
        })];

        assert_parse(source, expected);
    }

    #[test]
    fn test_parse_qualified_constructor_pattern() {
        let source = "let test (x : int) : bool = match x with | List.Nil -> true | _ -> false";

        let expected = vec![AstNode::LetBinding(LetBinding {
            name: VarName::new("test"),
            attributes: vec![],
            is_recursive: false,
            params: vec![(VarName::new("x"), Type::Int)],
            return_type: Some(Type::Bool),
            body: Expression::Match(
                Box::new(Expression::Variable("x".into())),
                vec![
                    (
                        Pattern::Constructor(
                            ConstructorName::Qualified {
                                module: "List".to_string(),
                                name: "Nil".to_string(),
                            },
                            vec![],
                        ),
                        Expression::Literal(Literal::Bool(true)),
                    ),
                    (Pattern::Wildcard, Expression::Literal(Literal::Bool(false))),
                ],
            ),
        })];

        assert_parse(source, expected);
    }

    #[test]
    fn test_parse_parenthesized_single_pattern() {
        let source = "let test (x : int) : bool = match x with | (0) -> true | _ -> false";

        let expected = vec![AstNode::LetBinding(LetBinding {
            name: VarName::new("test"),
            attributes: vec![],
            is_recursive: false,
            params: vec![(VarName::new("x"), Type::Int)],
            return_type: Some(Type::Bool),
            body: Expression::Match(
                Box::new(Expression::Variable("x".into())),
                vec![
                    (
                        Pattern::Literal(Literal::Int(0)),
                        Expression::Literal(Literal::Bool(true)),
                    ),
                    (Pattern::Wildcard, Expression::Literal(Literal::Bool(false))),
                ],
            ),
        })];

        assert_parse(source, expected);
    }

    #[test]
    fn test_parse_let_with_single_attribute() {
        assert_parse(
            "let[@simp] test (x : int) : bool = true",
            vec![AstNode::LetBinding(LetBinding {
                name: VarName::new("test"),
                attributes: vec!["simp".to_string()],
                is_recursive: false,
                params: vec![(VarName::new("x"), Type::Int)],
                return_type: Some(Type::Bool),
                body: Expression::Literal(Literal::Bool(true)),
            })],
        );
    }

    #[test]
    fn test_parse_let_with_multiple_attributes() {
        assert_parse(
            "let[@simp][@grind] test (x : int) : bool = true",
            vec![AstNode::LetBinding(LetBinding {
                name: VarName::new("test"),
                attributes: vec!["simp".to_string(), "grind".to_string()],
                is_recursive: false,
                params: vec![(VarName::new("x"), Type::Int)],
                return_type: Some(Type::Bool),
                body: Expression::Literal(Literal::Bool(true)),
            })],
        );
    }

    #[test]
    fn test_parse_recursive_let_with_attributes() {
        assert_parse(
            "let[@reflect] rec fib (n : int) : int = match n with | 0 -> 0 | 1 -> 1 | x -> fib (x - 1)",
            vec![let_binding_rec(
                "fib",
                vec!["reflect"],
                vec![("n", Type::Int)],
                Some(Type::Int),
                Expression::Match(
                    Box::new(Expression::Variable("n".into())),
                    vec![
                        (
                            Pattern::Literal(Literal::Int(0)),
                            Expression::Literal(Literal::Int(0)),
                        ),
                        (
                            Pattern::Literal(Literal::Int(1)),
                            Expression::Literal(Literal::Int(1)),
                        ),
                        (
                            Pattern::Variable("x".into()),
                            Expression::Application(
                                Box::new(Expression::Variable("fib".into())),
                                vec![Expression::BinaryOp(
                                    Box::new(Expression::Variable("x".into())),
                                    BinaryOp::Sub,
                                    Box::new(Expression::Literal(Literal::Int(1))),
                                )],
                            ),
                        ),
                    ],
                ),
            )],
        );
    }

    #[test]
    fn test_parse_type_with_attributes_and_value_definition_with_attributes() {
        let source = "type[@simp] ilist = Nil | Cons of int * int list
let[@grind] rec len (l : ilist) : int = match l with | Nil -> 0 | Cons (_, rest) -> 1 + len rest";

        let expected = vec![
            AstNode::TypeDeclaration(TypeDecl {
                name: "ilist".to_string(),
                variants: vec![
                    Variant {
                        name: "Nil".to_string(),
                        fields: vec![],
                    },
                    Variant {
                        name: "Cons".to_string(),
                        fields: vec![
                            ("0".to_string(), Type::Int),
                            ("1".to_string(), Type::Named("int list".to_string())),
                        ],
                    },
                ],
                attributes: vec!["simp".to_string()],
            }),
            AstNode::LetBinding(LetBinding {
                name: VarName::new("len"),
                attributes: vec!["grind".to_string()],
                is_recursive: true,
                params: vec![(VarName::new("l"), Type::Named("ilist".to_string()))],
                return_type: Some(Type::Int),
                body: Expression::Match(
                    Box::new(Expression::Variable("l".into())),
                    vec![
                        (
                            Pattern::Constructor(
                                ConstructorName::Simple("Nil".to_string()),
                                vec![],
                            ),
                            Expression::Literal(Literal::Int(0)),
                        ),
                        (
                            Pattern::Constructor(
                                ConstructorName::Simple("Cons".to_string()),
                                vec![Pattern::Wildcard, Pattern::Variable("rest".into())],
                            ),
                            Expression::BinaryOp(
                                Box::new(Expression::Literal(Literal::Int(1))),
                                BinaryOp::Add,
                                Box::new(Expression::Application(
                                    Box::new(Expression::Variable("len".into())),
                                    vec![Expression::Variable("rest".into())],
                                )),
                            ),
                        ),
                    ],
                ),
            }),
        ];

        assert_parse(source, expected);
    }

    #[test]
    fn test_parse_ite_as_variable_application() {
        // Test ite parsed as variable being applied (from tree example)
        assert_parse(
            "let[@simp] rec height (t : tree) : int = match t with | Leaf -> 0 | Node (v, l, r) -> 1 + ite (height l > height r) (height l) (height r)",
            vec![let_binding_rec(
                "height",
                vec!["simp"],
                vec![("t", Type::Named("tree".to_string()))],
                Some(Type::Int),
                Expression::Match(
                    Box::new(Expression::Variable("t".into())),
                    vec![
                        (
                            Pattern::Constructor(
                                ConstructorName::Simple("Leaf".to_string()),
                                vec![],
                            ),
                            Expression::Literal(Literal::Int(0)),
                        ),
                        (
                            Pattern::Constructor(
                                ConstructorName::Simple("Node".to_string()),
                                vec![
                                    Pattern::Variable("v".into()),
                                    Pattern::Variable("l".into()),
                                    Pattern::Variable("r".into()),
                                ],
                            ),
                            Expression::BinaryOp(
                                Box::new(Expression::Literal(Literal::Int(1))),
                                BinaryOp::Add,
                                Box::new(Expression::IfThenElse {
                                    condition: Box::new(Expression::BinaryOp(
                                        Box::new(Expression::Application(
                                            Box::new(Expression::Variable("height".into())),
                                            vec![Expression::Variable("l".into())],
                                        )),
                                        BinaryOp::Gt,
                                        Box::new(Expression::Application(
                                            Box::new(Expression::Variable("height".into())),
                                            vec![Expression::Variable("r".into())],
                                        )),
                                    )),
                                    then_branch: Box::new(Expression::Application(
                                        Box::new(Expression::Variable("height".into())),
                                        vec![Expression::Variable("l".into())],
                                    )),
                                    else_branch: Box::new(Expression::Application(
                                        Box::new(Expression::Variable("height".into())),
                                        vec![Expression::Variable("r".into())],
                                    )),
                                }),
                            ),
                        ),
                    ],
                ),
            )],
        );
    }

    #[test]
    fn test_parse_ite_as_constructor() {
        // Test ite parsed as constructor with arguments
        assert_parse(
            "let test = ite true 1 2",
            vec![let_binding(
                "test",
                vec![],
                None,
                Expression::IfThenElse {
                    condition: Box::new(Expression::Literal(Literal::Bool(true))),
                    then_branch: Box::new(Expression::Literal(Literal::Int(1))),
                    else_branch: Box::new(Expression::Literal(Literal::Int(2))),
                },
            )],
        );
    }
    #[test]
    fn test_parse_if_then_else_with_comparison() {
        assert_parse(
            "let test (x : int) : int = if x = 0 then 0 else x",
            vec![AstNode::LetBinding(LetBinding {
                name: VarName::new("test"),
                attributes: vec![],
                is_recursive: false,
                params: vec![(VarName::new("x"), Type::Int)],
                return_type: Some(Type::Int),
                body: Expression::IfThenElse {
                    condition: Box::new(Expression::BinaryOp(
                        Box::new(Expression::Variable("x".into())),
                        BinaryOp::Eq,
                        Box::new(Expression::Literal(Literal::Int(0))),
                    )),
                    then_branch: Box::new(Expression::Literal(Literal::Int(0))),
                    else_branch: Box::new(Expression::Variable("x".into())),
                },
            })],
        );
    }

    #[test]
    fn test_parse_match_enforces_pipe_separator() {
        // All match cases must be preceded by |
        assert_parse(
            "let test (x : int) : int = match x with | 0 -> 1 | 1 -> 2 | _ -> 3",
            vec![let_binding(
                "test",
                vec![("x", Type::Int)],
                Some(Type::Int),
                Expression::Match(
                    Box::new(Expression::Variable("x".into())),
                    vec![
                        (
                            Pattern::Literal(Literal::Int(0)),
                            Expression::Literal(Literal::Int(1)),
                        ),
                        (
                            Pattern::Literal(Literal::Int(1)),
                            Expression::Literal(Literal::Int(2)),
                        ),
                        (Pattern::Wildcard, Expression::Literal(Literal::Int(3))),
                    ],
                ),
            )],
        );
    }

    #[test]
    fn test_parse_match_single_case() {
        // Even single case must have pipe
        assert_parse(
            "let test (x : bool) : int = match x with | true -> 42",
            vec![let_binding(
                "test",
                vec![("x", Type::Bool)],
                Some(Type::Int),
                Expression::Match(
                    Box::new(Expression::Variable("x".into())),
                    vec![(
                        Pattern::Literal(Literal::Bool(true)),
                        Expression::Literal(Literal::Int(42)),
                    )],
                ),
            )],
        );
    }

    #[test]
    fn test_parse_num_black() {
        let source = "let[@simp] [@grind] rec num_black (t : rbtree) (h : int) : bool =
      match t with
      | Rbtleaf -> h = 0
      | Rbtnode (c, l, _, r) ->
          if c then num_black l (h - 1) && num_black r (h - 1)
          else num_black l h && num_black r h";

        let expected = vec![let_binding_rec(
            "num_black",
            vec!["simp", "grind"],
            vec![("t", Type::Named("rbtree".to_string())), ("h", Type::Int)],
            Some(Type::Bool),
            Expression::Match(
                Box::new(Expression::Variable("t".into())),
                vec![
                    (
                        Pattern::Constructor(
                            ConstructorName::Simple("Rbtleaf".to_string()),
                            vec![],
                        ),
                        Expression::BinaryOp(
                            Box::new(Expression::Variable("h".into())),
                            BinaryOp::Eq,
                            Box::new(Expression::Literal(Literal::Int(0))),
                        ),
                    ),
                    (
                        Pattern::Constructor(
                            ConstructorName::Simple("Rbtnode".to_string()),
                            vec![
                                Pattern::Variable("c".into()),
                                Pattern::Variable("l".into()),
                                Pattern::Wildcard,
                                Pattern::Variable("r".into()),
                            ],
                        ),
                        Expression::IfThenElse {
                            condition: Box::new(Expression::Variable("c".into())),
                            then_branch: Box::new(Expression::BinaryOp(
                                Box::new(Expression::Application(
                                    Box::new(Expression::Variable("num_black".into())),
                                    vec![
                                        Expression::Variable("l".into()),
                                        Expression::BinaryOp(
                                            Box::new(Expression::Variable("h".into())),
                                            BinaryOp::Sub,
                                            Box::new(Expression::Literal(Literal::Int(1))),
                                        ),
                                    ],
                                )),
                                BinaryOp::And,
                                Box::new(Expression::Application(
                                    Box::new(Expression::Variable("num_black".into())),
                                    vec![
                                        Expression::Variable("r".into()),
                                        Expression::BinaryOp(
                                            Box::new(Expression::Variable("h".into())),
                                            BinaryOp::Sub,
                                            Box::new(Expression::Literal(Literal::Int(1))),
                                        ),
                                    ],
                                )),
                            )),
                            else_branch: Box::new(Expression::BinaryOp(
                                Box::new(Expression::Application(
                                    Box::new(Expression::Variable("num_black".into())),
                                    vec![
                                        Expression::Variable("l".into()),
                                        Expression::Variable("h".into()),
                                    ],
                                )),
                                BinaryOp::And,
                                Box::new(Expression::Application(
                                    Box::new(Expression::Variable("num_black".into())),
                                    vec![
                                        Expression::Variable("r".into()),
                                        Expression::Variable("h".into()),
                                    ],
                                )),
                            )),
                        },
                    ),
                ],
            ),
        )];

        assert_parse(source, expected);
    }

    #[test]
    fn test_parse_rb_root_color() {
        let source = "let[@simp] [@grind] rec rb_root_color (t : rbtree) (c : bool) : bool =
      match t with Rbtleaf -> false | Rbtnode (c', _, _, _) -> c = c'";

        let expected = vec![let_binding_rec(
            "rb_root_color",
            vec!["simp", "grind"],
            vec![("t", Type::Named("rbtree".to_string())), ("c", Type::Bool)],
            Some(Type::Bool),
            Expression::Match(
                Box::new(Expression::Variable("t".into())),
                vec![
                    (
                        Pattern::Constructor(
                            ConstructorName::Simple("Rbtleaf".to_string()),
                            vec![],
                        ),
                        Expression::Literal(Literal::Bool(false)),
                    ),
                    (
                        Pattern::Constructor(
                            ConstructorName::Simple("Rbtnode".to_string()),
                            vec![
                                Pattern::Variable("c'".into()),
                                Pattern::Wildcard,
                                Pattern::Wildcard,
                                Pattern::Wildcard,
                            ],
                        ),
                        Expression::BinaryOp(
                            Box::new(Expression::Variable("c".into())),
                            BinaryOp::Eq,
                            Box::new(Expression::Variable("c'".into())),
                        ),
                    ),
                ],
            ),
        )];

        assert_parse(source, expected);
    }

    #[test]
    fn test_parse_rbdepth() {
        let source = "let[@simp] [@grind] rec rbdepth (t : rbtree) : int =
      match t with
      | Rbtleaf -> 0
      | Rbtnode (_, l, _, r) -> 1 + ite (rbdepth l > rbdepth r) (rbdepth l) (rbdepth r)";

        let expected = vec![let_binding_rec(
            "rbdepth",
            vec!["simp", "grind"],
            vec![("t", Type::Named("rbtree".to_string()))],
            Some(Type::Int),
            Expression::Match(
                Box::new(Expression::Variable("t".into())),
                vec![
                    (
                        Pattern::Constructor(
                            ConstructorName::Simple("Rbtleaf".to_string()),
                            vec![],
                        ),
                        Expression::Literal(Literal::Int(0)),
                    ),
                    (
                        Pattern::Constructor(
                            ConstructorName::Simple("Rbtnode".to_string()),
                            vec![
                                Pattern::Wildcard,
                                Pattern::Variable("l".into()),
                                Pattern::Wildcard,
                                Pattern::Variable("r".into()),
                            ],
                        ),
                        Expression::BinaryOp(
                            Box::new(Expression::Literal(Literal::Int(1))),
                            BinaryOp::Add,
                            Box::new(Expression::IfThenElse {
                                condition: Box::new(Expression::BinaryOp(
                                    Box::new(Expression::Application(
                                        Box::new(Expression::Variable("rbdepth".into())),
                                        vec![Expression::Variable("l".into())],
                                    )),
                                    BinaryOp::Gt,
                                    Box::new(Expression::Application(
                                        Box::new(Expression::Variable("rbdepth".into())),
                                        vec![Expression::Variable("r".into())],
                                    )),
                                )),
                                then_branch: Box::new(Expression::Application(
                                    Box::new(Expression::Variable("rbdepth".into())),
                                    vec![Expression::Variable("l".into())],
                                )),
                                else_branch: Box::new(Expression::Application(
                                    Box::new(Expression::Variable("rbdepth".into())),
                                    vec![Expression::Variable("r".into())],
                                )),
                            }),
                        ),
                    ),
                ],
            ),
        )];

        assert_parse(source, expected);
    }

    #[test]
    fn test_parse_fun_expression_simple_body() {
        // fun_expression should extract and return only the body expression
        // Parameters in fun expressions are currently skipped (handled at LetBinding level)
        let source = "let f = fun x -> x + 1";

        let expected = vec![let_binding(
            "f",
            vec![],
            None,
            Expression::BinaryOp(
                Box::new(Expression::Variable("x".into())),
                BinaryOp::Add,
                Box::new(Expression::Literal(Literal::Int(1))),
            ),
        )];

        assert_parse(source, expected);
    }

    #[test]
    fn test_parse_fun_expression_with_let_binding_params() {
        // When both let binding and fun expression have parameters,
        // this tests that fun_expression correctly extracts the body
        // Note: This is a degenerate case - normally you'd use:
        //   let rec len (l : ilist) : int = match l with ...
        // Rather than:
        //   let rec len = fun l -> match l with ...
        let source = "let rec len (l : ilist) : int = fun x -> x";

        let expected = vec![let_binding_rec(
            "len",
            vec![],
            vec![("l", Type::Named("ilist".to_string()))],
            Some(Type::Int),
            Expression::Variable("x".into()),
        )];

        assert_parse(source, expected);
    }

    #[test]
    fn test_parse_fun_expression_multiple_params() {
        // Test with multiple parameters before arrow
        let source = "let add = fun x y -> x + y";

        let expected = vec![let_binding(
            "add",
            vec![],
            None,
            Expression::BinaryOp(
                Box::new(Expression::Variable("x".into())),
                BinaryOp::Add,
                Box::new(Expression::Variable("y".into())),
            ),
        )];

        assert_parse(source, expected);
    }

    #[test]
    #[should_panic(expected = "Nested fun expressions")]
    fn test_parse_fun_expression_nested() {
        // Test that nested fun expressions are rejected with a clear error
        let source = "let curry = fun x -> fun y -> x + y";

        // This should panic with a descriptive error message about the limitation
        let _ = OcamlParser::parse_nodes(source);
    }
}

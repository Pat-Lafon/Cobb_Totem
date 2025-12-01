use crate::{
    VarName,
    prog_ir::{
        AstNode, BinaryOp, ConstructorName, Expression, LetBinding, Literal, Pattern, Type,
        TypeDecl, Variant,
    },
};
use tree_sitter::Node;

pub struct OcamlParser {
    source: String,
}

impl OcamlParser {
    pub fn new(source: String) -> Self {
        OcamlParser { source }
    }

    pub fn parse_source(
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
    pub fn parse_nodes(source: &str) -> Result<Vec<AstNode>, Box<dyn std::error::Error>> {
        let (parser, tree) = Self::parse_source(source)?;
        parser.parse(&tree)
    }

    // Example: "int", "int list", "string * bool"
    fn parse_type(&self, node: Node) -> Type {
        let text = node
            .utf8_text(self.source.as_bytes())
            .expect("Failed to extract text from type node");
        text.parse().expect("Failed to parse type")
    }

    /// Helper: moves cursor to parent and asserts success.
    fn restore_cursor(cursor: &mut tree_sitter::TreeCursor, context: &str) {
        assert!(
            cursor.goto_parent(),
            "Failed to restore cursor to {} parent",
            context
        );
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
                    "typed_pattern has no children"
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
                    .expect("Failed to extract parameter name")
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
                _ => {
                    unimplemented!()
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
            let mut expect_constructor = !cursor.node().kind().eq("|");

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

        // Parse first field
        let child = cursor.node();
        assert!(
            child.kind() == "type_constructor_path" || child.kind() == "constructed_type",
            "Expected field, got '{}'",
            child.kind()
        );
        fields.push(self.parse_type(child));

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
                    fields.push(self.parse_type(field));
                }
                kind => {
                    panic!("Expected separator, got '{}'", kind);
                }
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
            .expect("Failed to extract number text");
        text.trim()
            .parse::<i32>()
            .map(Literal::Int)
            .unwrap_or_else(|_| panic!("Failed to parse number: '{}'", text))
    }

    fn parse_boolean_from_node(&self, node: Node) -> Literal {
        let text = node
            .utf8_text(self.source.as_bytes())
            .expect("Failed to extract boolean text");
        match text.trim() {
            "true" => Literal::Bool(true),
            "false" => Literal::Bool(false),
            s => panic!("Expected 'true' or 'false', got '{}'", s),
        }
    }

    fn parse_expression(&self, node: Node) -> Expression {
        match node.kind() {
            "match_expression" => self.parse_match_expression_node(node),
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
                let valid_var = text.chars().all(|c| c.is_alphanumeric() || c == '_')
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
            Expression::Variable(_) | Expression::Application(_, _) | Expression::Match(_, _) => {
                Expression::Application(Box::new(func), args)
            }
            Expression::Literal(_)
            | Expression::UnaryOp(_, _)
            | Expression::BinaryOp(_, _, _)
            | Expression::Tuple(_) => {
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
        while cursor.goto_next_sibling() {
            let child = cursor.node();
            assert_eq!(child.kind(), "|", "Expected '|', got '{}'", child.kind());
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
                    fields: vec![Type::Int, Type::Named("int list".to_string())],
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
                    fields: vec![Type::Int, Type::Named("int list".to_string())],
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
                    fields: vec![Type::Int, Type::Named("int list".to_string())],
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
                fields: vec![Type::Int, Type::Named("ilist".to_string()), Type::Bool],
            }],
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
                        fields: vec![Type::Int, Type::Named("int list".to_string())],
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
}

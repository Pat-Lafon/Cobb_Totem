use crate::{AstNode, LetBinding, LetBindingBody, PatternCase, Type, TypeDecl, Variant};
use tree_sitter::Node;

pub struct OcamlParser {
    source: String,
}

impl OcamlParser {
    pub fn new(source: String) -> Self {
        OcamlParser { source }
    }

    // Example: "int", "int list", "string * bool"
    fn parse_type(&self, node: Node) -> Result<Type, String> {
        let text = node
            .utf8_text(self.source.as_bytes())
            .map_err(|e| format!("Failed to extract text from type node: {}", e))?;
        text.parse()
    }

    pub fn parse(
        &self,
        tree: &tree_sitter::Tree,
    ) -> Result<Vec<AstNode>, Box<dyn std::error::Error>> {
        let mut nodes = Vec::new();
        let mut cursor = tree.walk();

        for child in tree.root_node().children(&mut cursor) {
            match child.kind() {
                "type_definition" => match self.parse_type_definition(child) {
                    Ok(type_decl) => nodes.push(AstNode::TypeDeclaration(type_decl)),
                    Err(e) => return Err(format!("Failed to parse type definition: {}", e).into()),
                },
                "value_definition" => match self.parse_value_definition(child) {
                    Ok(let_binding) => nodes.push(AstNode::LetBinding(let_binding)),
                    Err(e) => return Err(format!("Failed to parse value definition: {}", e).into()),
                },
                _ => {
                    unimplemented!()
                }
            }
        }

        Ok(nodes)
    }

    // Example: "type ilist = Nil | Cons of int * int list"
    fn parse_type_definition(&self, node: Node) -> Result<TypeDecl, String> {
        let mut cursor = node.walk();
        let mut children = node.children(&mut cursor);

        let type_keyword = children
            .next()
            .ok_or("Type definition missing 'type' keyword")?;
        if type_keyword.kind() != "type" {
            return Err(format!("Expected 'type', got '{}'", type_keyword.kind()));
        }

        let type_binding = children
            .next()
            .ok_or("Type definition missing type_binding")?;
        if type_binding.kind() != "type_binding" {
            return Err(format!(
                "Expected 'type_binding', got '{}'",
                type_binding.kind()
            ));
        }

        assert!(children.next().is_none());

        self.parse_type_binding(type_binding)
    }

    // Example: "ilist = Nil | Cons of int * int list"
    fn parse_type_binding(&self, node: Node) -> Result<TypeDecl, String> {
        let mut cursor = node.walk();
        let mut children = node.children(&mut cursor);

        let type_constructor = children
            .next()
            .ok_or("Type binding missing type_constructor")?;
        if type_constructor.kind() != "type_constructor" {
            return Err(format!(
                "Expected 'type_constructor', got '{}'",
                type_constructor.kind()
            ));
        }

        let name = type_constructor
            .utf8_text(self.source.as_bytes())
            .map_err(|e| format!("Failed to extract type constructor name: {}", e))?
            .to_string();

        let equals = children.next().ok_or("Type binding missing '='")?;
        if equals.kind() != "=" {
            return Err(format!("Expected '=', got '{}'", equals.kind()));
        }

        let variant_decl = children
            .next()
            .ok_or("Type binding missing variant_declaration")?;
        if variant_decl.kind() != "variant_declaration" {
            return Err(format!(
                "Expected 'variant_declaration', got '{}'",
                variant_decl.kind()
            ));
        }

        let mut variants = Vec::new();
        let mut variant_cursor = variant_decl.walk();
        for variant_child in variant_decl.children(&mut variant_cursor) {
            if variant_child.kind() == "|" {
                continue;
            }
            assert_eq!(variant_child.kind(), "constructor_declaration");
            variants.push(self.parse_constructor_declaration(variant_child)?);
        }

        assert!(children.next().is_none());

        Ok(TypeDecl { name, variants })
    }

    // Example: "Nil" or "Cons of int * int list"
    fn parse_constructor_declaration(&self, node: Node) -> Result<Variant, String> {
        let mut cursor = node.walk();
        let mut children = node.children(&mut cursor);

        let constructor_name = children
            .next()
            .ok_or("Constructor declaration missing constructor_name")?;
        if constructor_name.kind() != "constructor_name" {
            return Err(format!(
                "Expected 'constructor_name', got '{}'",
                constructor_name.kind()
            ));
        }

        let name = constructor_name
            .utf8_text(self.source.as_bytes())
            .map_err(|e| format!("Failed to extract constructor name: {}", e))?
            .to_string();

        match children.next() {
            Some(next) if next.kind() == "of" => {
                let mut fields = Vec::new();
                for child in children {
                    match child.kind() {
                        "type_constructor_path" | "constructed_type" => {
                            fields.push(self.parse_type(child)?);
                        }
                        "*" => continue,
                        _ => {
                            return Err(format!(
                                "Unexpected token in constructor fields: {}",
                                child.kind()
                            ));
                        }
                    }
                }
                Ok(Variant { name, fields })
            }
            None => Ok(Variant {
                name,
                fields: vec![],
            }),
            Some(next) => Err(format!(
                "Expected 'of' or end of constructor, got '{}'",
                next.kind()
            )),
        }
    }

    // Example: "let rec len (l : ilist) (n : int) : bool = match l with ..."
    fn parse_value_definition(&self, node: Node) -> Result<LetBinding, String> {
        let mut cursor = node.walk();
        let mut name = String::new();
        let mut attributes = Vec::new();
        let mut is_recursive = false;
        let mut params = Vec::new();
        let mut return_type = None;
        let mut body = LetBindingBody::Expression(String::new());

        for child in node.children(&mut cursor) {
            match child.kind() {
                "attribute" => {
                    attributes.push(
                        child
                            .utf8_text(self.source.as_bytes())
                            .map_err(|e| format!("Failed to extract attribute: {}", e))?
                            .to_string(),
                    );
                }
                "rec" => {
                    is_recursive = true;
                }
                "let_binding" => {
                    let mut binding_cursor = child.walk();
                    let mut binding_children = child.children(&mut binding_cursor);

                    // First child should be value_name
                    let value_name_node = binding_children
                        .next()
                        .ok_or("Let binding missing value_name")?;
                    if value_name_node.kind() != "value_name" {
                        return Err(format!(
                            "Expected 'value_name', got '{}'",
                            value_name_node.kind()
                        ));
                    }
                    name = value_name_node
                        .utf8_text(self.source.as_bytes())
                        .map_err(|e| format!("Failed to extract value name: {}", e))?
                        .to_string();

                    // Phase 1: Collect all parameters
                    for binding_child in binding_children
                        .by_ref()
                        .take_while(|child| child.kind() == "parameter")
                    {
                        let text = binding_child
                            .utf8_text(self.source.as_bytes())
                            .map_err(|e| format!("Failed to extract parameter: {}", e))?;
                        params.push((text.to_string(), None));
                    }

                    // Phase 2: Handle optional return type and required body
                    if let Some(binding_child) = binding_children.next() {
                        // Check for return type
                        if binding_child.kind() == ":" {
                            let type_node = binding_children.next().ok_or(
                                "Return type annotation missing type after ':'".to_string(),
                            )?;
                            if type_node.kind() != "type_constructor_path"
                                && type_node.kind() != "constructed_type"
                            {
                                return Err(format!(
                                    "Expected type after ':', got '{}'",
                                    type_node.kind()
                                ));
                            }
                            return_type = Some(self.parse_type(type_node)?);

                            // After return type, expect '='
                            let eq = binding_children
                                .next()
                                .ok_or("Expected '=' after return type".to_string())?;
                            if eq.kind() != "=" {
                                return Err(format!("Expected '=', got '{}'", eq.kind()));
                            }
                        } else if binding_child.kind() == "type_constructor_path"
                            || binding_child.kind() == "constructed_type"
                        {
                            // Return type comes directly without ':' prefix
                            return_type = Some(self.parse_type(binding_child)?);

                            // After return type, expect '='
                            let eq = binding_children
                                .next()
                                .ok_or("Expected '=' after return type".to_string())?;
                            if eq.kind() != "=" {
                                return Err(format!("Expected '=', got '{}'", eq.kind()));
                            }
                        } else if binding_child.kind() != "=" {
                            return Err(format!(
                                "Expected ':' or '=' after parameters, got '{}'",
                                binding_child.kind()
                            ));
                        }

                        // Phase 3: Parse body
                        let body_node = binding_children
                            .next()
                            .ok_or("Let binding missing body expression")?;
                        body = self.parse_body_node(body_node)?;
                    }
                }
                _ => {}
            }
        }

        if name.is_empty() {
            return Err("Let binding must have a name".to_string());
        }

        Ok(LetBinding {
            name,
            attributes,
            is_recursive,
            params,
            return_type,
            body,
        })
    }

    fn parse_body_node(&self, node: Node) -> Result<LetBindingBody, String> {
        match node.kind() {
            "match_expression" => self.parse_match_expression_node(node),
            _ => {
                // For any other expression, extract the text
                let expr_text = node
                    .utf8_text(self.source.as_bytes())
                    .map_err(|e| format!("Failed to extract expression text: {}", e))?
                    .to_string();
                Ok(LetBindingBody::Expression(expr_text))
            }
        }
    }

    fn parse_match_expression_node(&self, node: Node) -> Result<LetBindingBody, String> {
        let mut cursor = node.walk();
        let mut children = node.children(&mut cursor);

        let match_keyword = children
            .next()
            .ok_or("Match expression missing 'match' keyword")?;
        if match_keyword.kind() != "match" {
            return Err(format!("Expected 'match', got '{}'", match_keyword.kind()));
        }

        // Next should be the scrutinee (value being matched)
        let scrutinee_node = children
            .next()
            .ok_or("Match expression missing scrutinee")?;
        let scrutinee = scrutinee_node
            .utf8_text(self.source.as_bytes())
            .map_err(|e| format!("Failed to extract scrutinee: {}", e))?
            .to_string();

        let with_keyword = children
            .next()
            .ok_or("Match expression missing 'with' keyword")?;
        if with_keyword.kind() != "with" {
            return Err(format!("Expected 'with', got '{}'", with_keyword.kind()));
        }

        let mut cases = Vec::new();

        // Collect all match cases
        for child in children {
            match child.kind() {
                "match_case" => {
                    let case = self.parse_match_case(child)?;
                    cases.push(case);
                }
                "|" => {
                    // Separator between cases, skip it
                    continue;
                }
                _ => {}
            }
        }

        Ok(LetBindingBody::PatternMatch(scrutinee, cases))
    }

    fn parse_match_case(&self, node: Node) -> Result<PatternCase, String> {
        let mut cursor = node.walk();
        let mut children = node.children(&mut cursor);

        // Pattern is the first child (could be various types)
        let pattern_node = children.next().ok_or("Match case missing pattern")?;
        let pattern = pattern_node
            .utf8_text(self.source.as_bytes())
            .map_err(|e| format!("Failed to extract pattern: {}", e))?
            .to_string();

        // Look for the arrow
        let arrow = children.next().ok_or("Match case missing '->'")?;
        if arrow.kind() != "->" {
            return Err(format!("Expected '->', got '{}'", arrow.kind()));
        }

        // Body is the remaining text after the arrow
        let body_node = children.next().ok_or("Match case missing body")?;
        let body = body_node
            .utf8_text(self.source.as_bytes())
            .map_err(|e| format!("Failed to extract case body: {}", e))?
            .to_string();

        Ok(PatternCase { pattern, body })
    }
}

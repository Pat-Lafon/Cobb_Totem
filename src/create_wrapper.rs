use crate::{
    VarName,
    prog_ir::{AstNode, BinaryOp, Expression, LetBinding, Type},
};

/// Generate a wrapper function that checks `f(...params) == res` for a given function
pub fn create_wrapper(binding: &LetBinding) -> AstNode {
    const RESULT_PARAM: &str = "res";

    assert!(
        !binding.params.is_empty(),
        "Function must have at least one parameter"
    );
    let return_type = binding
        .return_type
        .clone()
        .expect("Function must have a return type");

    let wrapper_name = format!("{}_wrapper", binding.name.as_str());

    // Create function arguments from all original parameters
    let arg_exprs: Vec<Expression> = binding
        .params
        .iter()
        .map(|(param_name, _)| Expression::Variable(param_name.clone()))
        .collect();

    // Build the wrapper parameters: all original params + result param
    let mut wrapper_params = binding.params.clone();
    wrapper_params.push((VarName::new(RESULT_PARAM), return_type.clone()));

    AstNode::LetBinding(LetBinding {
        name: VarName::new(wrapper_name),
        attributes: binding.attributes.clone(),
        is_recursive: false,
        params: wrapper_params,
        return_type: Some(Type::Bool),
        body: Expression::BinaryOp(
            Box::new(Expression::Application(
                Box::new(Expression::Variable(binding.name.clone())),
                arg_exprs,
            )),
            BinaryOp::Eq,
            Box::new(Expression::Variable(VarName::new(RESULT_PARAM))),
        ),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lean_backend::LeanContextBuilder;
    use crate::ocamlparser::OcamlParser;

    #[test]
    fn test_transform_length_function() {
        let ocaml_src = "let[@simp][@grind] rec len (l : ilist) : int = match l with | Nil -> 0 | Cons(_, tl) -> 1 + len tl";
        let binding = match OcamlParser::parse_nodes(ocaml_src) {
            Ok(nodes) => match &nodes[0] {
                crate::prog_ir::AstNode::LetBinding(b) => b.clone(),
                _ => panic!("Expected LetBinding"),
            },
            Err(e) => panic!("Failed to parse OCaml: {}", e),
        };

        let transformed = create_wrapper(&binding);

        let lean_code = LeanContextBuilder::new()
            .with_nodes(vec![transformed])
            .build();

        let expected = r#"@[simp, grind]
def len_wrapper (l : ilist) (res : Int) : Bool := (len l == res)"#;

        assert_eq!(lean_code.trim(), expected);
    }

    #[test]
    fn test_transform_multi_parameter_function() {
        let ocaml_src = "let[@simp] add (x : int) (y : int) : int = x + y";
        let binding = match OcamlParser::parse_nodes(ocaml_src) {
            Ok(nodes) => match &nodes[0] {
                crate::prog_ir::AstNode::LetBinding(b) => b.clone(),
                _ => panic!("Expected LetBinding"),
            },
            Err(e) => panic!("Failed to parse OCaml: {}", e),
        };

        let transformed = create_wrapper(&binding);

        let lean_code = LeanContextBuilder::new()
            .with_nodes(vec![transformed])
            .build();

        let expected = r#"@[simp]
def add_wrapper (x : Int) (y : Int) (res : Int) : Bool := (add x y == res)"#;

        assert_eq!(lean_code.trim(), expected);
    }

    #[test]
    fn test_transform_alternative_return_type() {
        let ocaml_src =
            "let[@simp] is_empty (l : ilist) : bool = match l with | Nil -> true | _ -> false";
        let binding = match OcamlParser::parse_nodes(ocaml_src) {
            Ok(nodes) => match &nodes[0] {
                crate::prog_ir::AstNode::LetBinding(b) => b.clone(),
                _ => panic!("Expected LetBinding"),
            },
            Err(e) => panic!("Failed to parse OCaml: {}", e),
        };

        let transformed = create_wrapper(&binding);

        let lean_code = LeanContextBuilder::new()
            .with_nodes(vec![transformed])
            .build();

        let expected = r#"@[simp]
def is_empty_wrapper (l : ilist) (res : Bool) : Bool := (is_empty l == res)"#;

        assert_eq!(lean_code.trim(), expected);
    }
}

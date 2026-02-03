use crate::{
    VarName,
    prog_ir::{BinaryOp, Expression, LetBinding, Type},
};

/// Result parameter name used in wrapper functions
pub(crate) const RESULT_PARAM: &str = "res";

/// Generate the impl function name for a given function name
fn impl_name(name: &VarName) -> VarName {
    VarName(format!("{}_impl", name.0))
}

/// Create both impl and wrapper functions for a predicate that needs wrapping.
/// Returns (impl_function, wrapper_function).
/// The impl function has the original logic but renamed to `{name}_impl`.
/// The wrapper function defines a predicate that checks `impl(...) == res`.
pub(crate) fn create_and_wrap_predicate(binding: &LetBinding) -> (LetBinding, LetBinding) {
    assert!(
        binding.return_type.is_some(),
        "Function must have a return type to be wrapped"
    );

    let original_name = binding.name.clone();
    let impl_fn_name = impl_name(&original_name);

    // Create impl function: rename the original function to _impl and update all function calls
    let mut impl_binding = binding.clone();
    impl_binding.name = impl_fn_name.clone();
    impl_binding.body = rename_function_calls_in(&impl_binding.body);

    let mut wrapper_attributes = binding.attributes.clone();
    wrapper_attributes.push("grind unfold".to_string());

    let wrapper = LetBinding {
        name: original_name.clone(),
        attributes: wrapper_attributes,
        is_recursive: false,
        params: {
            let mut params = binding.params.clone();
            params.push((
                VarName::new(RESULT_PARAM),
                binding
                    .return_type
                    .clone()
                    .expect("return_type must be Some"),
            ));
            params
        },
        return_type: Some(Type::Bool),
        body: {
            let func_call_args = binding
                .params
                .iter()
                .map(|(name, _)| Expression::Variable(name.clone()))
                .collect::<Vec<_>>();

            let func_call = Expression::Application(
                Box::new(Expression::Variable(impl_fn_name.clone())),
                func_call_args,
            );

            Expression::BinaryOp(
                Box::new(func_call),
                BinaryOp::Eq,
                Box::new(Expression::Variable(VarName::new(RESULT_PARAM))),
            )
        },
    };

    (impl_binding, wrapper)
}

/// Rename function calls in an expression to use _impl versions
/// This ensures that impl functions call the _impl versions of any functions they invoke
fn rename_function_calls_in(expr: &Expression) -> Expression {
    match expr {
        Expression::Variable(name) => Expression::Variable(name.clone()),
        Expression::Literal(lit) => Expression::Literal(lit.clone()),
        Expression::UnaryOp(op, e) => {
            Expression::UnaryOp(*op, Box::new(rename_function_calls_in(e)))
        }
        Expression::BinaryOp(left, op, right) => Expression::BinaryOp(
            Box::new(rename_function_calls_in(left)),
            *op,
            Box::new(rename_function_calls_in(right)),
        ),
        Expression::Application(func, args) => {
            // Rename ALL function applications to their _impl versions
            let renamed_func = match func.as_ref() {
                Expression::Variable(name) => Box::new(Expression::Variable(impl_name(name))),
                other => Box::new(rename_function_calls_in(other)),
            };
            Expression::Application(
                renamed_func,
                args.iter().map(rename_function_calls_in).collect(),
            )
        }
        Expression::Match(scrutinee, cases) => Expression::Match(
            Box::new(rename_function_calls_in(scrutinee)),
            cases
                .iter()
                .map(|(pattern, body)| (pattern.clone(), rename_function_calls_in(body)))
                .collect(),
        ),
        Expression::Tuple(elements) => {
            Expression::Tuple(elements.iter().map(rename_function_calls_in).collect())
        }
        Expression::IfThenElse {
            condition,
            then_branch,
            else_branch,
        } => Expression::IfThenElse {
            condition: Box::new(rename_function_calls_in(condition)),
            then_branch: Box::new(rename_function_calls_in(then_branch)),
            else_branch: Box::new(rename_function_calls_in(else_branch)),
        },
        Expression::Constructor(name, args) => Expression::Constructor(
            name.clone(),
            args.iter().map(rename_function_calls_in).collect(),
        ),
        Expression::Not(e) => Expression::Not(Box::new(rename_function_calls_in(e))),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lean_backend::LeanContextBuilder;
    use crate::prog_ir::AstNode;
    use crate::test_helpers;

    #[test]
    fn test_create_and_wrap_predicate_for_len() {
        let ocaml_src = "let[@simp][@grind] rec len (l : ilist) : int = match l with | Nil -> 0 | Cons(_, tl) -> 1 + len tl";
        let nodes = crate::ocamlparser::OcamlParser::parse_nodes(ocaml_src)
            .unwrap_or_else(|e| panic!("Failed to parse OCaml: {}", e));
        let binding = test_helpers::find_function(&nodes, "len");

        let (impl_fn, wrapper_fn) = create_and_wrap_predicate(&binding);

        let lean_wrapper = LeanContextBuilder::new()
            .with_nodes(vec![AstNode::LetBinding(wrapper_fn)])
            .build();

        let expected_wrapper = r#"@[simp, grind, grind unfold]
def len (l : ilist) (res : Int) : Bool := (len_impl l == res)"#;
        assert_eq!(lean_wrapper.trim(), expected_wrapper);

        let lean_impl = LeanContextBuilder::new()
            .with_nodes(vec![AstNode::LetBinding(impl_fn)])
            .build();

        let expected_impl = r#"@[simp, grind]
def len_impl (l : ilist) : Int := (match l with
  | .Nil => 0
  | (.Cons _ tl) => (1 + len_impl tl))"#;
        assert_eq!(lean_impl.trim(), expected_impl);
    }
}

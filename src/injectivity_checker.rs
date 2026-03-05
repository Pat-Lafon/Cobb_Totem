use crate::axiom_builder_state::BodyPropositionData;
use crate::prog_ir::BinaryOp;
use crate::spec_ir::Expression;

/// Extract the literal value from result equality (if it exists).
/// Returns Some(literal) if result_expr is an equality with a literal on either side.
/// Returns None otherwise.
pub(crate) fn extract_result_literal(body_prop: &BodyPropositionData) -> Option<Expression> {
    if let Some(Expression::BinaryOp(left, BinaryOp::Eq, right)) = &body_prop.result_expr {
        if let Expression::Literal(_) = left.as_ref() {
            return Some(left.as_ref().clone());
        }
        if let Expression::Literal(_) = right.as_ref() {
            return Some(right.as_ref().clone());
        }
    }
    None
}

/// Check if a base case is suitable for pattern inference (injectivity detection).
///
/// Requires: (1) non-boolean return type, (2) non-negativity pattern (zero + addition),
/// (3) extractable literal output
pub(crate) fn verify_base_case_is_injective(
    binding: &crate::prog_ir::LetBinding,
    body_prop: &BodyPropositionData,
) -> bool {
    if matches!(binding.return_type, Some(crate::prog_ir::Type::Bool)) {
        return false;
    }

    // Check for non-negativity pattern: contains zero and addition
    let body = &binding.body;
    if !(body.contains_literal_zero() && body.contains_addition()) {
        return false;
    }

    extract_result_literal(body_prop).is_some()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_extract_result_literal_finds_equality() {
        let body_prop = BodyPropositionData {
            input_constraints: vec![],
            body_steps: vec![],
            result_expr: Some(Expression::BinaryOp(
                Box::new(Expression::Literal(crate::Literal::Int(0))),
                BinaryOp::Eq,
                Box::new(Expression::Variable("res".into())),
            )),
            additional_parameters: vec![],
        };

        let literal = extract_result_literal(&body_prop);
        assert_eq!(
            literal,
            Some(Expression::Literal(crate::Literal::Int(0))),
            "Should extract the literal zero from equality"
        );
    }

    #[test]
    fn test_extract_result_literal_returns_none_for_non_equality() {
        let body_prop = BodyPropositionData {
            input_constraints: vec![],
            body_steps: vec![],
            result_expr: Some(Expression::BinaryOp(
                Box::new(Expression::Literal(crate::Literal::Int(5))),
                BinaryOp::Add,
                Box::new(Expression::Variable("x".into())),
            )),
            additional_parameters: vec![],
        };

        assert!(extract_result_literal(&body_prop).is_none());
    }

    #[test]
    fn test_extract_result_literal_returns_none_for_no_expr() {
        let body_prop = BodyPropositionData {
            input_constraints: vec![],
            body_steps: vec![],
            result_expr: None,
            additional_parameters: vec![],
        };

        assert!(extract_result_literal(&body_prop).is_none());
    }
}

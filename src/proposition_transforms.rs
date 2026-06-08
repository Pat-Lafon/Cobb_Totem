//! Pure transformations over propositions
//! These are stateless operations that rewrite logical structure without knowledge of axiom construction context.

use crate::prog_ir::BinaryOp;
use crate::spec_ir::{Expression, Proposition};

/// Convert boolean equality A == B to biconditional: (A && B) || (!A && !B)
fn boolean_equality_to_biconditional(left: Expression, right: Expression) -> Proposition {
    let l = Proposition::Expr(left);
    let r = Proposition::Expr(right);
    let and_both = Proposition::And(vec![l.clone(), r.clone()]);
    let not_both = Proposition::And(vec![
        Proposition::Not(Box::new(l)),
        Proposition::Not(Box::new(r)),
    ]);
    Proposition::Or(Box::new(and_both), Box::new(not_both))
}

/// Rewrite `A == B` to `(A ∧ B) ∨ (¬A ∧ ¬B)` when either side is a boolean compound.
pub(crate) fn transform_and_equality(prop: Proposition) -> Proposition {
    prop.map(&|p| match p {
        Proposition::Expr(Expression::BinaryOp(lhs, BinaryOp::Eq, rhs))
            if lhs.is_boolean_expr() || rhs.is_boolean_expr() =>
        {
            boolean_equality_to_biconditional(*lhs, *rhs)
        }
        _ => p,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::VarName;
    use crate::prog_ir::BinaryOp;
    use crate::spec_ir::{Expression, Proposition};

    /// Helper to build `BinaryOp(left, Eq, right)` propositions.
    fn eq_prop(left: Expression, right: Expression) -> Proposition {
        Proposition::Expr(Expression::BinaryOp(
            Box::new(left),
            BinaryOp::Eq,
            Box::new(right),
        ))
    }

    fn var(name: &str) -> Expression {
        Expression::Variable(VarName::new(name))
    }

    fn lt(left: &str, right: &str) -> Expression {
        Expression::BinaryOp(Box::new(var(left)), BinaryOp::Lt, Box::new(var(right)))
    }

    /// Expected biconditional `(L ∧ R) ∨ (¬L ∧ ¬R)`.
    fn biconditional(left: Expression, right: Expression) -> Proposition {
        let l = Proposition::Expr(left);
        let r = Proposition::Expr(right);
        Proposition::Or(
            Box::new(Proposition::And(vec![l.clone(), r.clone()])),
            Box::new(Proposition::And(vec![
                Proposition::Not(Box::new(l)),
                Proposition::Not(Box::new(r)),
            ])),
        )
    }

    /// Boolean compound on one side only. Pins both the biconditional shape
    /// and the `||` gate — flipping to `&&` would no-op this case.
    #[test]
    fn transforms_bool_equality() {
        let result = transform_and_equality(eq_prop(var("res"), lt("a", "b")));
        assert_eq!(result, biconditional(var("res"), lt("a", "b")));
    }

    /// Integer-only equalities must pass through unchanged.
    #[test]
    fn leaves_non_bool_equality_untouched() {
        let input = eq_prop(var("r1"), var("r2"));
        let result = transform_and_equality(input.clone());
        assert_eq!(result, input);
    }
}

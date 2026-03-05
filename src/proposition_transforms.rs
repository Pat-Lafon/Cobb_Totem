//! Pure transformations over propositions
//! These are stateless operations that rewrite logical structure without knowledge of axiom construction context.

use crate::VarName;
use crate::prog_ir::BinaryOp;
use crate::spec_ir::{Expression, Proposition};

/// Convert boolean equality A == B to biconditional: (A && B) || (!A && !B)
pub(crate) fn boolean_equality_to_biconditional(
    left: Expression,
    right: Expression,
) -> Proposition {
    let left_expr = Proposition::Expr(left.clone());
    let right_expr = Proposition::Expr(right.clone());

    // (left && right) || (!left && !right)
    let and_both = Proposition::And(vec![left_expr.clone(), right_expr.clone()]);
    let not_both = Proposition::And(vec![
        Proposition::Not(Box::new(left_expr)),
        Proposition::Not(Box::new(right_expr)),
    ]);

    Proposition::Or(Box::new(and_both), Box::new(not_both))
}

/// Transform boolean equalities into biconditionals during post-order traversal
pub(crate) fn transform_and_equality(prop: &Proposition) -> Proposition {
    prop.clone().map(&|p| match p {
        Proposition::Expr(Expression::BinaryOp(ref lhs, BinaryOp::Eq, ref rhs)) => {
            if lhs.is_boolean_expr() {
                boolean_equality_to_biconditional(lhs.as_ref().clone(), rhs.as_ref().clone())
            } else {
                p
            }
        }
        _ => p,
    })
}

/// Build an implication chain from all steps (standard format)
pub(crate) fn build_implication_chain(steps: &[Proposition]) -> Proposition {
    let mut chain = steps.last().unwrap().clone();
    for step in steps[..steps.len() - 1].iter().rev() {
        chain = Proposition::Implication(Box::new(step.clone()), Box::new(chain));
    }
    chain
}

/// Wrap remaining parameters as existential quantifiers at the outermost level.
/// Parameters must be pre-filtered to only those that should be wrapped.
fn wrap_remaining_existentials(
    mut prop: Proposition,
    params_to_wrap: Vec<crate::spec_ir::Parameter>,
) -> Proposition {
    for param in params_to_wrap.iter().rev() {
        prop = Proposition::Existential(param.clone(), Box::new(prop));
    }
    prop
}

/// Strengthen implications to conjunctions when both sides reference the given parameter
pub(crate) fn strengthen_implication_in_scope(
    param_name: &VarName,
    prop: Proposition,
) -> Proposition {
    match prop {
        Proposition::Implication(left, right) => {
            let left_vars = left.collect_variables();
            let right_vars = right.collect_variables();

            if !left_vars.contains(param_name) || !right_vars.contains(param_name) {
                return Proposition::Implication(left, right);
            }

            if matches!(&*right, Proposition::Existential(_, _)) {
                return Proposition::Implication(left, right);
            }

            match *right {
                Proposition::Implication(right_left, right_right) => {
                    let right_left_vars = right_left.collect_variables();
                    if right_left_vars.contains(param_name) {
                        Proposition::Implication(
                            Box::new(Proposition::And(vec![*left, *right_left])),
                            right_right,
                        )
                    } else {
                        Proposition::And(vec![
                            *left,
                            Proposition::Implication(right_left, right_right),
                        ])
                    }
                }
                other => Proposition::And(vec![*left, other]),
            }
        }
        other => other,
    }
}

/// Convert implications to conjunctions in existential bodies when both sides reference the existential
pub(crate) fn apply_conjunction_strengthening(prop: Proposition) -> Proposition {
    prop.map(&|p| match p {
        Proposition::Existential(param, body) => {
            let new_body = strengthen_implication_in_scope(&param.name, *body);
            Proposition::Existential(param, Box::new(new_body))
        }
        other => other,
    })
}

/// Reduce scope of existentials: push `∃ p` into antecedent only when consequent doesn't reference p
pub(crate) fn apply_scope_reduction_pass(prop: Proposition) -> Proposition {
    prop.map(&|p| match p {
        Proposition::Existential(param, body) => {
            if let Proposition::Implication(left, right) = *body.clone() {
                let right_vars = right.collect_variables();
                if !right_vars.contains(&param.name) {
                    return Proposition::Implication(
                        Box::new(Proposition::Existential(param.clone(), left)),
                        right,
                    );
                }
            }
            // Otherwise keep the existential as-is
            Proposition::Existential(param, body)
        }
        other => other,
    })
}

/// Single pass through proposition, wrapping each variable at its first usage point.
pub(crate) fn wrap_at_first_usage_pass(
    prop: &Proposition,
    remaining_params: Vec<crate::spec_ir::Parameter>,
) -> Proposition {
    match prop {
        Proposition::Implication(antecedent, consequent) => {
            // Find which parameters appear in the antecedent
            let antecedent_vars = antecedent.collect_variables();

            // Partition: params that match antecedent vs those that remain
            let (mut matching, remaining): (Vec<_>, Vec<_>) = remaining_params
                .into_iter()
                .partition(|p| antecedent_vars.contains(&p.name));

            // Sort matching params for deterministic order
            matching.sort_by(|a, b| a.name.0.cmp(&b.name.0));

            // Recurse into consequent with reduced parameter list
            let wrapped_consequent = wrap_at_first_usage_pass(consequent, remaining);
            let result = Proposition::Implication(antecedent.clone(), Box::new(wrapped_consequent));

            wrap_remaining_existentials(result, matching)
        }
        other => wrap_remaining_existentials(other.clone(), remaining_params),
    }
}

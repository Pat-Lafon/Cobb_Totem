use itertools::Itertools as _;

use crate::{
    VarName,
    spec_ir::{Axiom, Expression, Proposition},
};

fn collect_all_variables(prop: &Proposition) -> std::collections::HashSet<VarName> {
    let mut vars = std::collections::HashSet::new();
    collect_variables_in_prop(prop, &mut vars);
    vars
}

fn collect_variables_in_prop(prop: &Proposition, vars: &mut std::collections::HashSet<VarName>) {
    match prop {
        Proposition::Expr(expr) => collect_variables_in_expr(expr, vars),
        Proposition::Predicate(_, args) => {
            for arg in args {
                collect_variables_in_expr(arg, vars);
            }
        }
        Proposition::Implication(p, q)
        | Proposition::And(p, q)
        | Proposition::Or(p, q)
        | Proposition::Iff(p, q)
        | Proposition::Equality(p, q) => {
            collect_variables_in_prop(p, vars);
            collect_variables_in_prop(q, vars);
        }
        Proposition::Not(p) => collect_variables_in_prop(p, vars),
    }
}

fn collect_variables_in_expr(expr: &Expression, vars: &mut std::collections::HashSet<VarName>) {
    match expr {
        Expression::Variable(name) => {
            vars.insert(name.clone());
        }
        Expression::BinaryOp(left, _, right) => {
            collect_variables_in_expr(left, vars);
            collect_variables_in_expr(right, vars);
        }
        Expression::UnaryOp(_, expr) => collect_variables_in_expr(expr, vars),
        _ => {}
    }
}

pub(crate) trait ValidateNoFreeVariables {
    fn validate_no_free_variables(&self) -> Result<(), String>;
}

impl ValidateNoFreeVariables for Axiom {
    /// Check that all variables in the body are declared as parameters
    fn validate_no_free_variables(&self) -> Result<(), String> {
        let declared_vars: std::collections::HashSet<_> =
            self.params.iter().map(|p| p.name.clone()).collect();

        let all_vars = collect_all_variables(&self.body);
        let mut free_vars = all_vars.difference(&declared_vars).peekable();

        if free_vars.peek().is_none() {
            return Ok(());
        }

        Err(format!("Free variables in body: {}", free_vars.join(", ")))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::prog_ir::Type;
    use crate::spec_ir::Parameter;

    #[test]
    fn test_free_variable_detection() {
        let params = vec![Parameter::universal("l", Type::Named("ilist".to_string()))];

        let body = Proposition::Implication(
            Box::new(Proposition::Predicate("emp".to_string(), vec![])),
            Box::new(Proposition::Predicate(
                "hd".to_string(),
                vec![
                    Expression::Variable("l".into()),
                    Expression::Variable("x".into()), // Free variable!
                ],
            )),
        );

        let axiom = Axiom {
            name: "test".to_string(),
            params,
            body,
            proof: None,
        };

        assert!(axiom.validate_no_free_variables().is_err());
    }

    #[test]
    fn test_no_free_variables_success() {
        let params = vec![
            Parameter::universal("l", Type::Named("ilist".to_string())),
            Parameter::existential("x", Type::Int),
        ];

        let body = Proposition::Implication(
            Box::new(Proposition::Predicate("emp".to_string(), vec![])),
            Box::new(Proposition::Predicate(
                "hd".to_string(),
                vec![
                    Expression::Variable("l".into()),
                    Expression::Variable("x".into()),
                ],
            )),
        );

        let axiom = Axiom {
            name: "test".to_string(),
            params,
            body,
            proof: None,
        };

        axiom.validate_no_free_variables()
            .unwrap_or_else(|e| panic!("Axiom validation failed: {}", e));
    }
}

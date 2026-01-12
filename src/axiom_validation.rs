use crate::{
    VarName,
    spec_ir::{Axiom, Expression, Proposition, Quantifier},
};

type VarSet = std::collections::HashSet<VarName>;

fn collect_all_variables(prop: &Proposition) -> VarSet {
    let mut vars = VarSet::new();
    collect_variables_in_prop(prop, &mut vars);
    vars
}

fn collect_variables_in_prop(prop: &Proposition, vars: &mut VarSet) {
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

fn collect_variables_in_expr(expr: &Expression, vars: &mut VarSet) {
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

impl Axiom {
    pub fn validate(&self) -> Result<(), String> {
        self.validate_quantifier_order()?;
        self.validate_no_free_variables()
    }

    /// Validate that all universal parameters come before all existential parameters
    fn validate_quantifier_order(&self) -> Result<(), String> {
        self.params
            .iter()
            .try_fold(false, |found_existential, param| {
                match (found_existential, &param.quantifier) {
                    (true, Quantifier::Universal) => Err(format!(
                        "Axiom '{}': Found universal quantifier after existential quantifier. \
                         All universals must come before existentials.",
                        self.name
                    )),
                    _ => Ok(param.quantifier == Quantifier::Existential || found_existential),
                }
            })?;
        Ok(())
    }

    /// Check that all variables in the body are declared as parameters
    fn validate_no_free_variables(&self) -> Result<(), String> {
        let declared_vars: VarSet = self.params.iter().map(|p| p.name.clone()).collect();

        let all_vars = collect_all_variables(&self.body);
        let free_vars: Vec<_> = all_vars.difference(&declared_vars).collect();

        if free_vars.is_empty() {
            return Ok(());
        }

        Err(format!(
            "Free variables in body: {}",
            free_vars
                .iter()
                .map(|v| v.to_string())
                .collect::<Vec<_>>()
                .join(", ")
        ))
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

        assert!(
            axiom.validate_no_free_variables().is_err(),
            "Expected validation to fail for free variable"
        );
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

        axiom
            .validate_no_free_variables()
            .unwrap_or_else(|e| panic!("Axiom validation failed: {}", e));
    }
}

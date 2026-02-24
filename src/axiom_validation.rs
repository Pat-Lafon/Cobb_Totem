use crate::spec_ir::{Axiom, Quantifier};

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

    /// Check that all variables in the body are declared as parameters or existential quantifiers
    fn validate_no_free_variables(&self) -> Result<(), String> {
        let declared_vars: std::collections::HashSet<_> = self.params.iter().map(|p| p.name.clone()).collect();
        let existential_vars = self.body.collect_existential_variables();
        let valid_vars = declared_vars.union(&existential_vars).cloned().collect();

        let all_vars = self.body.collect_variables();
        let free_vars: Vec<_> = all_vars.difference(&valid_vars).collect();

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
    use crate::spec_ir::{Parameter, Proposition, Expression};

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
            attributes: vec![],
            is_internal: false,
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
            attributes: vec![],
            is_internal: false,
        };

        axiom
            .validate_no_free_variables()
            .unwrap_or_else(|e| panic!("Axiom validation failed: {}", e));
    }
}

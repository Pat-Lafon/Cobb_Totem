use crate::spec_ir::{Axiom, Quantifier};

impl Axiom {
    pub fn validate(&self) -> Result<(), String> {
        self.validate_quantifier_order()?;
        self.validate_no_duplicate_variables()?;
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

    /// Validate that no variable is declared more than once
    /// (in parameters or introduced as existential in the body)
    fn validate_no_duplicate_variables(&self) -> Result<(), String> {
        let mut seen = std::collections::HashSet::new();

        // Check for duplicates in parameters
        for param in &self.params {
            if !seen.insert(param.name.clone()) {
                return Err(format!(
                    "Axiom '{}': Duplicate variable '{}' in parameters",
                    self.name, param.name
                ));
            }
        }

        // Check existential variables don't duplicate parameters or each other
        // Collect all existential variables (preserving duplicates) to detect duplicates
        let existential_vars = self.body.collect_existential_variables();
        for var in existential_vars {
            if !seen.insert(var.clone()) {
                return Err(format!(
                    "Axiom '{}': Duplicate existential variable in body or conflicts with parameter",
                    self.name
                ));
            }
        }

        Ok(())
    }

    /// Check that all variables in the body are declared as parameters or existential quantifiers
    fn validate_no_free_variables(&self) -> Result<(), String> {
        let declared_vars: std::collections::HashSet<_> =
            self.params.iter().map(|p| p.name.clone()).collect();
        let existential_vars: std::collections::HashSet<_> = self
            .body
            .collect_existential_variables()
            .into_iter()
            .collect();
        let valid_vars = declared_vars.union(&existential_vars).cloned().collect();

        let all_vars = self.body.collect_variables();
        let free_vars: Vec<_> = all_vars.difference(&valid_vars).collect();

        if free_vars.is_empty() {
            return Ok(());
        }

        Err(format!(
            "Free variables in body: {}\nAxioms:{}",
            free_vars
                .iter()
                .map(|v| v.to_string())
                .collect::<Vec<_>>()
                .join(", "),
            self.to_string()
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::prog_ir::Type;
    use crate::spec_ir::{Expression, Parameter, Proposition};

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

        axiom
            .validate_no_free_variables()
            .expect_err("validation should fail for free variable");
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
            .expect("axiom validation failed");
    }

    #[test]
    fn test_duplicate_variable_in_parameters() {
        let axiom = Axiom {
            name: "test".to_string(),
            params: vec![
                Parameter::universal("x", Type::Int),
                Parameter::universal("x", Type::Int), // Duplicate!
            ],
            body: Proposition::Predicate("p".to_string(), vec![]),
            proof: None,
            attributes: vec![],
            is_internal: false,
        };
        axiom
            .validate_no_duplicate_variables()
            .expect_err("validation should fail for duplicate parameter");
    }

    #[test]
    fn test_duplicate_existential_in_body() {
        let axiom = Axiom {
            name: "test".to_string(),
            params: vec![Parameter::universal("x", Type::Int)],
            body: Proposition::Existential(
                Parameter::existential("y", Type::Int),
                Box::new(Proposition::Implication(
                    Box::new(Proposition::Predicate("p".to_string(), vec![])),
                    Box::new(Proposition::Existential(
                        Parameter::existential("y", Type::Int), // Duplicate existential!
                        Box::new(Proposition::Predicate("q".to_string(), vec![])),
                    )),
                )),
            ),
            proof: None,
            attributes: vec![],
            is_internal: false,
        };
        axiom
            .validate_no_duplicate_variables()
            .expect_err("validation should fail for duplicate existential");
    }

    #[test]
    fn test_existential_conflicts_with_parameter() {
        let axiom = Axiom {
            name: "test".to_string(),
            params: vec![Parameter::universal("x", Type::Int)],
            body: Proposition::Existential(
                Parameter::existential("x", Type::Int), // Conflicts with parameter!
                Box::new(Proposition::Predicate("p".to_string(), vec![])),
            ),
            proof: None,
            attributes: vec![],
            is_internal: false,
        };
        axiom
            .validate_no_duplicate_variables()
            .expect_err("validation should fail for existential conflicting with parameter");
    }

    #[test]
    fn test_no_duplicate_variables_with_existentials() {
        let axiom = Axiom {
            name: "test".to_string(),
            params: vec![
                Parameter::universal("x", Type::Int),
                Parameter::universal("y", Type::Int),
            ],
            body: Proposition::Implication(
                Box::new(Proposition::Existential(
                    Parameter::existential("z", Type::Int),
                    Box::new(Proposition::Predicate("p".to_string(), vec![])),
                )),
                Box::new(Proposition::Predicate("q".to_string(), vec![])),
            ),
            proof: None,
            attributes: vec![],
            is_internal: false,
        };
        axiom
            .validate_no_duplicate_variables()
            .expect("validation should succeed");
    }
}

use crate::prog_ir::{BinaryOp, LetBinding};
use crate::spec_ir::{Axiom, DOMAIN_AXIOM_SUFFIX, Parameter, Proposition};

/// Generate domain-specific axioms for measure functions (e.g., non-negativity constraint).
///
/// Measures are single-parameter recursive functions that return Int and exhibit
/// non-negativity patterns (contain a literal zero base case and build up through addition).
/// Examples: len(l), height(t), count(l)
/// Non-examples: count_greater(l, x) - multiple parameters, not a pure measure
pub(crate) fn generate(binding: &LetBinding) -> Vec<Axiom> {
    let mut domain_axioms = Vec::new();

    // Only generate domain axioms for single-parameter functions (measures)
    if binding.params.len() != 1 {
        return domain_axioms;
    }

    // Only generate domain axioms for functions with non-negativity patterns (zero + addition)
    let body = &binding.body;
    if !(body.contains_literal_zero() && body.contains_addition()) {
        return domain_axioms;
    }

    // For functions that return Int type and exhibit non-negativity patterns
    if binding.return_type.as_ref().map(|t| t.to_string()) == Some("int".to_string()) {
        // Generate: ∀ (param), (∀ (n : int), ((func param n) → (n >= 0)))
        // Only reaches here for measure functions like len(l), height(t) that
        // exhibit non-negativity patterns (start from 0, build up by addition)

        let result_param = binding
            .return_type
            .clone()
            .unwrap_or(crate::prog_ir::Type::Int);

        // Build axiom parameters from function parameters
        let mut axiom_params: Vec<Parameter> = binding
            .params
            .iter()
            .map(|(name, typ)| Parameter::universal(name.clone(), typ.clone()))
            .collect();
        axiom_params.push(Parameter::universal("n", result_param));

        // Build predicate arguments from function parameters
        let mut predicate_args: Vec<crate::spec_ir::Expression> = binding
            .params
            .iter()
            .map(|(name, _)| crate::spec_ir::Expression::Variable(name.clone()))
            .collect();
        predicate_args.push(crate::spec_ir::Expression::Variable("n".into()));

        let body = Proposition::Implication(
            Box::new(Proposition::Predicate(
                binding.name.0.clone(),
                predicate_args,
            )),
            Box::new(Proposition::Expr(crate::spec_ir::Expression::BinaryOp(
                Box::new(crate::spec_ir::Expression::Variable("n".into())),
                BinaryOp::Gte,
                Box::new(crate::spec_ir::Expression::Literal(crate::Literal::Int(0))),
            ))),
        );

        let mut axiom = Axiom {
            name: format!("{}{}", binding.name, DOMAIN_AXIOM_SUFFIX),
            params: axiom_params,
            body,
            proof: None,
            attributes: vec!["simp".to_string(), "grind".to_string()],
            is_internal: false,
        };

        // Use fun_induction tactic on the first (structural) parameter
        let first_param_name = binding
            .params
            .first()
            .map(|(name, _)| name.0.clone())
            .expect("Function must have at least one parameter to generate domain axiom");
        let impl_name = format!("{}_impl", binding.name.0);
        axiom.proof = Some(format!(
            "\nintro {}\nfun_induction {} {} with grind",
            first_param_name, impl_name, first_param_name
        ));
        domain_axioms.push(axiom);

        // Generate derived lemma: ¬((func_impl params...) = -1)
        // Example: from len_geq_0, generate len_impl_ne_negSucc
        let derived_params: Vec<Parameter> = binding
            .params
            .iter()
            .map(|(name, typ)| Parameter::universal(name.clone(), typ.clone()))
            .collect();

        // Build function call to the impl function: (impl_name param)
        // Since we only handle single-parameter measures here, this is straightforward
        let param_var = crate::spec_ir::Expression::Variable(binding.params[0].0.clone());
        let impl_call =
            crate::spec_ir::Expression::FieldAccess(impl_name.clone(), Box::new(param_var));

        let derived_body = Proposition::Not(Box::new(Proposition::Expr(
            crate::spec_ir::Expression::BinaryOp(
                Box::new(impl_call),
                BinaryOp::Eq,
                Box::new(crate::spec_ir::Expression::Literal(crate::Literal::Int(-1))),
            ),
        )));

        let mut derived_axiom = Axiom {
            name: format!("{}_impl_ne_negSucc", binding.name.0),
            params: derived_params,
            body: derived_body,
            proof: None,
            attributes: vec!["simp".to_string(), "grind".to_string()],
            is_internal: true,
        };

        // Build proof that references all parameters to the domain axiom
        let geq_0_name = format!("{}{}", binding.name, DOMAIN_AXIOM_SUFFIX);
        let all_param_names = binding
            .params
            .iter()
            .map(|(name, _)| name.0.clone())
            .collect::<Vec<_>>()
            .join(" ");
        let intro_names = format!("intros {}", all_param_names);
        let domain_axiom_call = format!("{} {}", geq_0_name, all_param_names);
        derived_axiom.proof = Some(format!(
            "\n{}\nhave h := {}\ngrind",
            intro_names, domain_axiom_call
        ));
        domain_axioms.push(derived_axiom);
    }

    domain_axioms
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_domain_axioms_not_generated_for_multi_param_functions() {
        use crate::VarName;
        use crate::prog_ir::Type;

        let binding = LetBinding {
            name: VarName("count_greater".into()),
            params: vec![
                (VarName("l".into()), Type::Int),
                (VarName("x".into()), Type::Int),
            ],
            body: crate::prog_ir::Expression::Literal(crate::Literal::Int(0)),
            return_type: Some(Type::Int),
            attributes: vec![],
            is_recursive: false,
            termination_proof: None,
        };

        let axioms = generate(&binding);
        assert_eq!(
            axioms.len(),
            0,
            "Multi-parameter functions should not generate domain axioms"
        );
    }

    #[test]
    fn test_domain_axiom_not_generated_for_body_without_patterns() {
        use crate::VarName;
        use crate::prog_ir::Type;

        // Body without zero literal or addition patterns should not generate domain axioms
        let binding = LetBinding {
            name: VarName("len".into()),
            params: vec![(VarName("l".into()), Type::Int)],
            body: crate::prog_ir::Expression::Literal(crate::Literal::Int(0)),
            return_type: Some(Type::Int),
            attributes: vec![],
            is_recursive: false,
            termination_proof: None,
        };

        let axioms = generate(&binding);
        // Body has literal zero but no addition, so it shouldn't pass the pattern check
        // Result should be empty since has_non_negativity_pattern requires both zero and addition
        assert_eq!(
            axioms.len(),
            0,
            "Simple literal body without addition should not generate domain axioms"
        );
    }
}

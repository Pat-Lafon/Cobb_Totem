use itertools::Itertools as _;

use crate::VarName;
use crate::prog_ir::{BinaryOp, LetBinding, TypeDecl};
use crate::spec_ir::{
    Axiom, DOMAIN_AXIOM_SUFFIX, Expression, Parameter, Proposition, Quantifier, RESULT_PARAM,
};

/// Type alias for proof tactic closure
pub type ProofTacticFn = Box<dyn Fn(&Axiom) -> String>;

/// Data for a single axiom body with its parameters
/// Explicitly separates input constraints (structural patterns + guard conditions) from body computation steps
#[derive(Debug, Clone)]
pub struct BodyPropositionData {
    /// Input constraints from both structural patterns (pattern matching) and guard conditions (if-then-else)
    pub input_constraints: Vec<Proposition>,
    pub body_steps: Vec<Proposition>,
    /// The final result expression, if one exists
    pub result_expr: Option<Expression>,
    pub additional_parameters: Vec<Parameter>,
}

impl BodyPropositionData {
    /// Partition additional parameters into universal and existential groups
    pub(crate) fn partition_parameters(&self) -> (Vec<Parameter>, Vec<Parameter>) {
        self.additional_parameters
            .iter()
            .cloned()
            .partition(|p| p.quantifier == Quantifier::Universal)
    }

    /// Extract the literal value from result equality (if it exists).
    /// Returns Some(literal) if result_expr is an equality with a literal on either side.
    /// Returns None otherwise.
    pub(crate) fn extract_result_literal(&self) -> Option<Expression> {
        if let Some(Expression::BinaryOp(left, crate::prog_ir::BinaryOp::Eq, right)) =
            &self.result_expr
        {
            if let Expression::Literal(_) = left.as_ref() {
                return Some(left.as_ref().clone());
            }
            if let Expression::Literal(_) = right.as_ref() {
                return Some(right.as_ref().clone());
            }
        }
        None
    }

    /// Collect all steps into a single sequence.
    /// Combines input constraints, body steps, and the optional result expression.
    pub(crate) fn collect_all_steps(&self) -> Vec<Proposition> {
        let mut all_steps = self.input_constraints.clone();
        all_steps.extend(self.body_steps.clone());
        if let Some(result_expr) = &self.result_expr {
            all_steps.push(Proposition::Expr(result_expr.clone()));
        }
        all_steps
    }
}

/// Intermediate builder state for axiom generation
/// Separates the analysis phase from the generation phase
pub struct AxiomBuilderState {
    /// Type constructors for analysis
    pub type_constructors: Vec<TypeDecl>,
    /// Functions with their body propositions for batch processing
    pub prepared: Vec<(LetBinding, Vec<BodyPropositionData>)>,
    /// Optional closure to determine proof technique for each axiom
    pub proof: Option<ProofTacticFn>,
}

impl std::fmt::Debug for AxiomBuilderState {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("AxiomBuilderState")
            .field("type_constructors", &self.type_constructors)
            .field("prepared", &self.prepared)
            .field("proof", &self.proof.as_ref().map(|_| "<closure>"))
            .finish()
    }
}

impl AxiomBuilderState {
    pub fn new(
        type_constructors: Vec<TypeDecl>,
        prepared: Vec<(LetBinding, Vec<BodyPropositionData>)>,
    ) -> Self {
        Self {
            type_constructors,
            prepared,
            proof: None,
        }
    }

    /// Set the proof for generated axioms using a closure that determines proof technique per axiom
    pub fn with_proof<F>(mut self, proof_fn: F) -> Self
    where
        F: Fn(&Axiom) -> String + 'static,
    {
        self.proof = Some(Box::new(proof_fn));
        self
    }

    /// Check if a function exhibits non-negativity patterns.
    ///
    /// Analyzes the function body for characteristics typical of non-negative-returning functions:
    /// - Contains a literal zero (base case that returns 0)
    /// - Uses addition operation (builds up result by adding)
    ///
    /// Functions with these patterns (like `len`, `height`, `count`) naturally guarantee non-negative results.
    fn has_non_negativity_pattern(binding: &LetBinding) -> bool {
        let body = &binding.body;
        body.contains_literal_zero() && body.contains_addition()
    }

    /// Verify that a specific base case body is suitable for pattern inference.
    ///
    /// Combines the function-level heuristic with actual inspection of the case's output:
    /// 1. Function must exhibit non-negativity pattern (zero + addition)
    /// 2. This specific case must have extractable output value
    /// 3. Output should be a literal constant (not a variable or complex expression)
    ///
    /// The non-negativity heuristic (zero + addition) works because most injective functions
    /// follow this pattern:
    /// - Base case returns literal constant (e.g., 0)
    /// - Recursive cases build up from that base (e.g., 1 + recursive_result)
    /// - Therefore, the base case output is unique and injective
    ///
    /// Examples where this works:
    /// - `len`: Nil→0, Cons→1+len → 0 is unique to base case ✓
    /// - `height`: Leaf→0, Node→1+max(height,height) → 0 is unique to base case ✓
    ///
    /// Examples where this correctly fails:
    /// - `even_list`: []→true, _::_→true → has no zero, returns false ✓
    /// - Function with boolean result (no zero literal) → correctly skipped
    ///
    /// **Limitation**: Cannot detect if base case returns non-zero literal
    /// (e.g., `Nil → 1` would fail this heuristic even if it were injective).
    /// This is acceptable because:
    /// 1. Most list/tree functions return 0 as base case
    /// 2. User can add domain-specific axioms for non-standard cases
    /// 3. Pattern inference is optional; functions still get forward/reverse axioms
    pub(crate) fn verify_base_case_output_is_injective(
        binding: &LetBinding,
        body_prop: &BodyPropositionData,
    ) -> bool {
        // Inference axioms are only valid for injective base cases.
        // Skip boolean-returning functions: different cases often return different values (true/false),
        // making the heuristic invalid.
        // Example: is_even returns true for x=0, false for x=1, false for x=-1, etc.
        // These are NOT injective - we can't infer the input from the output uniquely.
        if matches!(binding.return_type, Some(crate::prog_ir::Type::Bool)) {
            return false;
        }

        // Check function-level heuristic: must have literal zero and addition
        // This works because most injective functions follow the pattern:
        //   base_case → 0
        //   recursive_case → 0 + something
        if !Self::has_non_negativity_pattern(binding) {
            return false;
        }

        // Must be able to extract a literal output value from result_expr
        body_prop.extract_result_literal().is_some()
    }

    /// Convert boolean equality A == B to biconditional: (A && B) || (!A && !B)
    fn boolean_equality_to_biconditional(left: Expression, right: Expression) -> Proposition {
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

    /// Transform boolean equalities (A == B where A or B are boolean expressions) into biconditionals
    /// Also decomposes (expr && cond) == res into expr == res && cond == res when safe
    /// Note: transformation is applied post-order, so nested patterns are already transformed
    fn transform_and_equality(prop: &Proposition) -> Proposition {
        prop.clone().map(&|p| {
            match p {
                Proposition::Expr(Expression::BinaryOp(ref lhs, BinaryOp::Eq, ref rhs)) => {
                    if lhs.is_boolean_expr() {
                        // Convert boolean equality to biconditional
                        Self::boolean_equality_to_biconditional(
                            lhs.as_ref().clone(),
                            rhs.as_ref().clone(),
                        )
                    } else {
                        p
                    }
                }
                _ => p,
            }
        })
    }

    /// Build an implication chain from all steps (standard format)
    fn build_implication_chain(steps: &[Proposition]) -> Proposition {
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
        params_to_wrap: Vec<Parameter>,
    ) -> Proposition {
        for param in params_to_wrap.iter().rev() {
            prop = Proposition::Existential(param.clone(), Box::new(prop));
        }
        prop
    }

    /// Strengthen implications to conjunctions when both sides reference the given parameter.
    ///
    /// Given an existential parameter in scope, decides whether an implication can be
    /// strengthened to a conjunction based on whether both sides reference the parameter.
    /// Returns the original proposition if it's not an implication or doesn't meet criteria.
    fn strengthen_implication_in_scope(param_name: &VarName, prop: Proposition) -> Proposition {
        match prop {
            Proposition::Implication(left, right) => {
                let left_vars = left.collect_variables();
                let right_vars = right.collect_variables();

                // If either side doesn't reference the existential, keep as implication
                if !left_vars.contains(param_name) || !right_vars.contains(param_name) {
                    return Proposition::Implication(left, right);
                }

                // Exception: don't strengthen if right side is an existential
                if matches!(&*right, Proposition::Existential(_, _)) {
                    return Proposition::Implication(left, right);
                }

                match *right {
                    Proposition::Implication(right_left, right_right) => {
                        let right_left_vars = right_left.collect_variables();
                        if right_left_vars.contains(param_name) {
                            // Combine: (A ∧ B) → C
                            Proposition::Implication(
                                Box::new(Proposition::And(vec![*left, *right_left])),
                                right_right,
                            )
                        } else {
                            // Keep separate: A ∧ (B → C)
                            Proposition::And(vec![
                                *left,
                                Proposition::Implication(right_left, right_right),
                            ])
                        }
                    }
                    other => {
                        // Convert to conjunction: A ∧ B
                        Proposition::And(vec![*left, other])
                    }
                }
            }
            other => other,
        }
    }

    /// Apply conjunction strengthening: converts implications to conjunctions
    /// in existential bodies when both sides reference the same existential variable.
    ///
    /// This is a separate post-processing step that optimizes wrapped existentials
    /// by strengthening implications to conjunctions where the structure better
    /// represents the logical relationship.
    fn apply_conjunction_strengthening(prop: Proposition) -> Proposition {
        prop.map(&|p| match p {
            Proposition::Existential(param, body) => {
                let new_body = Self::strengthen_implication_in_scope(&param.name, *body);
                Proposition::Existential(param, Box::new(new_body))
            }
            other => other,
        })
    }

    /// Final pass to reduce scope of existentials where possible.
    /// If an existential wraps an implication where the consequent doesn't reference
    /// the existential variable, push the existential into the antecedent only:
    /// `∃ p, (A → B)` where B doesn't contain p becomes `(∃ p, A) → B`
    fn apply_scope_reduction_pass(prop: Proposition) -> Proposition {
        prop.map(&|p| match p {
            Proposition::Existential(param, body) => {
                // Try to reduce the scope within this existential body
                if let Proposition::Implication(left, right) = *body.clone() {
                    let right_vars = right.collect_variables();
                    // If the right side (consequent) doesn't reference this param,
                    // push the existential to wrap only the left side
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
    /// Removes wrapped parameters from `remaining_params` as they are encountered.
    fn wrap_at_first_usage_pass(
        prop: &Proposition,
        remaining_params: Vec<Parameter>,
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
                let wrapped_consequent = Self::wrap_at_first_usage_pass(consequent, remaining);
                let result =
                    Proposition::Implication(antecedent.clone(), Box::new(wrapped_consequent));

                Self::wrap_remaining_existentials(result, matching)
            }
            other => Self::wrap_remaining_existentials(other.clone(), remaining_params),
        }
    }

    /// Build forward axiom for a given binding and body proposition
    fn build_forward_axiom_for<F>(
        &self,
        binding: &LetBinding,
        idx: usize,
        body_prop: &BodyPropositionData,
        proof_fn: &F,
    ) -> Axiom
    where
        F: Fn(&Axiom) -> String,
    {
        let all_steps = body_prop.collect_all_steps();

        // Collect existential parameters
        let (uni_params, ext_params) = body_prop.partition_parameters();

        // Build implication chain
        let mut steps_body = Self::build_implication_chain(&all_steps);


        steps_body = Self::wrap_at_first_usage_pass(&steps_body, ext_params);
        steps_body = Self::apply_conjunction_strengthening(steps_body);
        steps_body = Self::apply_scope_reduction_pass(steps_body);

        let body = Proposition::Implication(
            Box::new(self.build_predicate_for(binding)),
            Box::new(steps_body),
        );

        let params = self.build_and_partition_params_for(binding, &uni_params);

        Axiom::with_proof(format!("{}_{}", binding.name, idx), params, body, proof_fn)
    }

    /// Build reverse axiom for a given binding and body proposition
    fn build_reverse_axiom_for<F>(
        &self,
        binding: &LetBinding,
        idx: usize,
        body_prop: &BodyPropositionData,
        proof_fn: &F,
    ) -> Axiom
    where
        F: Fn(&Axiom) -> String,
    {
        let all_steps = body_prop.collect_all_steps();

        // Collect existential parameters
        let (uni_params, ext_params) = body_prop.partition_parameters();

        // Build reverse chain: steps → predicate with implication
        let mut body = self.build_predicate_for(binding);

        for step in all_steps.iter().rev() {
            body = Proposition::Implication(Box::new(step.clone()), Box::new(body));
        }

        // Apply lazy existential wrapping with conjunction strengthening and scope reduction
        body = Self::wrap_at_first_usage_pass(&body, ext_params);
        body = Self::apply_conjunction_strengthening(body);
        body = Self::apply_scope_reduction_pass(body);

        let params = self.build_and_partition_params_for(binding, &uni_params);

        Axiom::with_proof(
            format!("{}_{}_rev", binding.name, idx),
            params,
            body,
            proof_fn,
        )
    }

    /// Build pattern inference axiom for a given binding and body proposition.
    ///
    /// Pattern inference axioms create reverse implication chains that infer
    /// structural patterns from computed output values. Only generated for
    /// injective base cases where the output uniquely identifies the pattern.
    ///
    /// For `len` base case (Nil→0):
    /// `len l res → (0 == res) → (is_nil l)`
    ///
    /// This reads: "If we computed the length and got 0, then the list must be nil"
    fn build_pattern_inference_axiom<F>(
        &self,
        binding: &LetBinding,
        idx: usize,
        body_prop: &BodyPropositionData,
        proof_fn: &F,
    ) -> Option<Axiom>
    where
        F: Fn(&Axiom) -> String,
    {
        // Guard: verify this specific base case has an injective output
        // Combines function-level heuristic with actual output verification
        if !Self::verify_base_case_output_is_injective(binding, body_prop) {
            return None;
        }

        // Extract the base case output (e.g., 0 from "0 == res")
        // Safe to unwrap because verify_base_case_output_is_injective already checked this
        let base_output = body_prop.extract_result_literal().unwrap_or_else(|| {
            panic!("verify_base_case_output_is_injective should have succeeded")
        });

        // Collect parameters: split by quantifier type
        let (uni_params, ext_params) = body_prop.partition_parameters();

        // Build the output equality: base_output == res
        let result_var = Expression::Variable(VarName::new(RESULT_PARAM));
        let mut body = Proposition::Expr(Expression::BinaryOp(
            Box::new(base_output),
            BinaryOp::Eq,
            Box::new(result_var),
        ));

        // Build the predicate with its arguments
        let predicate_prop = self.build_predicate_for(binding);


        // Add input constraints (patterns) as implications that consequent to output_eq
        // order: output_eq → constraint₁ → constraint₂ → ...
        for constraint in body_prop.input_constraints.iter() {
            body = Proposition::Implication(Box::new(body), Box::new(constraint.clone()));
        }

        // Wrap with predicate implication: predicate → (output_eq → constraints)
        body = Proposition::Implication(Box::new(predicate_prop), Box::new(body));
        // Apply lazy existential wrapping with conjunction strengthening and scope reduction
        body = Self::wrap_at_first_usage_pass(&body, ext_params);
        body = Self::apply_conjunction_strengthening(body);
        body = Self::apply_scope_reduction_pass(body);

        let params = self.build_and_partition_params_for(binding, &uni_params);

        Some(Axiom::with_proof(
            format!("{}_{}_infer", binding.name, idx),
            params,
            body,
            proof_fn,
        ))
    }

    /// Build forward-pattern axiom for a given binding and body proposition.
    ///
    /// Forward-pattern axioms express that when a pattern is known, the predicate
    /// implies the body. Only generated when pattern constraints are non-empty
    /// (i.e., the axiom has at least one pattern constraint).
    ///
    /// Structure: `(patterns → (predicate → body))`
    /// This maintains pattern context at the front for inference while establishing
    /// forward implication from predicate to body.
    ///
    /// For `len` base case (Nil→0):
    /// `(is_nil l) → ((len l res) → (0 == res))`
    ///
    /// This reads: "Given the pattern is nil, if the predicate holds, then the result equals 0"
    fn build_fwd_pattern_axiom<F>(
        &self,
        binding: &LetBinding,
        idx: usize,
        body_prop: &BodyPropositionData,
        proof_fn: &F,
    ) -> Option<Axiom>
    where
        F: Fn(&Axiom) -> String,
    {
        // Guard: only generate if there are input constraints (structural patterns or guard conditions)
        if body_prop.input_constraints.is_empty() {
            return None;
        }

        // Collect parameters: split by quantifier type
        let (uni_params, ext_params) = body_prop.partition_parameters();

        // Build the predicate with its arguments
        let predicate_prop = self.build_predicate_for(binding);

        // Build the consequent: body steps ∧ result expression
        let mut consequent_steps = body_prop.body_steps.clone();
        if let Some(result_expr) = &body_prop.result_expr {
            consequent_steps.push(Proposition::Expr(result_expr.clone()));
        }
        let consequent = Proposition::optional_conjunction(consequent_steps);

        // Create forward implication: predicate → (body_steps ∧ result)
        let mut final_body =
            Proposition::Implication(Box::new(predicate_prop), Box::new(consequent));

        // Add patterns as antecedents: pattern₁ → (pattern₂ → (... → (pred → result)))
        // Input constraints are collected with structural constraints first, guards last.
        // We want guards first (most selective), then structural patterns.
        // So reverse the list to get the correct order.
        let mut patterns_ordered = body_prop.input_constraints.clone();
        patterns_ordered.reverse();

        // Chain patterns so they nest correctly left-to-right
        // For patterns [is_nil xs, structural], build: is_nil xs → (structural → forward_impl)
        for pattern in patterns_ordered.iter().rev() {
            final_body = Proposition::Implication(Box::new(pattern.clone()), Box::new(final_body));
        }

        // Skip conjunction strengthening for forward patterns: we need patterns → (predicate → result)
        // Strengthening would convert this to patterns ∧ (predicate → result), breaking the structure
        final_body = Self::wrap_at_first_usage_pass(&final_body, ext_params);
        final_body = Self::apply_scope_reduction_pass(final_body);

        let params = self.build_and_partition_params_for(binding, &uni_params);

        Some(Axiom::with_proof(
            format!("{}_{}_fwd_pattern", binding.name, idx),
            params,
            final_body,
            proof_fn,
        ))
    }

    /// Build predicate arguments including function inputs and result variable
    fn build_predicate_for(&self, binding: &LetBinding) -> Proposition {
        let mut args = binding
            .params
            .iter()
            .map(|p| Expression::Variable(p.0.clone()))
            .collect_vec();
        args.push(Expression::Variable(VarName(RESULT_PARAM.to_string())));
        Proposition::Predicate(binding.name.0.clone(), args)
    }

    /// Build and partition parameters for a given binding
    fn build_and_partition_params_for(
        &self,
        binding: &LetBinding,
        uni_params: &[Parameter],
    ) -> Vec<Parameter> {
        let mut params = Parameter::from_vars(&binding.params);
        params.extend_from_slice(uni_params);
        params.push(Parameter::result(binding.return_type.clone().expect(
            "return_type must be Some after prepare_function validation",
        )));
        params
    }

    /// Build all axiom types for a given binding and body propositions
    ///
    /// Currently generates:
    /// - Forward axioms: predicate → (patterns && body)
    /// - Reverse axioms: (patterns && body) → predicate
    /// - Forward-pattern axioms: patterns → (predicate → body) (for axioms with patterns)
    fn build_axioms_for<F>(
        &self,
        binding: &LetBinding,
        body_props: &[BodyPropositionData],
        proof_fn: &F,
    ) -> Result<Vec<Axiom>, String>
    where
        F: Fn(&Axiom) -> String,
    {
        let mut axioms = Vec::new();

        // Build forward, reverse, and forward-pattern axioms for each index
        for (idx, body_prop) in body_props.iter().enumerate() {
            axioms.push(self.build_forward_axiom_for(binding, idx, body_prop, proof_fn));
            axioms.push(self.build_reverse_axiom_for(binding, idx, body_prop, proof_fn));

            if let Some(infer_axiom) =
                self.build_pattern_inference_axiom(binding, idx, body_prop, proof_fn)
            {
                axioms.push(infer_axiom);
            }

            if let Some(fwd_pattern_axiom) =
                self.build_fwd_pattern_axiom(binding, idx, body_prop, proof_fn)
            {
                axioms.push(fwd_pattern_axiom);
            }
        }

        Ok(axioms)
    }

    /// Generate domain-specific axioms for measure functions (e.g., non-negativity constraint).
    ///
    /// Measures are single-parameter recursive functions that return Int and exhibit non-negativity patterns
    /// (contain a literal zero base case and build up through addition).
    /// Examples: len(l), height(t), count(l)
    /// Non-examples: count_greater(l, x) - multiple parameters, not a pure measure
    fn generate_domain_axioms<F>(&self, binding: &LetBinding, _proof_fn: &F) -> Vec<Axiom>
    where
        F: Fn(&Axiom) -> String,
    {
        let mut domain_axioms = Vec::new();

        // Only generate domain axioms for single-parameter functions (measures)
        if binding.params.len() != 1 {
            return domain_axioms;
        }

        // Only generate domain axioms for functions with non-negativity patterns
        if !Self::has_non_negativity_pattern(binding) {
            return domain_axioms;
        }

        // For functions that return Int type and exhibit non-negativity patterns
        // (Already filtered by has_non_negativity_pattern check above: must have literal zero and addition)
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
            let mut predicate_args: Vec<Expression> = binding
                .params
                .iter()
                .map(|(name, _)| Expression::Variable(name.clone()))
                .collect();
            predicate_args.push(Expression::Variable("n".into()));

            let body = Proposition::Implication(
                Box::new(Proposition::Predicate(
                    binding.name.0.clone(),
                    predicate_args,
                )),
                Box::new(Proposition::Expr(Expression::BinaryOp(
                    Box::new(Expression::Variable("n".into())),
                    BinaryOp::Gte,
                    Box::new(Expression::Literal(crate::Literal::Int(0))),
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
            let param_var = Expression::Variable(binding.params[0].0.clone());
            let impl_call = Expression::FieldAccess(impl_name.clone(), Box::new(param_var));

            let derived_body = Proposition::Not(Box::new(Proposition::Expr(Expression::BinaryOp(
                Box::new(impl_call),
                BinaryOp::Eq,
                Box::new(Expression::Literal(crate::Literal::Int(-1))),
            ))));

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

    /// Build all axioms from the stored prepared functions
    /// Generate all axioms (both exported and internal) in proper order
    /// This is crate-internal as it returns the internal representation
    pub(crate) fn generate_all(&self) -> Result<Vec<Axiom>, String> {
        let proof_fn = self
            .proof
            .as_ref()
            .ok_or_else(|| "No proof function available. Use with_proof()".to_string())?;

        let mut axioms = Vec::new();

        // First pass: generate domain axioms first (for access by _infer axioms)
        // Domain axioms already have simp and grind attributes set
        for (binding, _body_propositions) in &self.prepared {
            axioms.extend(self.generate_domain_axioms(binding, proof_fn));
        }

        // Second pass: generate regular axioms
        for (binding, body_propositions) in &self.prepared {
            let mut binding_axioms = self.build_axioms_for(binding, body_propositions, proof_fn)?;
            for axiom in &mut binding_axioms {
                axiom.body = Self::transform_and_equality(&axiom.body);
            }
            axioms.extend(binding_axioms);
        }

        axioms.iter().try_for_each(|axiom| axiom.validate())?;
        Ok(axioms)
    }

    /// Generate OCaml axioms for export
    /// Returns formatted OCaml code with all exported axioms (internal axioms excluded)
    pub fn build_ocaml_export(&self) -> Result<String, String> {
        let all_axioms = self.generate_all()?;

        let ocaml_axioms: Vec<String> = all_axioms
            .iter()
            .filter(|a| !a.is_internal())
            .map(|a| format!("let[@axiom] {} =\n  {}", a.name, a))
            .collect();

        Ok(format!(
            "(* Generated axioms *)\n{}",
            ocaml_axioms.join("\n\n")
        ))
    }

    /// Validate all axioms through Lean backend
    /// Builds Lean code with all axioms (exported + internal) in proper order
    /// Returns Ok(()) if valid, Err with validation error message if invalid
    pub fn validate_with_lean(
        &self,
        nodes: Vec<crate::prog_ir::AstNode>,
        type_decls: &[crate::prog_ir::TypeDecl],
    ) -> Result<(), String> {
        use crate::lean_backend::LeanContextBuilder;
        use crate::lean_validation::validate_lean_code;

        let all_axioms = self.generate_all()?;

        let mut context_builder = LeanContextBuilder::new();
        for type_decl in type_decls {
            let theorems = type_decl.generate_complete_lawful_beq();
            context_builder = context_builder
                .with_type_theorems(&type_decl.name, theorems)
                .with_helper_predicates(&type_decl.name);
        }

        let lean_code = context_builder
            .with_nodes(nodes)
            .with_axioms(all_axioms)
            .build();

        if let Err(e) = validate_lean_code(&lean_code) {
            eprintln!("{lean_code}");
            Err(e)
        } else {
            Ok(())
        }
    }

    /// Get exported axioms only (for testing/inspection)
    /// Returns axioms that should appear in OCaml output (excludes internal axioms)
    pub(crate) fn exported_axioms(&self) -> Result<Vec<Axiom>, String> {
        let all_axioms = self.generate_all()?;
        Ok(all_axioms
            .into_iter()
            .filter(|a| !a.is_internal())
            .collect())
    }
}

#[cfg(test)]
mod tests {
    use crate::ToLean;
    use crate::spec_ir::Axiom;
    use crate::test_helpers;

    #[test]
    fn test_generate_axioms_from_length_function() {
        use crate::axiom_generator::AxiomGenerator;

        let program_str = "type [@grind] ilist = Nil | Cons of { head : int; tail : ilist }\n\nlet [@simp] [@grind] rec len (l : ilist) : int =\nmatch l with\n| Nil -> 0\n| Cons { head = x; tail = xs } -> 1 + len xs";

        let mut parsed_nodes = test_helpers::parse_program(program_str);
        let len_fn = test_helpers::find_function(&parsed_nodes, "len");
        let type_constructors = test_helpers::extract_type_decls(&parsed_nodes);

        let mut generator = AxiomGenerator::new(type_constructors);
        generator
            .prepare_function(&len_fn)
            .expect("Failed to prepare len");

        let builder = generator
            .build_all()
            .with_proof(|a| a.suggest_proof_tactic());

        // Validate axioms with Lean backend
        parsed_nodes = crate::wrap_all_functions(parsed_nodes);
        let type_constructors = test_helpers::extract_type_decls(&parsed_nodes);
        builder
            .validate_with_lean(parsed_nodes, &type_constructors)
            .expect("Failed to validate axioms with Lean");
    }

    #[test]
    fn test_derived_lemma_ne_neg_succ_generated() {
        use crate::axiom_generator::AxiomGenerator;

        let program_str = "type [@grind] ilist = Nil | Cons of { head : int; tail : ilist }\n\nlet [@simp] [@grind] rec len (l : ilist) : int =\nmatch l with\n| Nil -> 0\n| Cons { head = x; tail = xs } -> 1 + len xs";

        let mut parsed_nodes = test_helpers::parse_program(program_str);
        let len_fn = test_helpers::find_function(&parsed_nodes, "len");
        let type_constructors = test_helpers::extract_type_decls(&parsed_nodes);

        let mut generator = AxiomGenerator::new(type_constructors.clone());
        generator
            .prepare_function(&len_fn)
            .expect("Failed to prepare len");

        let builder = generator
            .build_all()
            .with_proof(|a| a.suggest_proof_tactic());

        // Generate all axioms including internal ones (for checking the derived lemma)
        let all_axioms = builder.generate_all().expect("Failed to generate axioms");

        // Check that len_impl_ne_negSucc axiom was generated
        let ne_negsucc = all_axioms
            .iter()
            .find(|a| a.name == "len_impl_ne_negSucc")
            .expect("len_impl_ne_negSucc axiom should be generated");

        // Check the complete Lean representation
        let lean_code = ne_negsucc.to_lean();
        let expected = "@[simp, grind] theorem len_impl_ne_negSucc : ∀ l : ilist, ¬(((len_impl l) = -1)) := by \nintros l\nhave h := len_geq_0 l\ngrind";
        assert_eq!(
            lean_code.trim(),
            expected,
            "Derived lemma should generate correct Lean theorem"
        );

        parsed_nodes = crate::wrap_all_functions(parsed_nodes);
        builder
            .validate_with_lean(parsed_nodes, &type_constructors)
            .expect("Failed to validate axioms with Lean");
    }

    #[test]
    fn test_generate_axioms_from_sorted_function() {
        use crate::axiom_generator::AxiomGenerator;

        let program_str = "type [@grind] ilist = Nil | Cons of { head : int; tail : ilist }\nlet [@simp] [@grind] rec sorted (l : ilist) : bool = match l with | Nil -> true | Cons { head = x; tail = xs } -> match xs with | Nil -> true | Cons { head = y; tail = ys } -> (x <= y) && sorted xs";

        let mut parsed_nodes = test_helpers::parse_program(program_str);
        let sorted_fn = test_helpers::find_function(&parsed_nodes, "sorted");
        let type_constructors = test_helpers::extract_type_decls(&parsed_nodes);

        let mut generator = AxiomGenerator::new(type_constructors.clone());
        generator
            .prepare_function(&sorted_fn)
            .expect("Failed to prepare sorted");

        let builder = generator
            .build_all()
            .with_proof(|a| a.suggest_proof_tactic());

        parsed_nodes = crate::wrap_all_functions(parsed_nodes);
        builder
            .validate_with_lean(parsed_nodes, &type_constructors)
            .expect("Failed to validate axioms with Lean");
    }

    #[test]
    fn test_sorted_1_fwd_pattern_axiom_structure() {
        let program_str = "type [@grind] ilist = Nil | Cons of { head : int; tail : ilist }\nlet [@simp] [@grind] rec sorted (l : ilist) : bool = match l with | Nil -> true | Cons { head = x; tail = xs } -> match xs with | Nil -> true | Cons { head = y; tail = ys } -> (x <= y) && sorted xs";
        let (parsed_nodes, axioms) = test_helpers::generate_axioms_with_wrapper(program_str);

        let expected = "theorem sorted_1_fwd_pattern : ∀ l : ilist, ∀ x : Int, ∀ xs : ilist, ∀ res : Bool, ((is_nil xs) → (((is_cons l) ∧ ((head l) = x) ∧ ((tail l) = xs)) → ((sorted l res) → (true = res)))) := by grind";
        assert_axiom_lean_output(&axioms, &[("sorted_1_fwd_pattern", expected)]);

        test_helpers::validate_axioms(parsed_nodes, axioms);
    }

    #[test]
    fn test_sorted_2_axiom_structure() {
        let program_str = "type [@grind] ilist = Nil | Cons of { head : int; tail : ilist }\nlet [@simp] [@grind] rec sorted (l : ilist) : bool = match l with | Nil -> true | Cons { head = x; tail = xs } -> match xs with | Nil -> true | Cons { head = y; tail = ys } -> (x <= y) && sorted xs";
        let (parsed_nodes, axioms) = test_helpers::generate_axioms_with_wrapper(program_str);

        let expected = "theorem sorted_2 : ∀ l : ilist, ∀ x : Int, ∀ xs : ilist, ∀ y : Int, ∀ ys : ilist, ∀ res : Bool, ((sorted l res) → (((is_cons l) ∧ ((head l) = x) ∧ ((tail l) = xs)) → (((is_cons xs) ∧ ((head xs) = y) ∧ ((tail xs) = ys)) → (∃ res_0 : Bool, ((sorted xs res_0) ∧ ((((x ≤ y) ∧ res_0) ∧ res) ∨ (¬(((x ≤ y) ∧ res_0)) ∧ ¬(res)))))))) := by \ntry aesop (config := { maxRuleHeartbeats := 20000 })\nintros l\ncases l with\n| _ => \n  try simp_all; grind\n  try aesop\n  try grind\n";
        assert_axiom_lean_output(&axioms, &[("sorted_2", expected)]);

        test_helpers::validate_axioms(parsed_nodes, axioms);
    }

    #[test]
    fn test_sorted_2_rev_axiom_structure() {
        let program_str = "type [@grind] ilist = Nil | Cons of { head : int; tail : ilist }\nlet [@simp] [@grind] rec sorted (l : ilist) : bool = match l with | Nil -> true | Cons { head = x; tail = xs } -> match xs with | Nil -> true | Cons { head = y; tail = ys } -> (x <= y) && sorted xs";
        let (parsed_nodes, axioms) = test_helpers::generate_axioms_with_wrapper(program_str);

        let expected = "theorem sorted_2_rev : ∀ l : ilist, ∀ x : Int, ∀ xs : ilist, ∀ y : Int, ∀ ys : ilist, ∀ res : Bool, (((is_cons l) ∧ ((head l) = x) ∧ ((tail l) = xs)) → (((is_cons xs) ∧ ((head xs) = y) ∧ ((tail xs) = ys)) → ((∃ res_0 : Bool, ((sorted xs res_0) ∧ ((((x ≤ y) ∧ res_0) ∧ res) ∨ (¬(((x ≤ y) ∧ res_0)) ∧ ¬(res))))) → (sorted l res)))) := by \ntry aesop (config := { maxRuleHeartbeats := 20000 })\nintros l\ncases l with\n| _ => \n  try simp_all; grind\n  try aesop\n  try grind\n";
        assert_axiom_lean_output(&axioms, &[("sorted_2_rev", expected)]);

        test_helpers::validate_axioms(parsed_nodes, axioms);
    }

    #[test]
    fn test_generate_axioms_from_mem_function() {
        let program_str = "type [@grind] ilist = Nil | Cons of { head : int; tail : ilist }\nlet [@simp] [@grind] rec mem (l : ilist) (x : int) : bool = match l with | Nil -> false | Cons { head = h; tail = t } -> (h = x) || mem t x";
        let (parsed_nodes, axioms) = test_helpers::generate_axioms_with_wrapper(program_str);

        let mem_0_expected = "theorem mem_0 : ∀ l : ilist, ∀ x : Int, ∀ res : Bool, ((mem l x res) → ((is_nil l) → (false = res))) := by grind";
        let mem_1_expected = "theorem mem_1 : ∀ l : ilist, ∀ x : Int, ∀ h : Int, ∀ t : ilist, ∀ res : Bool, ((mem l x res) → (((is_cons l) ∧ ((head l) = h) ∧ ((tail l) = t)) → (∃ res_0 : Bool, ((mem t x res_0) ∧ ((((h = x) ∨ res_0) ∧ res) ∨ (¬(((h = x) ∨ res_0)) ∧ ¬(res))))))) := by \ntry aesop (config := { maxRuleHeartbeats := 20000 })\nintros l\ncases l with\n| _ => \n  try simp_all; grind\n  try aesop\n  try grind\n";

        assert_axiom_lean_output(
            &axioms,
            &[("mem_0", mem_0_expected), ("mem_1", mem_1_expected)],
        );

        test_helpers::validate_axioms(parsed_nodes, axioms);
    }

    #[test]
    fn test_generate_axioms_from_all_eq_function() {
        let program_str = "type [@grind] ilist = Nil | Cons of { head : int; tail : ilist }\nlet [@simp] [@grind] rec all_eq (l : ilist) (x : int) : bool = match l with | Nil -> true | Cons { head = h; tail = t } -> (h = x) && all_eq t x";
        let (parsed_nodes, axioms) = test_helpers::generate_axioms_with_wrapper(program_str);

        let all_eq_0_expected = "theorem all_eq_0 : ∀ l : ilist, ∀ x : Int, ∀ res : Bool, ((all_eq l x res) → ((is_nil l) → (true = res))) := by grind";
        let all_eq_1_expected = "theorem all_eq_1 : ∀ l : ilist, ∀ x : Int, ∀ h : Int, ∀ t : ilist, ∀ res : Bool, ((all_eq l x res) → (((is_cons l) ∧ ((head l) = h) ∧ ((tail l) = t)) → (∃ res_0 : Bool, ((all_eq t x res_0) ∧ ((((h = x) ∧ res_0) ∧ res) ∨ (¬(((h = x) ∧ res_0)) ∧ ¬(res))))))) := by \ntry aesop (config := { maxRuleHeartbeats := 20000 })\nintros l\ncases l with\n| _ => \n  try simp_all; grind\n  try aesop\n  try grind\n";

        assert_axiom_lean_output(
            &axioms,
            &[
                ("all_eq_0", all_eq_0_expected),
                ("all_eq_1", all_eq_1_expected),
            ],
        );

        test_helpers::validate_axioms(parsed_nodes, axioms);
    }

    #[test]
    fn test_generate_axioms_from_lower_bound_function() {
        let program_str = "type [@grind] tree = Leaf | Node of { value : int; left : tree; right : tree }\n

          let [@simp] [@grind] rec lower_bound (t : tree) (x : int) : bool =
              match t with
              | Leaf -> true
              | Node { value = y; left = l; right = r } -> x <= y && lower_bound l x && lower_bound r x";
        let (parsed_nodes, axioms) = test_helpers::generate_axioms_with_wrapper(program_str);

        let lb_0_expected = "theorem lower_bound_0 : ∀ t : tree, ∀ x : Int, ∀ res : Bool, ((lower_bound t x res) → ((is_leaf t) → (true = res))) := by grind";
        let lb_1_expected = "theorem lower_bound_1 : ∀ t : tree, ∀ x : Int, ∀ y : Int, ∀ l : tree, ∀ r : tree, ∀ res : Bool, ((lower_bound t x res) → (((is_node t) ∧ ((value t) = y) ∧ ((left t) = l) ∧ ((right t) = r)) → (∃ res_0 : Bool, ((lower_bound l x res_0) → (∃ res_1 : Bool, ((lower_bound r x res_1) ∧ ((((x ≤ y) ∧ (res_0 ∧ res_1)) ∧ res) ∨ (¬(((x ≤ y) ∧ (res_0 ∧ res_1))) ∧ ¬(res))))))))) := by \ntry aesop (config := { maxRuleHeartbeats := 20000 })\nintros t\ncases t with\n| _ => \n  try simp_all; grind\n  try aesop\n  try grind\n";

        assert_axiom_lean_output(
            &axioms,
            &[
                ("lower_bound_0", lb_0_expected),
                ("lower_bound_1", lb_1_expected),
            ],
        );

        test_helpers::validate_axioms(parsed_nodes, axioms);
    }

    #[test]
    fn test_generate_axioms_from_upper_bound_function() {
        let program_str = "type [@grind] tree = Leaf | Node of { value : int; left : tree; right : tree }\n

         let [@simp] [@grind] rec upper_bound (t : tree) (x : int) : bool =
             match t with
             | Leaf -> true
             | Node { value = y; left = l; right = r } -> y <= x && upper_bound l x && upper_bound r x";
        let (parsed_nodes, axioms) = test_helpers::generate_axioms_with_wrapper(program_str);

        let expected = "theorem upper_bound_0 : ∀ t : tree, ∀ x : Int, ∀ res : Bool, ((upper_bound t x res) → ((is_leaf t) → (true = res))) := by grind";
        assert_axiom_lean_output(&axioms, &[("upper_bound_0", expected)]);

        test_helpers::validate_axioms(parsed_nodes, axioms);
    }

    // TODO: Use this more often
    /// Assert that axioms with given names match expected Lean output
    fn assert_axiom_lean_output(axioms: &[Axiom], expectations: &[(&str, &str)]) {
        for (expected_name, expected_lean) in expectations {
            let axiom = axioms
                .iter()
                .find(|a| &a.name == expected_name)
                .unwrap_or_else(|| panic!("{} axiom should exist", expected_name));

            let actual_lean = axiom.to_lean();
            assert_eq!(
                actual_lean.trim(),
                expected_lean.trim(),
                "{} axiom has incorrect structure",
                expected_name
            );
        }
    }

    #[test]
    fn test_len_1_axiom_structure() {
        let program_str = "type [@grind] ilist = Nil | Cons of { head : int; tail : ilist }\nlet [@simp] [@grind] rec len (l : ilist) : int = match l with | Nil -> 0 | Cons { head = x; tail = xs } -> 1 + len xs";
        let (parsed_nodes, axioms) = test_helpers::generate_axioms_with_wrapper(program_str);

        let len_1_expected = "theorem len_1 : ∀ l : ilist, ∀ x : Int, ∀ xs : ilist, ∀ res : Int, ((len l res) → (((is_cons l) ∧ ((head l) = x) ∧ ((tail l) = xs)) → (∃ res_0 : Int, ((len xs res_0) ∧ ((1 + res_0) = res))))) := by \ntry aesop (config := { maxRuleHeartbeats := 20000 })\nintros l\ncases l with\n| _ => \n  try simp_all; grind\n  try aesop\n  try grind\n";

        assert_axiom_lean_output(&axioms, &[("len_1", len_1_expected)]);

        test_helpers::validate_axioms(parsed_nodes, axioms);
    }

    #[test]
    fn test_mem_1_rev_axiom_structure() {
        let program_str = "type [@grind] ilist = Nil | Cons of { head : int; tail : ilist }\nlet [@simp] [@grind] rec mem (l : ilist) (x : int) : bool = match l with | Nil -> false | Cons { head = h; tail = t } -> (h = x) || mem t x";
        let (parsed_nodes, axioms) = test_helpers::generate_axioms_with_wrapper(program_str);

        let expected = "theorem mem_1_rev : ∀ l : ilist, ∀ x : Int, ∀ h : Int, ∀ t : ilist, ∀ res : Bool, (((is_cons l) ∧ ((head l) = h) ∧ ((tail l) = t)) → ((∃ res_0 : Bool, ((mem t x res_0) ∧ ((((h = x) ∨ res_0) ∧ res) ∨ (¬(((h = x) ∨ res_0)) ∧ ¬(res))))) → (mem l x res))) := by \ntry aesop (config := { maxRuleHeartbeats := 20000 })\nintros l\ncases l with\n| _ => \n  try simp_all; grind\n  try aesop\n  try grind\n";
        assert_axiom_lean_output(&axioms, &[("mem_1_rev", expected)]);

        test_helpers::validate_axioms(parsed_nodes, axioms);
    }

    #[test]
    fn test_lazy_existential_placement_in_height_axiom() {
        use crate::axiom_generator::AxiomGenerator;

        let program_str = "type [@grind] tree = Leaf | Node of { value : int; left : tree; right : tree }\nlet [@simp] [@grind] rec height (t : tree) : int = match t with | Leaf -> 0 | Node { value = v; left = l; right = r } -> ite (height l > height r) (1 + height l) (1 + height r)";

        let mut parsed_nodes = test_helpers::parse_program(program_str);
        let height_fn = test_helpers::find_function(&parsed_nodes, "height");
        let type_constructors = test_helpers::extract_type_decls(&parsed_nodes);

        let mut generator = AxiomGenerator::new(type_constructors.clone());
        generator
            .prepare_function(&height_fn)
            .expect("Failed to prepare height");

        let builder = generator
            .build_all()
            .with_proof(|a| a.suggest_proof_tactic());

        let axioms = builder.exported_axioms().expect("Failed to export axioms");

        let height_1 = axioms
            .iter()
            .find(|a| a.name == "height_1")
            .expect("height_1 axiom should exist");

        let lean_output = height_1.to_lean();

        let expected = "theorem height_1 : ∀ t : tree, ∀ v : Int, ∀ l : tree, ∀ r : tree, ∀ res : Int, ((height t res) → (((is_node t) ∧ ((value t) = v) ∧ ((left t) = l) ∧ ((right t) = r)) → (∃ res_0 : Int, ((∃ res_1 : Int, ((height l res_0) ∧ (height r res_1) ∧ (res_0 > res_1))) → ((height l res_0) → ((1 + res_0) = res)))))) := by \ntry aesop (config := { maxRuleHeartbeats := 20000 })\nintros t\ncases t with\n| _ => \n  try simp_all; grind\n  try aesop\n  try grind\n";

        assert_eq!(
            lean_output.trim(),
            expected.trim(),
            "height_1 axiom structure (grouped condition atoms).\n\
             With grouped conditions: both res_0 and res_1 are quantified together since they appear in same conjunction."
        );

        // Verify forward-pattern axiom has correct existential scoping
        let height_1_fwd_pattern = axioms
            .iter()
            .find(|a| a.name == "height_1_fwd_pattern")
            .expect("height_1_fwd_pattern axiom should exist");

        let lean_output = height_1_fwd_pattern.to_lean();
        let expected = "theorem height_1_fwd_pattern : ∀ t : tree, ∀ v : Int, ∀ l : tree, ∀ r : tree, ∀ res : Int, (∃ res_0 : Int, ((∃ res_1 : Int, ((height l res_0) ∧ (height r res_1) ∧ (res_0 > res_1))) → (((is_node t) ∧ ((value t) = v) ∧ ((left t) = l) ∧ ((right t) = r)) → ((height t res) → ((height l res_0) ∧ ((1 + res_0) = res)))))) := by \ntry aesop (config := { maxRuleHeartbeats := 20000 })\nintros t\ncases t with\n| _ => \n  try simp_all; grind\n  try aesop\n  try grind\n";

        assert_eq!(lean_output.trim(), expected.trim());

        parsed_nodes = crate::wrap_all_functions(parsed_nodes);
        builder
            .validate_with_lean(parsed_nodes, &type_constructors)
            .expect("Failed to validate axioms with Lean");
    }

    #[test]
    fn test_height_2_and_height_2_fwd_pattern_structure() {
        use crate::axiom_generator::AxiomGenerator;

        let program_str = "type [@grind] tree = Leaf | Node of { value : int; left : tree; right : tree }\nlet [@simp] [@grind] rec height (t : tree) : int = match t with | Leaf -> 0 | Node { value = v; left = l; right = r } -> ite (height l > height r) (1 + height l) (1 + height r)";

        let mut parsed_nodes = test_helpers::parse_program(program_str);
        let height_fn = test_helpers::find_function(&parsed_nodes, "height");
        let type_constructors = test_helpers::extract_type_decls(&parsed_nodes);

        let mut generator = AxiomGenerator::new(type_constructors.clone());
        generator
            .prepare_function(&height_fn)
            .expect("Failed to prepare height");

        let builder = generator
            .build_all()
            .with_proof(|a| a.suggest_proof_tactic());

        let axioms = builder.exported_axioms().expect("Failed to export axioms");

        // Verify height_2_rev has correct structure
        let height_2_rev = axioms
            .iter()
            .find(|a| a.name == "height_2_rev")
            .expect("height_2_rev axiom should exist");

        let lean_output = height_2_rev.to_lean();
        // Updated expected: the antecedent now correctly groups conditions And[And[conditions], predicates]
        // and the consequent chain is (result_eq → predicate)
        let expected = "theorem height_2_rev : ∀ t : tree, ∀ v : Int, ∀ l : tree, ∀ r : tree, ∀ res : Int, (((is_node t) ∧ ((value t) = v) ∧ ((left t) = l) ∧ ((right t) = r)) → (∃ res_0 : Int, (∃ res_1 : Int, ((((height l res_0) ∧ (height r res_1) ∧ ¬((res_0 > res_1))) ∧ (height r res_1)) → (((1 + res_1) = res) → (height t res)))))) := by \ntry aesop (config := { maxRuleHeartbeats := 20000 })\nintros t\ncases t with\n| _ => \n  try simp_all; grind\n  try aesop\n  try grind\n";

        assert_eq!(
            lean_output.trim(),
            expected.trim(),
            "height_2_rev axiom should have the reverse implication structure with proper nesting"
        );

        // Verify height_2_fwd_pattern has correct structure
        let height_2_fwd_pattern = axioms
            .iter()
            .find(|a| a.name == "height_2_fwd_pattern")
            .expect("height_2_fwd_pattern axiom should exist");

        let lean_output = height_2_fwd_pattern.to_lean();
        let expected = "theorem height_2_fwd_pattern : ∀ t : tree, ∀ v : Int, ∀ l : tree, ∀ r : tree, ∀ res : Int, (∃ res_0 : Int, (∃ res_1 : Int, (((height l res_0) ∧ (height r res_1) ∧ ¬((res_0 > res_1))) → (((is_node t) ∧ ((value t) = v) ∧ ((left t) = l) ∧ ((right t) = r)) → ((height t res) → ((height r res_1) ∧ ((1 + res_1) = res))))))) := by \ntry aesop (config := { maxRuleHeartbeats := 20000 })\nintros t\ncases t with\n| _ => \n  try simp_all; grind\n  try aesop\n  try grind\n";

        assert_eq!(
            lean_output.trim(),
            expected.trim(),
            "height_2_fwd_pattern axiom should have the forward pattern structure with pattern guard inside implication"
        );

        parsed_nodes = crate::wrap_all_functions(parsed_nodes);
        builder
            .validate_with_lean(parsed_nodes, &type_constructors)
            .expect("Failed to validate axioms with Lean");
    }

    #[test]
    fn test_generate_axioms_from_height_and_complete_functions() {
        use crate::axiom_generator::AxiomGenerator;

        let program_str = "type [@grind] tree = Leaf | Node of { value : int; left : tree; right : tree }\n\nlet [@simp] [@grind] rec height (t : tree) : int = match t with | Leaf -> 0 | Node { value = v; left = l; right = r } -> ite (height l > height r) (1 + height l) (1 + height r)\n\nlet [@simp] [@grind] rec complete (t : tree) : bool = match t with | Leaf -> true | Node { value = x; left = l; right = r } -> complete l && complete r && height l = height r";

        let mut parsed_nodes = test_helpers::parse_program(program_str);
        let height_fn = test_helpers::find_function(&parsed_nodes, "height");
        let complete_fn = test_helpers::find_function(&parsed_nodes, "complete");
        let type_constructors = test_helpers::extract_type_decls(&parsed_nodes);

        let mut generator = AxiomGenerator::new(type_constructors.clone());
        generator
            .prepare_function(&height_fn)
            .expect("Failed to prepare height");
        generator
            .prepare_function(&complete_fn)
            .expect("Failed to prepare complete");

        let builder = generator
            .build_all()
            .with_proof(|a| a.suggest_proof_tactic());

        parsed_nodes = crate::wrap_all_functions(parsed_nodes);
        builder
            .validate_with_lean(parsed_nodes, &type_constructors)
            .expect("Failed to validate axioms with Lean");
    }

    #[test]
    fn test_generate_axioms_from_bst_functions() {
        use crate::axiom_generator::AxiomGenerator;

        let program_str = "type [@grind] tree = Leaf | Node of { value : int; left : tree; right : tree }\n\n    let [@simp] [@grind] rec lower_bound (t : tree) (x : int) : bool =\n  match t with\n  | Leaf -> true\n  | Node { value = y; left = l; right = r } -> x <= y && lower_bound l x && lower_bound r x\n\n    let [@simp] [@grind] rec upper_bound (t : tree) (x : int) : bool =\n  match t with\n  | Leaf -> true\n  | Node { value = y; left = l; right = r } -> y <= x && upper_bound l x && upper_bound r x\n\n    let [@simp] [@grind] rec bst (t : tree) : bool =\n  match t with\n  | Leaf -> true\n  | Node { value = x; left = l; right = r } -> bst l && bst r && upper_bound l x && lower_bound r x";

        let mut parsed_nodes = test_helpers::parse_program(program_str);
        let lower_bound_fn = test_helpers::find_function(&parsed_nodes, "lower_bound");
        let upper_bound_fn = test_helpers::find_function(&parsed_nodes, "upper_bound");
        let bst_fn = test_helpers::find_function(&parsed_nodes, "bst");
        let type_constructors = test_helpers::extract_type_decls(&parsed_nodes);

        let mut generator = AxiomGenerator::new(type_constructors.clone());
        generator
            .prepare_function(&lower_bound_fn)
            .expect("Failed to prepare lower_bound");
        generator
            .prepare_function(&upper_bound_fn)
            .expect("Failed to prepare upper_bound");
        generator
            .prepare_function(&bst_fn)
            .expect("Failed to prepare bst");

        let builder = generator
            .build_all()
            .with_proof(|a| a.suggest_proof_tactic());

        parsed_nodes = crate::wrap_all_functions(parsed_nodes);
        builder
            .validate_with_lean(parsed_nodes, &type_constructors)
            .expect("Failed to validate axioms with Lean");
    }

    #[test]
    fn test_domain_axiom_generated_for_len_with_patterns() {
        use crate::axiom_generator::AxiomGenerator;

        let program_str = "type [@grind] ilist = Nil | Cons of { head : int; tail : ilist }\nlet [@simp] [@grind] rec len (l : ilist) : int = match l with | Nil -> 0 | Cons { head = x; tail = xs } -> 1 + len xs";
        let mut parsed_nodes = test_helpers::parse_program(program_str);
        let len_fn = test_helpers::find_function(&parsed_nodes, "len");
        let type_constructors = test_helpers::extract_type_decls(&parsed_nodes);

        let mut generator = AxiomGenerator::new(type_constructors.clone());
        generator
            .prepare_function(&len_fn)
            .expect("Failed to prepare len");

        let builder = generator
            .build_all()
            .with_proof(|a| a.suggest_proof_tactic());

        let axioms = builder.exported_axioms().expect("Failed to export axioms");

        // len has both zero (base case) and addition patterns, so domain axiom should be generated
        let domain_axiom = axioms
            .iter()
            .find(|a| a.name == "len_geq_0")
            .expect("len function should generate len_geq_0 axiom due to non-negativity patterns");

        assert!(domain_axiom.is_domain_specific());

        parsed_nodes = crate::wrap_all_functions(parsed_nodes);
        builder
            .validate_with_lean(parsed_nodes, &type_constructors)
            .expect("Failed to validate axioms with Lean");
    }

    #[test]
    fn test_domain_axiom_not_generated_without_patterns() {
        use crate::axiom_generator::AxiomGenerator;

        // all_eq function: has addition (&&) but no literal zero, so should NOT get domain axiom
        let program_str = "type [@grind] ilist = Nil | Cons of { head : int; tail : ilist }\nlet [@simp] [@grind] rec all_eq (l : ilist) (x : int) : bool = match l with | Nil -> true | Cons { head = h; tail = t } -> (h = x) && all_eq t x";
        let mut parsed_nodes = test_helpers::parse_program(program_str);
        let all_eq_fn = test_helpers::find_function(&parsed_nodes, "all_eq");
        let type_constructors = test_helpers::extract_type_decls(&parsed_nodes);

        let mut generator = AxiomGenerator::new(type_constructors.clone());
        generator
            .prepare_function(&all_eq_fn)
            .expect("Failed to prepare all_eq");

        let builder = generator
            .build_all()
            .with_proof(|a| a.suggest_proof_tactic());

        let axioms = builder.exported_axioms().expect("Failed to export axioms");

        // all_eq returns bool, so no domain axiom should be generated
        let domain_axiom_count = axioms.iter().filter(|a| a.is_domain_specific()).count();
        assert_eq!(
            domain_axiom_count, 0,
            "bool-returning function should not generate domain axioms"
        );

        parsed_nodes = crate::wrap_all_functions(parsed_nodes);
        builder
            .validate_with_lean(parsed_nodes, &type_constructors)
            .expect("Failed to validate axioms with Lean");
    }

    #[test]
    fn test_domain_axiom_for_tree_height() {
        use crate::axiom_generator::AxiomGenerator;

        let program_str = "type [@grind] tree = Leaf | Node of { value : int; left : tree; right : tree }\nlet [@simp] [@grind] rec height (t : tree) : int = match t with | Leaf -> 0 | Node { value = v; left = l; right = r } -> 1 + (if height l > height r then height l else height r)";
        let mut parsed_nodes = test_helpers::parse_program(program_str);
        let height_fn = test_helpers::find_function(&parsed_nodes, "height");
        let type_constructors = test_helpers::extract_type_decls(&parsed_nodes);

        let mut generator = AxiomGenerator::new(type_constructors.clone());
        generator
            .prepare_function(&height_fn)
            .expect("Failed to prepare height");

        let builder = generator
            .build_all()
            .with_proof(|a| a.suggest_proof_tactic());

        let all_axioms = builder
            .generate_all()
            .expect("Failed to generate all axioms");

        // Verify height_geq_0 domain axiom exists
        all_axioms
            .iter()
            .find(|a| a.name == "height_geq_0")
            .expect("height function should generate height_geq_0 axiom");

        let height_geq_0_expected = "@[simp, grind] theorem height_geq_0 : ∀ t : tree, ∀ n : Int, ((height t n) → (n ≥ 0)) := by \nintro t\nfun_induction height_impl t with grind";
        let height_impl_ne_neg_succ_expected = "@[simp, grind] theorem height_impl_ne_negSucc : ∀ t : tree, ¬(((height_impl t) = -1)) := by \nintros t\nhave h := height_geq_0 t\ngrind";

        assert_axiom_lean_output(
            &all_axioms,
            &[
                ("height_geq_0", height_geq_0_expected),
                ("height_impl_ne_negSucc", height_impl_ne_neg_succ_expected),
            ],
        );

        // Validate Lean axioms
        parsed_nodes = crate::wrap_all_functions(parsed_nodes);
        builder
            .validate_with_lean(parsed_nodes, &type_constructors)
            .expect("Failed to validate axioms with Lean");
    }

    #[test]
    fn test_len_infer_axiom_generated() {
        use crate::axiom_generator::AxiomGenerator;

        let program_str = "type [@grind] ilist = Nil | Cons of { head : int; tail : ilist }\nlet [@simp] [@grind] rec len (l : ilist) : int = match l with | Nil -> 0 | Cons { head = x; tail = xs } -> 1 + len xs";
        let mut parsed_nodes = test_helpers::parse_program(program_str);
        let len_fn = test_helpers::find_function(&parsed_nodes, "len");
        let type_constructors = test_helpers::extract_type_decls(&parsed_nodes);

        let mut generator = AxiomGenerator::new(type_constructors.clone());
        generator
            .prepare_function(&len_fn)
            .expect("Failed to prepare len");

        let builder = generator
            .build_all()
            .with_proof(|a| a.suggest_proof_tactic());

        let axioms = builder.exported_axioms().expect("Failed to export axioms");

        let len_0_infer_expected = "theorem len_0_infer : ∀ l : ilist, ∀ res : Int, ((len l res) → ((0 = res) → (is_nil l))) := by grind";
        assert_axiom_lean_output(&axioms, &[("len_0_infer", len_0_infer_expected)]);

        // Validate through Lean
        parsed_nodes = crate::wrap_all_functions(parsed_nodes);
        builder
            .validate_with_lean(parsed_nodes, &type_constructors)
            .expect("Failed to validate axioms with Lean");
    }

    #[test]
    fn test_infer_axioms_generated_for_multiple_functions() {
        use crate::axiom_generator::AxiomGenerator;

        // Test with multiple functions that have injective base cases (len, height, count)
        let program_str = "type [@grind] ilist = Nil | Cons of { head : int; tail : ilist }\ntype [@grind] tree = Leaf | Node of { value : int; left : tree; right : tree }\nlet [@simp] [@grind] rec len (l : ilist) : int = match l with | Nil -> 0 | Cons { head = x; tail = xs } -> 1 + len xs\nlet [@simp] [@grind] rec height (t : tree) : int = match t with | Leaf -> 0 | Node { value = v; left = l; right = r } -> 1 + (if height l > height r then height l else height r)\nlet [@simp] [@grind] rec count (l : ilist) : int = match l with | Nil -> 0 | Cons { head = x; tail = xs } -> 1 + count xs";
        let mut parsed_nodes = test_helpers::parse_program(program_str);
        let len_fn = test_helpers::find_function(&parsed_nodes, "len");
        let height_fn = test_helpers::find_function(&parsed_nodes, "height");
        let count_fn = test_helpers::find_function(&parsed_nodes, "count");
        let type_constructors = test_helpers::extract_type_decls(&parsed_nodes);

        let mut generator = AxiomGenerator::new(type_constructors.clone());
        generator
            .prepare_function(&len_fn)
            .expect("Failed to prepare len");
        generator
            .prepare_function(&height_fn)
            .expect("Failed to prepare height");
        generator
            .prepare_function(&count_fn)
            .expect("Failed to prepare count");

        let builder = generator
            .build_all()
            .with_proof(|a| a.suggest_proof_tactic());

        let axioms = builder.exported_axioms().expect("Failed to export axioms");

        // Verify len_0_infer axiom base case
        let len_0_infer = axioms
            .iter()
            .find(|a| a.name == "len_0_infer")
            .expect("len function should generate len_0_infer axiom (base case returns 0)");
        let len_0_infer_lean = len_0_infer.to_lean();
        let len_0_infer_expected = "theorem len_0_infer : ∀ l : ilist, ∀ res : Int, ((len l res) → ((0 = res) → (is_nil l))) := by grind";
        assert_eq!(
            len_0_infer_lean.trim(),
            len_0_infer_expected.trim(),
            "len_0_infer should have correct structure with parameter l, constraint (0 = res), and conclusion (is_nil l)"
        );

        // Verify height_0_infer axiom base case
        let height_0_infer = axioms
            .iter()
            .find(|a| a.name == "height_0_infer")
            .expect("height function should generate height_0_infer axiom (base case returns 0)");
        let height_0_infer_lean = height_0_infer.to_lean();
        let height_0_infer_expected = "theorem height_0_infer : ∀ t : tree, ∀ res : Int, ((height t res) → ((0 = res) → (is_leaf t))) := by grind";
        assert_eq!(
            height_0_infer_lean.trim(),
            height_0_infer_expected.trim(),
            "height_0_infer should have correct structure with parameter t, constraint (0 = res), and conclusion (is_leaf t)"
        );

        // Verify count_0_infer axiom base case
        let count_0_infer = axioms
            .iter()
            .find(|a| a.name == "count_0_infer")
            .expect("count function should generate count_0_infer axiom (base case returns 0)");
        let count_0_infer_lean = count_0_infer.to_lean();
        let count_0_infer_expected = "theorem count_0_infer : ∀ l : ilist, ∀ res : Int, ((count l res) → ((0 = res) → (is_nil l))) := by grind";
        assert_eq!(
            count_0_infer_lean.trim(),
            count_0_infer_expected.trim(),
            "count_0_infer should have correct structure with parameter l, constraint (0 = res), and conclusion (is_nil l)"
        );

        // Verify height_1_fwd_pattern full structure
        let height_1_fwd_pattern = axioms
            .iter()
            .find(|a| a.name == "height_1_fwd_pattern")
            .expect("height_1_fwd_pattern axiom should exist");

        let height_1_lean = height_1_fwd_pattern.to_lean();
        let height_1_expected = "theorem height_1_fwd_pattern : ∀ t : tree, ∀ v : Int, ∀ l : tree, ∀ r : tree, ∀ res : Int, (∃ res_1 : Int, ((∃ res_2 : Int, ((height l res_1) ∧ (height r res_2) ∧ (res_1 > res_2))) → (((is_node t) ∧ ((value t) = v) ∧ ((left t) = l) ∧ ((right t) = r)) → ((height t res) → ((height l res_1) ∧ ((1 + res_1) = res)))))) := by \ntry aesop (config := { maxRuleHeartbeats := 20000 })\nintros t\ncases t with\n| _ => \n  try simp_all; grind\n  try aesop\n  try grind\n";
        assert_eq!(
            height_1_lean.trim(),
            height_1_expected.trim(),
            "height_1_fwd_pattern should have structure pattern ∧ implication with existentials and conjunction of body steps"
        );

        // Verify height_2_fwd_pattern full structure
        let height_2_fwd_pattern = axioms
            .iter()
            .find(|a| a.name == "height_2_fwd_pattern")
            .expect("height_2_fwd_pattern axiom should exist");

        let height_2_lean = height_2_fwd_pattern.to_lean();
        let height_2_expected = "theorem height_2_fwd_pattern : ∀ t : tree, ∀ v : Int, ∀ l : tree, ∀ r : tree, ∀ res : Int, (∃ res_1 : Int, (∃ res_2 : Int, (((height l res_1) ∧ (height r res_2) ∧ ¬((res_1 > res_2))) → (((is_node t) ∧ ((value t) = v) ∧ ((left t) = l) ∧ ((right t) = r)) → ((height t res) → ((height r res_2) ∧ ((1 + res_2) = res))))))) := by \ntry aesop (config := { maxRuleHeartbeats := 20000 })\nintros t\ncases t with\n| _ => \n  try simp_all; grind\n  try aesop\n  try grind\n";
        assert_eq!(
            height_2_lean.trim(),
            height_2_expected.trim(),
            "height_2_fwd_pattern should have correct structure with negated comparison and right branch conclusion"
        );

        // Validate through Lean
        parsed_nodes = crate::wrap_all_functions(parsed_nodes);
        builder
            .validate_with_lean(parsed_nodes, &type_constructors)
            .expect("Failed to validate axioms with Lean");
    }

    #[test]
    fn test_infer_axioms_not_generated_for_non_injective_base_cases() {
        use crate::axiom_generator::AxiomGenerator;

        // all_eq has addition (&&) but no literal zero, so no _infer axiom
        let program_str = "type [@grind] ilist = Nil | Cons of { head : int; tail : ilist }\nlet [@simp] [@grind] rec all_eq (l : ilist) (x : int) : bool = match l with | Nil -> true | Cons { head = h; tail = t } -> (h = x) && all_eq t x";
        let parsed_nodes = test_helpers::parse_program(program_str);
        let all_eq_fn = test_helpers::find_function(&parsed_nodes, "all_eq");
        let type_constructors = test_helpers::extract_type_decls(&parsed_nodes);

        let mut generator = AxiomGenerator::new(type_constructors);
        generator
            .prepare_function(&all_eq_fn)
            .expect("Failed to prepare all_eq");

        let builder = generator
            .build_all()
            .with_proof(|a| a.suggest_proof_tactic());

        let axioms = builder.exported_axioms().expect("Failed to export axioms");

        // Verify _infer axiom is NOT generated (function returns bool, no zero literal)
        let has_all_eq_0_infer = axioms.iter().any(|a| a.name == "all_eq_0_infer");
        assert!(
            !has_all_eq_0_infer,
            "all_eq should not generate _infer axiom (no literal zero, returns bool)"
        );

        // But should still have forward/reverse axioms
        let has_all_eq_0 = axioms.iter().any(|a| a.name == "all_eq_0");
        let has_all_eq_0_rev = axioms.iter().any(|a| a.name == "all_eq_0_rev");
        assert!(
            has_all_eq_0,
            "all_eq should still generate forward axiom (all_eq_0)"
        );
        assert!(
            has_all_eq_0_rev,
            "all_eq should still generate reverse axiom (all_eq_0_rev)"
        );
    }

    #[test]
    fn test_generate_axioms_from_is_even_function() {
        use crate::axiom_generator::AxiomGenerator;

        let program_str = "let [@grind] rec is_even (x : int) : bool =
  if x = 0 then true else
    if x = 1 then false else
      if x = (0-1) then false else
        if x > 1 then is_even (x - 2) else
          is_even (x + 2)";

        let mut parsed_nodes = test_helpers::parse_program(program_str);
        let is_even_fn = test_helpers::find_function(&parsed_nodes, "is_even");
        let type_constructors = test_helpers::extract_type_decls(&parsed_nodes);

        let mut generator = AxiomGenerator::new(type_constructors.clone());
        generator
            .prepare_function(&is_even_fn)
            .unwrap_or_else(|e| panic!("Failed to prepare is_even: {}", e));

        let builder = generator
            .build_all()
            .with_proof(|a| a.suggest_proof_tactic());

        let axioms = builder
            .exported_axioms()
            .unwrap_or_else(|e| panic!("Failed to export axioms: {}", e));

        // Verify complete Lean output for each axiom
        assert_axiom_lean_output(
            &axioms,
            &[
                (
                    "is_even_0",
                    "theorem is_even_0 : ∀ x : Int, ∀ res : Bool, ((is_even x res) → ((x = 0) → (true = res))) := by grind",
                ),
                (
                    "is_even_0_rev",
                    "theorem is_even_0_rev : ∀ x : Int, ∀ res : Bool, ((x = 0) → ((true = res) → (is_even x res))) := by grind",
                ),
                (
                    "is_even_0_fwd_pattern",
                    "theorem is_even_0_fwd_pattern : ∀ x : Int, ∀ res : Bool, ((x = 0) → ((is_even x res) → (true = res))) := by grind",
                ),
                (
                    "is_even_1",
                    "theorem is_even_1 : ∀ x : Int, ∀ res : Bool, ((is_even x res) → (¬((x = 0)) → ((x = 1) → (false = res)))) := by grind",
                ),
                (
                    "is_even_1_rev",
                    "theorem is_even_1_rev : ∀ x : Int, ∀ res : Bool, (¬((x = 0)) → ((x = 1) → ((false = res) → (is_even x res)))) := by grind",
                ),
                (
                    "is_even_1_fwd_pattern",
                    "theorem is_even_1_fwd_pattern : ∀ x : Int, ∀ res : Bool, ((x = 1) → (¬((x = 0)) → ((is_even x res) → (false = res)))) := by grind",
                ),
                (
                    "is_even_2",
                    "theorem is_even_2 : ∀ x : Int, ∀ res : Bool, ((is_even x res) → (¬((x = 0)) → (¬((x = 1)) → ((x = (0 - 1)) → (false = res))))) := by grind",
                ),
                (
                    "is_even_2_rev",
                    "theorem is_even_2_rev : ∀ x : Int, ∀ res : Bool, (¬((x = 0)) → (¬((x = 1)) → ((x = (0 - 1)) → ((false = res) → (is_even x res))))) := by grind",
                ),
                (
                    "is_even_2_fwd_pattern",
                    "theorem is_even_2_fwd_pattern : ∀ x : Int, ∀ res : Bool, ((x = (0 - 1)) → (¬((x = 1)) → (¬((x = 0)) → ((is_even x res) → (false = res))))) := by grind",
                ),
                (
                    "is_even_3",
                    "theorem is_even_3 : ∀ x : Int, ∀ res : Bool, ((is_even x res) → (¬((x = 0)) → (¬((x = 1)) → (¬((x = (0 - 1))) → ((x > 1) → (∃ res_0 : Bool, ((is_even (x - 2) res_0) ∧ (res_0 = res)))))))) := by \ntry aesop (config := { maxRuleHeartbeats := 20000 })\nintros x\ncases x with\n| _ => \n  try simp_all; grind\n  try aesop\n  try grind\n",
                ),
                (
                    "is_even_3_rev",
                    "theorem is_even_3_rev : ∀ x : Int, ∀ res : Bool, (¬((x = 0)) → (¬((x = 1)) → (¬((x = (0 - 1))) → ((x > 1) → ((∃ res_0 : Bool, ((is_even (x - 2) res_0) ∧ (res_0 = res))) → (is_even x res)))))) := by \ntry aesop (config := { maxRuleHeartbeats := 20000 })\nintros x\ncases x with\n| _ => \n  try simp_all; grind\n  try aesop\n  try grind\n",
                ),
                (
                    "is_even_3_fwd_pattern",
                    "theorem is_even_3_fwd_pattern : ∀ x : Int, ∀ res : Bool, ((x > 1) → (¬((x = (0 - 1))) → (¬((x = 1)) → (¬((x = 0)) → ((is_even x res) → (∃ res_0 : Bool, ((is_even (x - 2) res_0) ∧ (res_0 = res)))))))) := by \ntry aesop (config := { maxRuleHeartbeats := 20000 })\nintros x\ncases x with\n| _ => \n  try simp_all; grind\n  try aesop\n  try grind\n",
                ),
                (
                    "is_even_4",
                    "theorem is_even_4 : ∀ x : Int, ∀ res : Bool, ((is_even x res) → (¬((x = 0)) → (¬((x = 1)) → (¬((x = (0 - 1))) → (¬((x > 1)) → (∃ res_1 : Bool, ((is_even (x + 2) res_1) ∧ (res_1 = res)))))))) := by \ntry aesop (config := { maxRuleHeartbeats := 20000 })\nintros x\ncases x with\n| _ => \n  try simp_all; grind\n  try aesop\n  try grind\n",
                ),
                (
                    "is_even_4_rev",
                    "theorem is_even_4_rev : ∀ x : Int, ∀ res : Bool, (¬((x = 0)) → (¬((x = 1)) → (¬((x = (0 - 1))) → (¬((x > 1)) → ((∃ res_1 : Bool, ((is_even (x + 2) res_1) ∧ (res_1 = res))) → (is_even x res)))))) := by \ntry aesop (config := { maxRuleHeartbeats := 20000 })\nintros x\ncases x with\n| _ => \n  try simp_all; grind\n  try aesop\n  try grind\n",
                ),
                (
                    "is_even_4_fwd_pattern",
                    "theorem is_even_4_fwd_pattern : ∀ x : Int, ∀ res : Bool, (¬((x > 1)) → (¬((x = (0 - 1))) → (¬((x = 1)) → (¬((x = 0)) → ((is_even x res) → (∃ res_1 : Bool, ((is_even (x + 2) res_1) ∧ (res_1 = res)))))))) := by \ntry aesop (config := { maxRuleHeartbeats := 20000 })\nintros x\ncases x with\n| _ => \n  try simp_all; grind\n  try aesop\n  try grind\n",
                ),
            ],
        );

        parsed_nodes = crate::wrap_all_functions(parsed_nodes);
        builder
            .validate_with_lean(parsed_nodes, &type_constructors)
            .unwrap_or_else(|e| panic!("Failed to validate axioms with Lean: {}", e));
    }

    #[test]
    fn test_generate_axioms_from_all_even_function() {
        let program_str = "type [@grind] ilist = Nil | Cons of { head : int; tail : ilist }

    let [@grind] rec is_even_num (x : int) : bool =
    if x = 0 then true else
    if x = 1 then false else
      if x = (0-1) then false else
        if x > 1 then is_even_num (x - 2) else
          is_even_num (x + 2)

    let [@grind] rec all_even (l : ilist) : bool =
    match l with
    | Nil -> true
    | Cons { head = x; tail = xs } ->
      is_even_num x && all_even xs";

        let (parsed_nodes, axioms) = test_helpers::generate_axioms_with_wrapper(program_str);

        let all_even_0_expected = "theorem all_even_0 : ∀ l : ilist, ∀ res : Bool, ((all_even l res) → ((is_nil l) → (true = res))) := by grind";
        let all_even_1_expected = "theorem all_even_1 : ∀ l : ilist, ∀ x : Int, ∀ xs : ilist, ∀ res : Bool, ((all_even l res) → (((is_cons l) ∧ ((head l) = x) ∧ ((tail l) = xs)) → (∃ res_2 : Bool, ((is_even_num x res_2) → (∃ res_3 : Bool, ((all_even xs res_3) ∧ (((res_2 ∧ res_3) ∧ res) ∨ (¬((res_2 ∧ res_3)) ∧ ¬(res))))))))) := by \ntry aesop (config := { maxRuleHeartbeats := 20000 })\nintros l\ncases l with\n| _ => \n  try simp_all; grind\n  try aesop\n  try grind\n";

        assert_axiom_lean_output(
            &axioms,
            &[
                ("all_even_0", all_even_0_expected),
                ("all_even_1", all_even_1_expected),
            ],
        );

        test_helpers::validate_axioms(parsed_nodes, axioms);
    }
}

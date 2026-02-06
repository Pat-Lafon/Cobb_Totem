use itertools::Itertools as _;
use std::collections::HashSet;

use crate::VarName;
use crate::create_wrapper::RESULT_PARAM;
use crate::prog_ir::{BinaryOp, LetBinding, TypeDecl};
use crate::spec_ir::{Axiom, DOMAIN_AXIOM_SUFFIX, Expression, Parameter, Proposition, Quantifier};

/// Type alias for proof tactic closure
pub type ProofTacticFn = Box<dyn Fn(&Axiom) -> String>;

/// Data for a single axiom body with its parameters
/// Explicitly separates pattern constraints from body computation steps
#[derive(Debug, Clone)]
pub struct BodyPropositionData {
    pub pattern_constraints: Vec<Proposition>,
    pub body_steps: Vec<Proposition>,
    pub additional_parameters: Vec<Parameter>,
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

    /// Convert boolean equality A == B to biconditional: (A && B) || (!A && !B)
    fn boolean_equality_to_biconditional(left: Expression, right: Expression) -> Proposition {
        let left_expr = Proposition::Expr(left.clone());
        let right_expr = Proposition::Expr(right.clone());

        // (left && right) || (!left && !right)
        let and_both = Proposition::And(Box::new(left_expr.clone()), Box::new(right_expr.clone()));
        let not_both = Proposition::And(
            Box::new(Proposition::Not(Box::new(left_expr))),
            Box::new(Proposition::Not(Box::new(right_expr))),
        );

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

    /// Extract all variable references from a proposition
    pub(crate) fn extract_variables_from_proposition(prop: &Proposition) -> HashSet<VarName> {
        prop.fold(HashSet::new(), &|mut vars, p| match p {
            Proposition::Expr(expr) => {
                vars = expr.fold(vars, &|mut vars, e| {
                    if let Expression::Variable(v) = e {
                        vars.insert(v.clone());
                    }
                    vars
                });
                vars
            }
            Proposition::Predicate(_, args) => {
                for arg in args {
                    vars = arg.fold(vars, &|mut vars, e| {
                        if let Expression::Variable(v) = e {
                            vars.insert(v.clone());
                        }
                        vars
                    });
                }
                vars
            }
            _ => vars,
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

    /// Add lazy existential quantifiers to an implication chain.
    ///
    /// Wraps each existential parameter at its first usage point within the chain.
    /// Parameters are processed in reverse order to create proper nesting:
    /// ∃ last_var, (∃ second_var, (∃ first_var, ...))
    fn add_lazy_existentials_to_chain(chain: Proposition, ext_params: &[Parameter]) -> Proposition {
        let mut params_by_name: std::collections::HashMap<VarName, Parameter> = ext_params
            .iter()
            .map(|p| (p.name.clone(), p.clone()))
            .collect();
        Self::wrap_at_first_usage_pass(&chain, &mut params_by_name)
    }

    /// Strengthen implications to conjunctions when both sides reference the given parameter.
    ///
    /// Given an existential parameter in scope, decides whether an implication can be
    /// strengthened to a conjunction based on whether both sides reference the parameter.
    /// Returns the original proposition if it's not an implication or doesn't meet criteria.
    fn strengthen_implication_in_scope(param_name: &VarName, prop: Proposition) -> Proposition {
        match prop {
            Proposition::Implication(left, right) => {
                let left_vars = Self::extract_variables_from_proposition(&left);
                let right_vars = Self::extract_variables_from_proposition(&right);

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
                        let right_left_vars = Self::extract_variables_from_proposition(&right_left);
                        if right_left_vars.contains(param_name) {
                            // Combine: (A ∧ B) → C
                            Proposition::Implication(
                                Box::new(Proposition::And(left, right_left)),
                                right_right,
                            )
                        } else {
                            // Keep separate: A ∧ (B → C)
                            Proposition::And(
                                left,
                                Box::new(Proposition::Implication(right_left, right_right)),
                            )
                        }
                    }
                    other => {
                        // Convert to conjunction: A ∧ B
                        Proposition::And(left, Box::new(other))
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

    /// Single pass through proposition, wrapping each variable at its first usage point.
    fn wrap_at_first_usage_pass(
        prop: &Proposition,
        params_by_name: &mut std::collections::HashMap<VarName, Parameter>,
    ) -> Proposition {
        match prop {
            Proposition::Implication(antecedent, consequent) => {
                // Extract variables that appear in the antecedent and exist in our parameter map
                let antecedent_vars = Self::extract_variables_from_proposition(antecedent);
                let mut vars_to_wrap: Vec<_> = antecedent_vars
                    .iter()
                    .filter_map(|v| params_by_name.remove(v).map(|p| (v.clone(), p)))
                    .collect();

                // Recurse into consequent with reduced parameter map
                let wrapped_consequent = Self::wrap_at_first_usage_pass(consequent, params_by_name);
                let mut result =
                    Proposition::Implication(antecedent.clone(), Box::new(wrapped_consequent));

                // Wrap variables in reverse order for proper nesting
                for (_, param) in vars_to_wrap.iter_mut().rev() {
                    result = Proposition::Existential(Box::new(param.clone()), Box::new(result));
                }

                result
            }
            other => other.clone(),
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
        let mut all_steps = body_prop.pattern_constraints.clone();
        all_steps.extend(body_prop.body_steps.clone());

        // Collect existential parameters
        let (uni_params, ext_params): (Vec<_>, Vec<_>) = body_prop
            .additional_parameters
            .iter()
            .cloned()
            .partition(|p| p.quantifier == Quantifier::Universal);

        // Build implication chain
        let mut steps_body = Self::build_implication_chain(&all_steps);

        // Add existential quantifiers lazily to the chain
        steps_body = Self::add_lazy_existentials_to_chain(steps_body, &ext_params);

        // Apply conjunction strengthening as a separate post-processing step
        steps_body = Self::apply_conjunction_strengthening(steps_body);

        let predicate_args = self.build_predicate_args_for(binding);

        let body = Proposition::Implication(
            Box::new(Proposition::Predicate(
                binding.name.0.clone(),
                predicate_args,
            )),
            Box::new(steps_body),
        );

        let params = self.build_and_partition_params_for(binding, &uni_params);

        let mut axiom = Axiom {
            name: format!("{}_{}", binding.name, idx),
            params,
            body,
            proof: None,
        };

        axiom.proof = Some(proof_fn(&axiom));
        axiom
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
        let mut all_steps = body_prop.pattern_constraints.clone();
        all_steps.extend(body_prop.body_steps.clone());

        // Collect existential parameters
        let (ext_params, uni_params): (Vec<_>, Vec<_>) = body_prop
            .additional_parameters
            .iter()
            .cloned()
            .partition(|p| p.quantifier == Quantifier::Existential);

        // Build reverse chain: steps → predicate with implication
        let predicate_args = self.build_predicate_args_for(binding);
        let mut body = Proposition::Predicate(binding.name.0.clone(), predicate_args);

        for step in all_steps.iter().rev() {
            body = Proposition::Implication(Box::new(step.clone()), Box::new(body));
        }

        // Add existential quantifiers lazily to wrap at first usage
        body = Self::add_lazy_existentials_to_chain(body, &ext_params);

        // Apply conjunction strengthening as a separate post-processing step
        body = Self::apply_conjunction_strengthening(body);

        let params = self.build_and_partition_params_for(binding, &uni_params);

        let mut axiom = Axiom {
            name: format!("{}_{}_rev", binding.name, idx),
            params,
            body,
            proof: None,
        };

        axiom.proof = Some(proof_fn(&axiom));
        axiom
    }

    /// Build predicate arguments including function inputs and result variable
    fn build_predicate_args_for(&self, binding: &LetBinding) -> Vec<Expression> {
        let mut args = binding
            .params
            .iter()
            .map(|p| Expression::Variable(p.0.clone()))
            .collect_vec();
        args.push(Expression::Variable(VarName(RESULT_PARAM.to_string())));
        args
    }

    /// Build and partition parameters for a given binding
    fn build_and_partition_params_for(
        &self,
        binding: &LetBinding,
        uni_params: &[Parameter],
    ) -> Vec<Parameter> {
        let mut params = Parameter::from_vars(&binding.params);

        params.extend_from_slice(uni_params);
        params.push(Parameter::universal(
            VarName::new(RESULT_PARAM),
            binding
                .return_type
                .clone()
                .expect("return_type must be Some after prepare_function validation"),
        ));
        params
    }

    /// Build both forward and reverse axioms for a given binding and body propositions
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

        // Build forward and reverse axioms as pairs for each index
        for (idx, body_prop) in body_props.iter().enumerate() {
            axioms.push(self.build_forward_axiom_for(binding, idx, body_prop, proof_fn));
            axioms.push(self.build_reverse_axiom_for(binding, idx, body_prop, proof_fn));
        }

        Ok(axioms)
    }

    /// Generate domain-specific axioms for a function (e.g., non-negativity constraint).
    ///
    /// Analyzes the function body for non-negativity patterns (presence of zero and addition).
    /// Only generates domain axioms for int-returning functions that exhibit these patterns.
    fn generate_domain_axioms<F>(&self, binding: &LetBinding, _proof_fn: &F) -> Vec<Axiom>
    where
        F: Fn(&Axiom) -> String,
    {
        let mut domain_axioms = Vec::new();

        // Only generate domain axioms for functions with non-negativity patterns
        if !Self::has_non_negativity_pattern(binding) {
            return domain_axioms;
        }

        // For functions that return Int type and exhibit non-negativity patterns
        if binding.return_type.as_ref().map(|t| t.to_string()) == Some("int".to_string()) {
            // Generate: ∀ (l : ilist), (∀ (n : int), ((func l n) → (n >= 0)))
            let list_param_name = binding
                .params
                .first()
                .map(|p| p.0.clone())
                .unwrap_or_else(|| VarName::new("x"));
            let list_param_type = binding
                .params
                .first()
                .map(|p| p.1.clone())
                .unwrap_or_else(|| crate::prog_ir::Type::Named("ilist".to_string()));
            let result_param = binding
                .return_type
                .clone()
                .unwrap_or_else(|| crate::prog_ir::Type::Int);

            let params = vec![
                Parameter::universal(list_param_name.clone(), list_param_type),
                Parameter::universal("n", result_param),
            ];

            let body = Proposition::Implication(
                Box::new(Proposition::Predicate(
                    binding.name.0.clone(),
                    vec![
                        Expression::Variable(list_param_name.clone()),
                        Expression::Variable("n".into()),
                    ],
                )),
                Box::new(Proposition::Expr(Expression::BinaryOp(
                    Box::new(Expression::Variable("n".into())),
                    BinaryOp::Gte,
                    Box::new(Expression::Literal(crate::Literal::Int(0))),
                ))),
            );

            let mut axiom = Axiom {
                name: format!("{}{}", binding.name, DOMAIN_AXIOM_SUFFIX),
                params,
                body,
                proof: None,
            };
            // Use fun_induction tactic for domain axioms instead of the generic proof tactic
            let param_name = list_param_name.0.clone();
            let impl_name = format!("{}_impl", binding.name.0);
            axiom.proof = Some(format!(
                "\nintro {}\nfun_induction {} {} with grind",
                param_name, impl_name, param_name
            ));
            domain_axioms.push(axiom);
        }

        domain_axioms
    }

    /// Build all axioms from the stored prepared functions
    pub fn build(&self) -> Result<Vec<Axiom>, String> {
        let proof_fn = self
            .proof
            .as_ref()
            .ok_or_else(|| "No proof function available. Use with_proof()".to_string())?;

        let mut axioms = Vec::new();

        for (binding, body_propositions) in &self.prepared {
            let mut binding_axioms = self.build_axioms_for(binding, body_propositions, proof_fn)?;
            for axiom in &mut binding_axioms {
                axiom.body = Self::transform_and_equality(&axiom.body);
            }
            axioms.extend(binding_axioms);
            // Add domain-specific axioms
            axioms.extend(self.generate_domain_axioms(binding, proof_fn));
        }

        axioms.iter().try_for_each(|axiom| axiom.validate())?;
        Ok(axioms)
    }
}

#[cfg(test)]
mod tests {
    use crate::ToLean;
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

        let builder = generator.build_all();
        let axioms = builder
            .with_proof(|a| a.suggest_proof_tactic())
            .build()
            .expect("Failed to generate axioms");

        // Validate axioms with Lean backend
        parsed_nodes = crate::wrap_all_functions(parsed_nodes);
        test_helpers::validate_axioms(parsed_nodes, axioms);
    }

    #[test]
    fn test_generate_axioms_from_sorted_function() {
        use crate::axiom_generator::AxiomGenerator;

        let program_str = "type [@grind] ilist = Nil | Cons of { head : int; tail : ilist }\nlet [@simp] [@grind] rec sorted (l : ilist) : bool = match l with | Nil -> true | Cons { head = x; tail = xs } -> match xs with | Nil -> true | Cons { head = y; tail = ys } -> (x <= y) && sorted xs";

        let mut parsed_nodes = test_helpers::parse_program(program_str);
        let sorted_fn = test_helpers::find_function(&parsed_nodes, "sorted");
        let type_constructors = test_helpers::extract_type_decls(&parsed_nodes);

        let mut generator = AxiomGenerator::new(type_constructors);
        generator
            .prepare_function(&sorted_fn)
            .expect("Failed to prepare sorted");

        let builder = generator.build_all();
        let axioms = builder
            .with_proof(|a| a.suggest_proof_tactic())
            .build()
            .expect("Failed to generate axioms");

        parsed_nodes = crate::wrap_all_functions(parsed_nodes);
        test_helpers::validate_axioms(parsed_nodes, axioms);
    }

    #[test]
    fn test_sorted_2_axiom_structure() {
        let program_str = "type [@grind] ilist = Nil | Cons of { head : int; tail : ilist }\nlet [@simp] [@grind] rec sorted (l : ilist) : bool = match l with | Nil -> true | Cons { head = x; tail = xs } -> match xs with | Nil -> true | Cons { head = y; tail = ys } -> (x <= y) && sorted xs";
        let (parsed_nodes, axioms) =
            test_helpers::generate_axioms_with_wrapper(program_str, "sorted");

        // Find the sorted_2 axiom (forward version of Cons/Cons case)
        let sorted_2 = axioms
            .iter()
            .find(|a| a.name == "sorted_2")
            .expect("sorted_2 axiom should exist");

        let lean_output = sorted_2.to_lean();

        let expected = "theorem sorted_2 : ∀ l : ilist, ∀ x : Int, ∀ xs : ilist, ∀ y : Int, ∀ ys : ilist, ∀ res : Bool, ((sorted l res) → ((((is_cons l) ∧ ((head l) = x)) ∧ ((tail l) = xs)) → ((((is_cons xs) ∧ ((head xs) = y)) ∧ ((tail xs) = ys)) → (∃ res_0 : Bool, ((sorted xs res_0) ∧ ((((x ≤ y) ∧ res_0) ∧ res) ∨ (¬(((x ≤ y) ∧ res_0)) ∧ ¬(res)))))))) := by \ntry aesop (config := { maxRuleHeartbeats := 20000 })\nintros l\ncases l with\n| _ => \n  simp_all\n  try grind\n  try aesop\n";
        assert_eq!(
            lean_output, expected,
            "sorted_2 axiom has incorrect structure"
        );

        test_helpers::validate_axioms(parsed_nodes, axioms);
    }

    #[test]
    fn test_sorted_2_rev_axiom_structure() {
        let program_str = "type [@grind] ilist = Nil | Cons of { head : int; tail : ilist }\nlet [@simp] [@grind] rec sorted (l : ilist) : bool = match l with | Nil -> true | Cons { head = x; tail = xs } -> match xs with | Nil -> true | Cons { head = y; tail = ys } -> (x <= y) && sorted xs";
        let (parsed_nodes, axioms) =
            test_helpers::generate_axioms_with_wrapper(program_str, "sorted");

        // Find the sorted_2_rev axiom (reverse version of Cons/Cons case)
        let sorted_2_rev = axioms
            .iter()
            .find(|a| a.name == "sorted_2_rev")
            .expect("sorted_2_rev axiom should exist");

        let lean_output = sorted_2_rev.to_lean();
        assert_eq!(
            lean_output,
            "theorem sorted_2_rev : ∀ l : ilist, ∀ x : Int, ∀ xs : ilist, ∀ y : Int, ∀ ys : ilist, ∀ res : Bool, ((((is_cons l) ∧ ((head l) = x)) ∧ ((tail l) = xs)) → ((((is_cons xs) ∧ ((head xs) = y)) ∧ ((tail xs) = ys)) → (∃ res_0 : Bool, (((sorted xs res_0) ∧ ((((x ≤ y) ∧ res_0) ∧ res) ∨ (¬(((x ≤ y) ∧ res_0)) ∧ ¬(res)))) → (sorted l res))))) := by \ntry aesop (config := { maxRuleHeartbeats := 20000 })\nintros l\ncases l with\n| _ => \n  simp_all\n  try grind\n  try aesop\n"
        );

        test_helpers::validate_axioms(parsed_nodes, axioms);
    }

    #[test]
    fn test_generate_axioms_from_mem_function() {
        let program_str = "type [@grind] ilist = Nil | Cons of { head : int; tail : ilist }\nlet [@simp] [@grind] rec mem (x : int) (l : ilist) : bool = match l with | Nil -> false | Cons { head = h; tail = t } -> (h = x) || mem x t";
        let (parsed_nodes, axioms) = test_helpers::generate_axioms_with_wrapper(program_str, "mem");

        // Check mem_0 (base case: Nil)
        let mem_0 = axioms
            .iter()
            .find(|a| a.name == "mem_0")
            .expect("mem_0 axiom should exist");
        let mem_0_lean = mem_0.to_lean();
        assert_eq!(
            mem_0_lean,
            "theorem mem_0 : ∀ x : Int, ∀ l : ilist, ∀ res : Bool, ((mem x l res) → ((is_nil l) → (false = res))) := by grind"
        );

        // Check mem_1 (recursive case: Cons)
        let mem_1 = axioms
            .iter()
            .find(|a| a.name == "mem_1")
            .expect("mem_1 axiom should exist");
        let mem_1_lean = mem_1.to_lean();
        let expected_mem_1 = "theorem mem_1 : ∀ x : Int, ∀ l : ilist, ∀ h : Int, ∀ t : ilist, ∀ res : Bool, ((mem x l res) → ((((is_cons l) ∧ ((head l) = h)) ∧ ((tail l) = t)) → (∃ res_0 : Bool, ((mem x t res_0) ∧ ((((h = x) ∨ res_0) ∧ res) ∨ (¬(((h = x) ∨ res_0)) ∧ ¬(res))))))) := by \ntry aesop (config := { maxRuleHeartbeats := 20000 })\nintros l\ncases l with\n| _ => \n  simp_all\n  try grind\n  try aesop\n";
        assert_eq!(mem_1_lean, expected_mem_1);

        test_helpers::validate_axioms(parsed_nodes, axioms);
    }

    #[test]
    fn test_generate_axioms_from_all_eq_function() {
        let program_str = "type [@grind] ilist = Nil | Cons of { head : int; tail : ilist }\nlet [@simp] [@grind] rec all_eq (l : ilist) (x : int) : bool = match l with | Nil -> true | Cons { head = h; tail = t } -> (h = x) && all_eq t x";
        let (parsed_nodes, axioms) =
            test_helpers::generate_axioms_with_wrapper(program_str, "all_eq");

        // Check all_eq_0 (base case: Nil)
        let all_eq_0 = axioms
            .iter()
            .find(|a| a.name == "all_eq_0")
            .expect("all_eq_0 axiom should exist");
        let all_eq_0_lean = all_eq_0.to_lean();
        assert_eq!(
            all_eq_0_lean,
            "theorem all_eq_0 : ∀ l : ilist, ∀ x : Int, ∀ res : Bool, ((all_eq l x res) → ((is_nil l) → (true = res))) := by grind"
        );

        // Check all_eq_1 (recursive case: Cons)
        let all_eq_1 = axioms
            .iter()
            .find(|a| a.name == "all_eq_1")
            .expect("all_eq_1 axiom should exist");
        let all_eq_1_lean = all_eq_1.to_lean();
        // Boolean equalities are now converted to biconditionals: (A && B) || (!A && !B)
        let expected_all_eq_1 = "theorem all_eq_1 : ∀ l : ilist, ∀ x : Int, ∀ h : Int, ∀ t : ilist, ∀ res : Bool, ((all_eq l x res) → ((((is_cons l) ∧ ((head l) = h)) ∧ ((tail l) = t)) → (∃ res_0 : Bool, ((all_eq t x res_0) ∧ ((((h = x) ∧ res_0) ∧ res) ∨ (¬(((h = x) ∧ res_0)) ∧ ¬(res))))))) := by \ntry aesop (config := { maxRuleHeartbeats := 20000 })\nintros l\ncases l with\n| _ => \n  simp_all\n  try grind\n  try aesop\n";
        assert_eq!(all_eq_1_lean, expected_all_eq_1);

        test_helpers::validate_axioms(parsed_nodes, axioms);
    }

    #[test]
    fn test_generate_axioms_from_lower_bound_function() {
        let program_str = "type [@grind] tree = Leaf | Node of { value : int; left : tree; right : tree }\n

          let [@simp] [@grind] rec lower_bound (t : tree) (x : int) : bool =
              match t with
              | Leaf -> true
              | Node { value = y; left = l; right = r } -> x <= y && lower_bound l x && lower_bound r x";
        let (parsed_nodes, axioms) =
            test_helpers::generate_axioms_with_wrapper(program_str, "lower_bound");

        // Check lower_bound_0 (base case: Leaf)
        let lb_0 = axioms
            .iter()
            .find(|a| a.name == "lower_bound_0")
            .expect("lower_bound_0 axiom should exist");
        let lb_0_lean = lb_0.to_lean();
        assert_eq!(
            lb_0_lean,
            "theorem lower_bound_0 : ∀ t : tree, ∀ x : Int, ∀ res : Bool, ((lower_bound t x res) → ((is_leaf t) → (true = res))) := by grind"
        );

        let lb_1 = axioms
            .iter()
            .find(|a| a.name == "lower_bound_1")
            .expect("lower_bound_1 axiom should exist");
        let lb_1_lean = lb_1.to_lean();
        let expected_lb_1 = "theorem lower_bound_1 : ∀ t : tree, ∀ x : Int, ∀ y : Int, ∀ l : tree, ∀ r : tree, ∀ res : Bool, ((lower_bound t x res) → (((((is_node t) ∧ ((value t) = y)) ∧ ((left t) = l)) ∧ ((right t) = r)) → (∃ res_0 : Bool, ((lower_bound l x res_0) → (∃ res_1 : Bool, ((lower_bound r x res_1) ∧ ((((x ≤ y) ∧ (res_0 ∧ res_1)) ∧ res) ∨ (¬(((x ≤ y) ∧ (res_0 ∧ res_1))) ∧ ¬(res))))))))) := by \ntry aesop (config := { maxRuleHeartbeats := 20000 })\nintros t\ncases t with\n| _ => \n  simp_all\n  try grind\n  try aesop\n";
        assert_eq!(lb_1_lean, expected_lb_1);

        test_helpers::validate_axioms(parsed_nodes, axioms);
    }

    #[test]
    fn test_generate_axioms_from_upper_bound_function() {
        let program_str = "type [@grind] tree = Leaf | Node of { value : int; left : tree; right : tree }\n

         let [@simp] [@grind] rec upper_bound (t : tree) (x : int) : bool =
             match t with
             | Leaf -> true
             | Node { value = y; left = l; right = r } -> y <= x && upper_bound l x && upper_bound r x";
        let (parsed_nodes, axioms) =
            test_helpers::generate_axioms_with_wrapper(program_str, "upper_bound");

        // Verify base case axiom structure
        let ub_0 = axioms
            .iter()
            .find(|a| a.name == "upper_bound_0")
            .expect("upper_bound_0 axiom should exist");
        let lean_output = ub_0.to_lean();
        let expected = "theorem upper_bound_0 : ∀ t : tree, ∀ x : Int, ∀ res : Bool, ((upper_bound t x res) → ((is_leaf t) → (true = res))) := by grind";
        assert_eq!(
            lean_output, expected,
            "upper_bound_0 axiom has incorrect structure"
        );

        test_helpers::validate_axioms(parsed_nodes, axioms);
    }

    #[test]
    fn test_len_1_axiom_structure() {
        let program_str = "type [@grind] ilist = Nil | Cons of { head : int; tail : ilist }\nlet [@simp] [@grind] rec len (l : ilist) : int = match l with | Nil -> 0 | Cons { head = x; tail = xs } -> 1 + len xs";
        let (parsed_nodes, axioms) = test_helpers::generate_axioms_with_wrapper(program_str, "len");

        // Find the len_1 axiom (forward version of Cons case)
        let len_1 = axioms
            .iter()
            .find(|a| a.name == "len_1")
            .expect("len_1 axiom should exist");

        // Check the complete Lean representation
        let lean_output = len_1.to_lean();
        let expected = "theorem len_1 : ∀ l : ilist, ∀ x : Int, ∀ xs : ilist, ∀ res : Int, ((len l res) → ((((is_cons l) ∧ ((head l) = x)) ∧ ((tail l) = xs)) → (∃ res_0 : Int, ((len xs res_0) ∧ ((1 + res_0) = res))))) := by \ntry aesop (config := { maxRuleHeartbeats := 20000 })\nintros l\ncases l with\n| _ => \n  simp_all\n  try grind\n  try aesop\n";
        assert_eq!(lean_output, expected, "len_1 axiom has incorrect structure");

        test_helpers::validate_axioms(parsed_nodes, axioms);
    }

    #[test]
    fn test_mem_1_rev_axiom_structure() {
        let program_str = "type [@grind] ilist = Nil | Cons of { head : int; tail : ilist }\nlet [@simp] [@grind] rec mem (x : int) (l : ilist) : bool = match l with | Nil -> false | Cons { head = h; tail = t } -> (h = x) || mem x t";
        let (parsed_nodes, axioms) = test_helpers::generate_axioms_with_wrapper(program_str, "mem");

        // Find the mem_1_rev axiom (reverse version of Cons case)
        let mem_1_rev = axioms
            .iter()
            .find(|a| a.name == "mem_1_rev")
            .expect("mem_1_rev axiom should exist");

        // Check the complete Lean representation
        // Note: Conjunction strengthening pulls conjunction into nested implications:
        // (A ∧ (B → C)) becomes ((A ∧ B) → C) when both A and B reference the existential
        let expected = "theorem mem_1_rev : ∀ x : Int, ∀ l : ilist, ∀ h : Int, ∀ t : ilist, ∀ res : Bool, ((((is_cons l) ∧ ((head l) = h)) ∧ ((tail l) = t)) → (∃ res_0 : Bool, (((mem x t res_0) ∧ ((((h = x) ∨ res_0) ∧ res) ∨ (¬(((h = x) ∨ res_0)) ∧ ¬(res)))) → (mem x l res)))) := by \ntry aesop (config := { maxRuleHeartbeats := 20000 })\nintros l\ncases l with\n| _ => \n  simp_all\n  try grind\n  try aesop\n";
        assert_eq!(
            mem_1_rev.to_lean(),
            expected,
            "mem_1_rev axiom has incorrect structure"
        );

        test_helpers::validate_axioms(parsed_nodes, axioms);
    }

    #[test]
    fn test_lazy_existential_placement_in_height_axiom() {
        use crate::axiom_generator::AxiomGenerator;

        let program_str = "type [@grind] tree = Leaf | Node of { value : int; left : tree; right : tree }\nlet [@simp] [@grind] rec height (t : tree) : int = match t with | Leaf -> 0 | Node { value = v; left = l; right = r } -> 1 + ite (height l > height r) (height l) (height r)";

        let mut parsed_nodes = test_helpers::parse_program(program_str);
        let height_fn = test_helpers::find_function(&parsed_nodes, "height");
        let type_constructors = test_helpers::extract_type_decls(&parsed_nodes);

        let mut generator = AxiomGenerator::new(type_constructors);
        generator
            .prepare_function(&height_fn)
            .expect("Failed to prepare height");

        let builder = generator.build_all();
        let axioms = builder
            .with_proof(|a| a.suggest_proof_tactic())
            .build()
            .expect("Failed to generate axioms");

        let height_1 = axioms
            .iter()
            .find(|a| a.name == "height_1")
            .expect("height_1 axiom should exist");

        let lean_output = height_1.to_lean();

        let expected = "theorem height_1 : ∀ t : tree, ∀ v : Int, ∀ l : tree, ∀ r : tree, ∀ res : Int, ((height t res) → (((((is_node t) ∧ ((value t) = v)) ∧ ((left t) = l)) ∧ ((right t) = r)) → (∃ res_0 : Int, ((height l res_0) → (∃ res_1 : Int, (((height r res_1) ∧ (((res_0 > res_1) ∧ true) ∨ (¬((res_0 > res_1)) ∧ ¬(true)))) → ((height l res_0) → ((1 + res_0) = res)))))))) := by \ntry aesop (config := { maxRuleHeartbeats := 20000 })\nintros t\ncases t with\n| _ => \n  simp_all\n  try grind\n  try aesop";

        assert_eq!(
            lean_output.trim(),
            expected.trim(),
            "height_1 axiom has incorrect structure.\n\
             Key requirement: existential quantifiers must wrap at earliest usage point.\n\
             Expected nesting: ∃ res_0, (height l res_0) → (∃ res_1, (height r res_1) → ...)"
        );

        parsed_nodes = crate::wrap_all_functions(parsed_nodes);
        test_helpers::validate_axioms(parsed_nodes, axioms);
    }

    #[test]
    fn test_generate_axioms_from_height_and_complete_functions() {
        use crate::axiom_generator::AxiomGenerator;

        let program_str = "type [@grind] tree = Leaf | Node of { value : int; left : tree; right : tree }\n\nlet [@simp] [@grind] rec height (t : tree) : int = match t with | Leaf -> 0 | Node { value = v; left = l; right = r } -> 1 + ite (height l > height r) (height l) (height r)\n\nlet [@simp] [@grind] rec complete (t : tree) : bool = match t with | Leaf -> true | Node { value = x; left = l; right = r } -> complete l && complete r && height l = height r";

        let mut parsed_nodes = test_helpers::parse_program(program_str);
        let height_fn = test_helpers::find_function(&parsed_nodes, "height");
        let complete_fn = test_helpers::find_function(&parsed_nodes, "complete");
        let type_constructors = test_helpers::extract_type_decls(&parsed_nodes);

        let mut generator = AxiomGenerator::new(type_constructors);
        generator
            .prepare_function(&height_fn)
            .expect("Failed to prepare height");
        generator
            .prepare_function(&complete_fn)
            .expect("Failed to prepare complete");

        let builder = generator.build_all();
        let axioms = builder
            .with_proof(|a| a.suggest_proof_tactic())
            .build()
            .expect("Failed to generate axioms");

        parsed_nodes = crate::wrap_all_functions(parsed_nodes);
        test_helpers::validate_axioms(parsed_nodes, axioms);
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

        let mut generator = AxiomGenerator::new(type_constructors);
        generator
            .prepare_function(&lower_bound_fn)
            .expect("Failed to prepare lower_bound");
        generator
            .prepare_function(&upper_bound_fn)
            .expect("Failed to prepare upper_bound");
        generator
            .prepare_function(&bst_fn)
            .expect("Failed to prepare bst");

        let builder = generator.build_all();
        let axioms = builder
            .with_proof(|a| a.suggest_proof_tactic())
            .build()
            .expect("Failed to generate axioms");

        parsed_nodes = crate::wrap_all_functions(parsed_nodes);
        test_helpers::validate_axioms(parsed_nodes, axioms);
    }

    #[test]
    fn test_domain_axiom_generated_for_len_with_patterns() {
        use crate::axiom_generator::AxiomGenerator;

        let program_str = "type [@grind] ilist = Nil | Cons of { head : int; tail : ilist }\nlet [@simp] [@grind] rec len (l : ilist) : int = match l with | Nil -> 0 | Cons { head = x; tail = xs } -> 1 + len xs";
        let parsed_nodes = test_helpers::parse_program(program_str);
        let len_fn = test_helpers::find_function(&parsed_nodes, "len");
        let type_constructors = test_helpers::extract_type_decls(&parsed_nodes);

        let mut generator = AxiomGenerator::new(type_constructors);
        generator
            .prepare_function(&len_fn)
            .expect("Failed to prepare len");

        let builder = generator.build_all();
        let axioms = builder
            .with_proof(|a| a.suggest_proof_tactic())
            .build()
            .expect("Failed to generate axioms");

        // len has both zero (base case) and addition patterns, so domain axiom should be generated
        let domain_axiom = axioms
            .iter()
            .find(|a| a.name == "len_geq_0")
            .expect("len function should generate len_geq_0 axiom due to non-negativity patterns");

        assert!(domain_axiom.is_domain_specific());
    }

    #[test]
    fn test_domain_axiom_not_generated_without_patterns() {
        use crate::axiom_generator::AxiomGenerator;

        // all_eq function: has addition (&&) but no literal zero, so should NOT get domain axiom
        let program_str = "type [@grind] ilist = Nil | Cons of { head : int; tail : ilist }\nlet [@simp] [@grind] rec all_eq (l : ilist) (x : int) : bool = match l with | Nil -> true | Cons { head = h; tail = t } -> (h = x) && all_eq t x";
        let parsed_nodes = test_helpers::parse_program(program_str);
        let all_eq_fn = test_helpers::find_function(&parsed_nodes, "all_eq");
        let type_constructors = test_helpers::extract_type_decls(&parsed_nodes);

        let mut generator = AxiomGenerator::new(type_constructors);
        generator
            .prepare_function(&all_eq_fn)
            .expect("Failed to prepare all_eq");

        let builder = generator.build_all();
        let axioms = builder
            .with_proof(|a| a.suggest_proof_tactic())
            .build()
            .expect("Failed to generate axioms");

        // all_eq returns bool, so no domain axiom should be generated
        let domain_axiom_count = axioms.iter().filter(|a| a.is_domain_specific()).count();
        assert_eq!(
            domain_axiom_count, 0,
            "bool-returning function should not generate domain axioms"
        );
    }

    #[test]
    fn test_domain_axiom_requires_both_zero_and_addition() {
        use crate::axiom_generator::AxiomGenerator;

        // A function that returns int but only has zero (no addition) should not get domain axiom
        let program_str = "type [@grind] unit = Unit\nlet [@simp] [@grind] rec const_zero (u : unit) : int = match u with | Unit -> 0";
        let parsed_nodes = test_helpers::parse_program(program_str);
        let const_zero_fn = test_helpers::find_function(&parsed_nodes, "const_zero");
        let type_constructors = test_helpers::extract_type_decls(&parsed_nodes);

        let mut generator = AxiomGenerator::new(type_constructors);
        generator
            .prepare_function(&const_zero_fn)
            .expect("Failed to prepare const_zero");

        let builder = generator.build_all();
        let axioms = builder
            .with_proof(|a| a.suggest_proof_tactic())
            .build()
            .expect("Failed to generate axioms");

        // const_zero has zero but no addition, so no domain axiom should be generated
        let domain_axiom_count = axioms.iter().filter(|a| a.is_domain_specific()).count();
        assert_eq!(
            domain_axiom_count, 0,
            "function without both zero and addition should not generate domain axioms"
        );
    }
}

use crate::VarName;
use crate::domain_axiom_builder;
use crate::injectivity_checker;
use crate::prog_ir::{BinaryOp, LetBinding, TypeDecl};
use crate::proposition_transforms::{
    apply_conjunction_strengthening, apply_scope_reduction_pass, build_implication_chain,
    transform_and_equality, wrap_at_first_usage_pass,
};
use crate::spec_ir::{Axiom, Expression, Parameter, Proposition, Quantifier, RESULT_PARAM};

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
}

impl std::fmt::Debug for AxiomBuilderState {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("AxiomBuilderState")
            .field("type_constructors", &self.type_constructors)
            .field("prepared", &self.prepared)
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
        }
    }

    /// Build forward axiom for a given binding and body proposition
    fn build_forward_axiom_for(
        &self,
        binding: &LetBinding,
        idx: usize,
        body_prop: &BodyPropositionData,
    ) -> Axiom {
        let all_steps = body_prop.collect_all_steps();
        let (uni_params, ext_params) = body_prop.partition_parameters();

        let mut steps_body = build_implication_chain(&all_steps);
        steps_body = wrap_at_first_usage_pass(&steps_body, ext_params);
        steps_body = apply_conjunction_strengthening(steps_body);
        steps_body = apply_scope_reduction_pass(steps_body);

        let body = Proposition::Implication(
            Box::new(Proposition::build_relation_predicate(binding, RESULT_PARAM)),
            Box::new(steps_body),
        );

        Axiom::from_let_binding(
            format!("{}_{}", binding.name, idx),
            binding,
            &uni_params,
            body,
        )
    }

    /// Build reverse axiom for a given binding and body proposition
    fn build_reverse_axiom_for(
        &self,
        binding: &LetBinding,
        idx: usize,
        body_prop: &BodyPropositionData,
    ) -> Axiom {
        let all_steps = body_prop.collect_all_steps();
        let (uni_params, ext_params) = body_prop.partition_parameters();

        let mut body = Proposition::build_relation_predicate(binding, RESULT_PARAM);

        for step in all_steps.iter().rev() {
            body = Proposition::Implication(Box::new(step.clone()), Box::new(body));
        }

        // Apply lazy existential wrapping with conjunction strengthening and scope reduction
        body = wrap_at_first_usage_pass(&body, ext_params);
        body = apply_conjunction_strengthening(body);
        body = apply_scope_reduction_pass(body);

        Axiom::from_let_binding(
            format!("{}_{}_rev", binding.name, idx),
            binding,
            &uni_params,
            body,
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
    fn build_pattern_inference_axiom(
        &self,
        binding: &LetBinding,
        idx: usize,
        body_prop: &BodyPropositionData,
    ) -> Option<Axiom> {
        // Guard: verify this specific base case has an injective output
        // Requires: (1) non-boolean return type, (2) non-negativity pattern (zero + addition),
        // (3) extractable literal output
        if !injectivity_checker::verify_base_case_is_injective(binding, body_prop) {
            return None;
        }

        // Extract the base case output (e.g., 0 from "0 == res")
        // Safe to unwrap because verify_base_case_is_injective already checked this
        let base_output = injectivity_checker::extract_result_literal(body_prop)
            .unwrap_or_else(|| panic!("verify_base_case_is_injective should have succeeded"));

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
        let predicate_prop = Proposition::build_relation_predicate(binding, RESULT_PARAM);

        // Add input constraints (patterns) as implications that consequent to output_eq
        // order: output_eq → constraint₁ → constraint₂ → ...
        for constraint in body_prop.input_constraints.iter() {
            body = Proposition::Implication(Box::new(body), Box::new(constraint.clone()));
        }

        body = Proposition::Implication(Box::new(predicate_prop), Box::new(body));
        body = wrap_at_first_usage_pass(&body, ext_params);
        body = apply_conjunction_strengthening(body);
        body = apply_scope_reduction_pass(body);

        Some(Axiom::from_let_binding(
            format!("{}_{}_infer", binding.name, idx),
            binding,
            &uni_params,
            body,
        ))
    }

    /// Build forward-pattern axiom: generated only when pattern constraints are non-empty
    fn build_fwd_pattern_axiom(
        &self,
        binding: &LetBinding,
        idx: usize,
        body_prop: &BodyPropositionData,
    ) -> Option<Axiom> {
        if body_prop.input_constraints.is_empty() {
            return None;
        }

        let (uni_params, ext_params) = body_prop.partition_parameters();
        let predicate_prop = Proposition::build_relation_predicate(binding, RESULT_PARAM);

        let mut consequent_steps = body_prop.body_steps.clone();
        if let Some(result_expr) = &body_prop.result_expr {
            consequent_steps.push(Proposition::Expr(result_expr.clone()));
        }
        let consequent = Proposition::optional_conjunction(consequent_steps);

        let mut final_body =
            Proposition::Implication(Box::new(predicate_prop), Box::new(consequent));

        let mut patterns_ordered = body_prop.input_constraints.clone();
        patterns_ordered.reverse();

        for pattern in patterns_ordered.iter().rev() {
            final_body = Proposition::Implication(Box::new(pattern.clone()), Box::new(final_body));
        }

        final_body = wrap_at_first_usage_pass(&final_body, ext_params);
        final_body = apply_scope_reduction_pass(final_body);

        Some(Axiom::from_let_binding(
            format!("{}_{}_fwd_pattern", binding.name, idx),
            binding,
            &uni_params,
            final_body,
        ))
    }

    /// Build all axiom types for a given binding and body propositions
    ///
    /// Currently generates:
    /// - Forward axioms: predicate → (patterns && body)
    /// - Reverse axioms: (patterns && body) → predicate
    /// - Forward-pattern axioms: patterns → (predicate → body) (for axioms with patterns)
    fn build_axioms_for(
        &self,
        binding: &LetBinding,
        body_props: &[BodyPropositionData],
    ) -> Result<Vec<Axiom>, String> {
        let mut axioms = Vec::new();

        // Build forward, reverse, and forward-pattern axioms for each index
        for (idx, body_prop) in body_props.iter().enumerate() {
            axioms.push(
                self.build_forward_axiom_for(binding, idx, body_prop)
                    .with_suggested_proof(),
            );
            axioms.push(
                self.build_reverse_axiom_for(binding, idx, body_prop)
                    .with_suggested_proof(),
            );

            if let Some(infer_axiom) = self.build_pattern_inference_axiom(binding, idx, body_prop) {
                axioms.push(infer_axiom.with_suggested_proof());
            }

            if let Some(fwd_pattern_axiom) = self.build_fwd_pattern_axiom(binding, idx, body_prop) {
                axioms.push(fwd_pattern_axiom.with_suggested_proof());
            }
        }

        Ok(axioms)
    }

    /// Build all axioms from the stored prepared functions
    /// Generate all axioms (both exported and internal) in proper order
    /// This is crate-internal as it returns the internal representation
    pub(crate) fn generate_all(&self) -> Result<Vec<Axiom>, String> {
        let mut axioms = Vec::new();

        // First pass: generate domain axioms first (for access by _infer axioms)
        // Domain axioms already have simp and grind attributes set
        for (binding, _body_propositions) in &self.prepared {
            axioms.extend(domain_axiom_builder::generate(binding));
        }

        // Second pass: generate regular axioms
        for (binding, body_propositions) in &self.prepared {
            let mut binding_axioms = self.build_axioms_for(binding, body_propositions)?;
            for axiom in &mut binding_axioms {
                axiom.body = transform_and_equality(&axiom.body);
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
        let exported: Vec<Axiom> = all_axioms
            .into_iter()
            .filter(|a| !a.is_internal())
            .collect();
        let ocaml_axioms: Vec<String> = exported
            .iter()
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

        let builder = generator.build_all();

        // Generate all axioms including internal ones (for checking the derived lemma)
        let all_axioms = builder.generate_all().expect("Failed to generate axioms");

        let expected = "@[simp, grind] theorem len_impl_ne_negSucc : ∀ l : ilist, ¬(((len_impl l) = -1)) := by \nintros l\nhave h := len_geq_0 l\ngrind";
        assert_axiom_lean_output(&all_axioms, &[("len_impl_ne_negSucc", expected)]);

        parsed_nodes = crate::wrap_all_functions(parsed_nodes);
        builder
            .validate_with_lean(parsed_nodes, &type_constructors)
            .expect("Failed to validate axioms with Lean");
    }

    #[test]
    fn test_sorted_axiom_structures() {
        let program_str = "type [@grind] ilist = Nil | Cons of { head : int; tail : ilist }\nlet [@simp] [@grind] rec sorted (l : ilist) : bool = match l with | Nil -> true | Cons { head = x; tail = xs } -> match xs with | Nil -> true | Cons { head = y; tail = ys } -> (x <= y) && sorted xs";
        let (parsed_nodes, axioms) = test_helpers::generate_axioms_with_wrapper(program_str);

        let sorted_1_fwd_pattern_expected = "theorem sorted_1_fwd_pattern : ∀ l : ilist, ∀ x : Int, ∀ xs : ilist, ∀ res : Bool, ((is_nil xs) → (((is_cons l) ∧ ((head l) = x) ∧ ((tail l) = xs)) → ((sorted l res) → (true = res)))) := by grind";
        let sorted_2_expected = "theorem sorted_2 : ∀ l : ilist, ∀ x : Int, ∀ xs : ilist, ∀ y : Int, ∀ ys : ilist, ∀ res : Bool, ((sorted l res) → (((is_cons l) ∧ ((head l) = x) ∧ ((tail l) = xs)) → (((is_cons xs) ∧ ((head xs) = y) ∧ ((tail xs) = ys)) → (∃ res_0 : Bool, ((sorted xs res_0) ∧ ((((x ≤ y) ∧ res_0) ∧ res) ∨ (¬(((x ≤ y) ∧ res_0)) ∧ ¬(res)))))))) := by \ntry aesop (config := { maxRuleHeartbeats := 20000 })\nintros l\ncases l with\n| _ => \n  try simp_all; grind\n  try aesop\n  try grind\n";
        let sorted_2_rev_expected = "theorem sorted_2_rev : ∀ l : ilist, ∀ x : Int, ∀ xs : ilist, ∀ y : Int, ∀ ys : ilist, ∀ res : Bool, (((is_cons l) ∧ ((head l) = x) ∧ ((tail l) = xs)) → (((is_cons xs) ∧ ((head xs) = y) ∧ ((tail xs) = ys)) → ((∃ res_0 : Bool, ((sorted xs res_0) ∧ ((((x ≤ y) ∧ res_0) ∧ res) ∨ (¬(((x ≤ y) ∧ res_0)) ∧ ¬(res))))) → (sorted l res)))) := by \ntry aesop (config := { maxRuleHeartbeats := 20000 })\nintros l\ncases l with\n| _ => \n  try simp_all; grind\n  try aesop\n  try grind\n";

        assert_axiom_lean_output(
            &axioms,
            &[
                ("sorted_1_fwd_pattern", sorted_1_fwd_pattern_expected),
                ("sorted_2", sorted_2_expected),
                ("sorted_2_rev", sorted_2_rev_expected),
            ],
        );

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
    fn test_height_existential_scoping_and_structures() {
        use crate::axiom_generator::AxiomGenerator;

        let program_str = "type [@grind] tree = Leaf | Node of { value : int; left : tree; right : tree }\nlet [@simp] [@grind] rec height (t : tree) : int = match t with | Leaf -> 0 | Node { value = v; left = l; right = r } -> ite (height l > height r) (1 + height l) (1 + height r)";

        let mut parsed_nodes = test_helpers::parse_program(program_str);
        let height_fn = test_helpers::find_function(&parsed_nodes, "height");
        let type_constructors = test_helpers::extract_type_decls(&parsed_nodes);

        let mut generator = AxiomGenerator::new(type_constructors.clone());
        generator
            .prepare_function(&height_fn)
            .expect("Failed to prepare height");

        let builder = generator.build_all();

        let axioms = builder.exported_axioms().expect("Failed to export axioms");

        let height_1_expected = "theorem height_1 : ∀ t : tree, ∀ v : Int, ∀ l : tree, ∀ r : tree, ∀ res : Int, ((height t res) → (((is_node t) ∧ ((value t) = v) ∧ ((left t) = l) ∧ ((right t) = r)) → (∃ res_0 : Int, ((∃ res_1 : Int, ((height l res_0) ∧ (height r res_1) ∧ (res_0 > res_1))) → ((height l res_0) → ((1 + res_0) = res)))))) := by \ntry aesop (config := { maxRuleHeartbeats := 20000 })\nintros t\ncases t with\n| _ => \n  try simp_all; grind\n  try aesop\n  try grind\n";

        let height_1_fwd_pattern_expected = "theorem height_1_fwd_pattern : ∀ t : tree, ∀ v : Int, ∀ l : tree, ∀ r : tree, ∀ res : Int, (∃ res_0 : Int, ((∃ res_1 : Int, ((height l res_0) ∧ (height r res_1) ∧ (res_0 > res_1))) → (((is_node t) ∧ ((value t) = v) ∧ ((left t) = l) ∧ ((right t) = r)) → ((height t res) → ((height l res_0) ∧ ((1 + res_0) = res)))))) := by \ntry aesop (config := { maxRuleHeartbeats := 20000 })\nintros t\ncases t with\n| _ => \n  try simp_all; grind\n  try aesop\n  try grind\n";

        let height_2_rev_expected = "theorem height_2_rev : ∀ t : tree, ∀ v : Int, ∀ l : tree, ∀ r : tree, ∀ res : Int, (((is_node t) ∧ ((value t) = v) ∧ ((left t) = l) ∧ ((right t) = r)) → (∃ res_0 : Int, (∃ res_1 : Int, ((((height l res_0) ∧ (height r res_1) ∧ ¬((res_0 > res_1))) ∧ (height r res_1)) → (((1 + res_1) = res) → (height t res)))))) := by \ntry aesop (config := { maxRuleHeartbeats := 20000 })\nintros t\ncases t with\n| _ => \n  try simp_all; grind\n  try aesop\n  try grind\n";

        let height_2_fwd_pattern_expected = "theorem height_2_fwd_pattern : ∀ t : tree, ∀ v : Int, ∀ l : tree, ∀ r : tree, ∀ res : Int, (∃ res_0 : Int, (∃ res_1 : Int, (((height l res_0) ∧ (height r res_1) ∧ ¬((res_0 > res_1))) → (((is_node t) ∧ ((value t) = v) ∧ ((left t) = l) ∧ ((right t) = r)) → ((height t res) → ((height r res_1) ∧ ((1 + res_1) = res))))))) := by \ntry aesop (config := { maxRuleHeartbeats := 20000 })\nintros t\ncases t with\n| _ => \n  try simp_all; grind\n  try aesop\n  try grind\n";

        assert_axiom_lean_output(
            &axioms,
            &[
                ("height_1", height_1_expected),
                ("height_1_fwd_pattern", height_1_fwd_pattern_expected),
                ("height_2_rev", height_2_rev_expected),
                ("height_2_fwd_pattern", height_2_fwd_pattern_expected),
            ],
        );

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

        let builder = generator.build_all();

        let axioms = builder.exported_axioms().expect("Failed to export axioms");

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

        let program_str = "type [@grind] ilist = Nil | Cons of { head : int; tail : ilist }\nlet [@simp] [@grind] rec all_eq (l : ilist) (x : int) : bool = match l with | Nil -> true | Cons { head = h; tail = t } -> (h = x) && all_eq t x";
        let mut parsed_nodes = test_helpers::parse_program(program_str);
        let all_eq_fn = test_helpers::find_function(&parsed_nodes, "all_eq");
        let type_constructors = test_helpers::extract_type_decls(&parsed_nodes);

        let mut generator = AxiomGenerator::new(type_constructors.clone());
        generator
            .prepare_function(&all_eq_fn)
            .expect("Failed to prepare all_eq");

        let builder = generator.build_all();

        let axioms = builder.exported_axioms().expect("Failed to export axioms");

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

        let builder = generator.build_all();

        let all_axioms = builder
            .generate_all()
            .expect("Failed to generate all axioms");

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

        let builder = generator.build_all();

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

        let builder = generator.build_all();

        let axioms = builder.exported_axioms().expect("Failed to export axioms");

        assert_axiom_lean_output(
            &axioms,
            &[
                (
                    "len_0_infer",
                    "theorem len_0_infer : ∀ l : ilist, ∀ res : Int, ((len l res) → ((0 = res) → (is_nil l))) := by grind",
                ),
                (
                    "height_0_infer",
                    "theorem height_0_infer : ∀ t : tree, ∀ res : Int, ((height t res) → ((0 = res) → (is_leaf t))) := by grind",
                ),
                (
                    "count_0_infer",
                    "theorem count_0_infer : ∀ l : ilist, ∀ res : Int, ((count l res) → ((0 = res) → (is_nil l))) := by grind",
                ),
                (
                    "height_1_fwd_pattern",
                    "theorem height_1_fwd_pattern : ∀ t : tree, ∀ v : Int, ∀ l : tree, ∀ r : tree, ∀ res : Int, (∃ res_1 : Int, ((∃ res_2 : Int, ((height l res_1) ∧ (height r res_2) ∧ (res_1 > res_2))) → (((is_node t) ∧ ((value t) = v) ∧ ((left t) = l) ∧ ((right t) = r)) → ((height t res) → ((height l res_1) ∧ ((1 + res_1) = res)))))) := by \ntry aesop (config := { maxRuleHeartbeats := 20000 })\nintros t\ncases t with\n| _ => \n  try simp_all; grind\n  try aesop\n  try grind\n",
                ),
                (
                    "height_2_fwd_pattern",
                    "theorem height_2_fwd_pattern : ∀ t : tree, ∀ v : Int, ∀ l : tree, ∀ r : tree, ∀ res : Int, (∃ res_1 : Int, (∃ res_2 : Int, (((height l res_1) ∧ (height r res_2) ∧ ¬((res_1 > res_2))) → (((is_node t) ∧ ((value t) = v) ∧ ((left t) = l) ∧ ((right t) = r)) → ((height t res) → ((height r res_2) ∧ ((1 + res_2) = res))))))) := by \ntry aesop (config := { maxRuleHeartbeats := 20000 })\nintros t\ncases t with\n| _ => \n  try simp_all; grind\n  try aesop\n  try grind\n",
                ),
            ],
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

        let builder = generator.build_all();

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

        let builder = generator.build_all();

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

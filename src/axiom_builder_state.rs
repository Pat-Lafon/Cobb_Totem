use crate::VarName;
use crate::domain_axiom_builder;
use crate::prog_ir::{BinaryOp, LetBinding, Type};
use crate::proposition_transforms::transform_and_equality;
use crate::spec_ir::{Axiom, Expression, Parameter, Proposition, RESULT_PARAM};
use std::collections::HashSet;

/// The two result binders of the determinism (functional) axiom. Synthesized result/determinism
/// variables share the axiom's quantifier scope with the input parameters; `prepare_function`
/// rejects any input parameter that shadows one of these or [`RESULT_PARAM`], so the builders bind
/// these names as-is with no risk of a duplicate quantifier.
pub(crate) const DETERMINISM_PARAMS: [&str; 2] = ["r1", "r2"];

#[derive(Debug, Clone)]
pub(crate) struct BodyPropositionData {
    /// Constraints from structural patterns (pattern matching) and guard conditions (if-then-else).
    pub(crate) input_constraints: Vec<Proposition>,
    pub(crate) body_steps: Vec<Proposition>,
    pub(crate) result_expr: Option<Expression>,
    pub(crate) additional_parameters: Vec<Parameter>,
}

impl BodyPropositionData {
    /// Consume self and return the antecedent steps in order: input constraints, body steps, then
    /// the optional `result = result_expr` step.
    fn into_steps(self) -> (Vec<Proposition>, Vec<Parameter>) {
        let BodyPropositionData {
            mut input_constraints,
            body_steps,
            result_expr,
            additional_parameters,
        } = self;
        input_constraints.extend(body_steps);
        if let Some(result_expr) = result_expr {
            input_constraints.push(Proposition::Expr(result_expr));
        }
        (input_constraints, additional_parameters)
    }
}

/// A function ready for axiom generation: the binding, its (now-validated) return type, and one
/// `BodyPropositionData` per match/ite branch.
#[derive(Debug, Clone)]
pub(crate) struct PreparedBinding {
    pub(crate) binding: LetBinding,
    pub(crate) return_type: Type,
    pub(crate) body_propositions: Vec<BodyPropositionData>,
}

#[derive(Debug)]
pub(crate) struct AxiomBuilderState {
    prepared: Vec<PreparedBinding>,
}

impl AxiomBuilderState {
    pub(crate) fn new(prepared: Vec<PreparedBinding>) -> Self {
        Self { prepared }
    }

    /// Assemble a branch implication `(⋀ antecedent) → (∃ witnesses. ⋀ consequent)`.
    ///
    /// Each parameter is bound on the side it occurs: universal (returned, for the caller to
    /// quantify outermost) if it appears among the `antecedent` atoms, existential (nested over
    /// the consequent) if it appears only in `consequent`. The outer-∀ lift is the identity
    /// `(∃x. P(x)) → Q ≡ ∀x. (P(x) → Q)`, valid because such `x` is bound in the antecedent. A
    /// parameter occurring on neither side cannot be soundly bound and panics.
    fn branch_implication(
        antecedent: Vec<Proposition>,
        consequent: Vec<Proposition>,
        params: Vec<Parameter>,
        name: &VarName,
        idx: usize,
    ) -> (Vec<Parameter>, Proposition) {
        let antecedent_vars: HashSet<VarName> =
            antecedent.iter().flat_map(|p| p.collect_variables()).collect();
        assert!(
            !antecedent.is_empty(),
            "branch {idx} of `{name}` has an empty antecedent and cannot form an implication",
        );
        assert!(
            !consequent.is_empty(),
            "branch {idx} of `{name}` has an empty consequent and cannot form an implication",
        );
        let consequent_inner = Proposition::optional_conjunction(consequent);
        let consequent_vars = consequent_inner.collect_variables();

        let mut universals: Vec<Parameter> = Vec::new();
        let mut existentials: Vec<Parameter> = Vec::new();
        for p in params {
            if antecedent_vars.contains(&p.name) {
                universals.push(Parameter::universal(p.name, p.typ));
            } else {
                let pname = &p.name;
                assert!(
                    consequent_vars.contains(pname),
                    "parameter `{pname}` in branch {idx} of `{name}` occurs on neither side of the \
                     implication and cannot be soundly bound",
                );
                existentials.push(Parameter::existential(p.name, p.typ));
            }
        }

        let consequent = existentials.into_iter().rev().fold(consequent_inner, |acc, param| {
            Proposition::Existential(param, Box::new(acc))
        });
        let body = transform_and_equality(Proposition::Implication(
            Box::new(Proposition::optional_conjunction(antecedent)),
            Box::new(consequent),
        ));
        (universals, body)
    }

    /// Per-branch axiom shape:
    ///   `∀ inputs, ∀ lifted_params, ∀ res, (step₁ ∧ … ∧ stepₙ ∧ result_eq) → pred inputs res`.
    fn build_branch_axiom_for(
        prepared: &PreparedBinding,
        idx: usize,
        body_prop: BodyPropositionData,
    ) -> Axiom {
        let (steps, additional_parameters) = body_prop.into_steps();
        let pred = Proposition::build_relation_predicate(&prepared.binding, RESULT_PARAM);
        let (lifted_params, body) = Self::branch_implication(
            steps,
            vec![pred],
            additional_parameters,
            &prepared.binding.name,
            idx,
        );
        Axiom::from_let_binding(
            format!("{}_{}", prepared.binding.name, idx),
            &prepared.binding,
            prepared.return_type.clone(),
            &lifted_params,
            RESULT_PARAM,
            body,
        )
    }

    /// Forward-elimination axiom for branch `idx`:
    ///   `∀ inputs, ∀ res, ∀ structural_lifted.
    ///     (pred inputs res ∧ input_constraints) → ∃ body_params. (body_steps ∧ result_eq)`.
    fn build_branch_elim_axiom_for(
        prepared: &PreparedBinding,
        idx: usize,
        body_prop: BodyPropositionData,
    ) -> Axiom {
        let BodyPropositionData {
            input_constraints,
            body_steps,
            result_expr,
            additional_parameters,
        } = body_prop;

        let pred = Proposition::build_relation_predicate(&prepared.binding, RESULT_PARAM);
        let mut antecedent = vec![pred];
        antecedent.extend(input_constraints);

        let mut consequent = body_steps;
        if let Some(result_expr) = result_expr {
            consequent.push(Proposition::Expr(result_expr));
        }

        let (structural_lifted, body) = Self::branch_implication(
            antecedent,
            consequent,
            additional_parameters,
            &prepared.binding.name,
            idx,
        );

        let mut params = Parameter::from_vars(&prepared.binding.params);
        params.push(Parameter::universal(RESULT_PARAM, prepared.return_type.clone()));
        params.extend(structural_lifted);

        Axiom::new(format!("{}_{}_fwd", prepared.binding.name, idx), params, body)
    }

    /// Functional (determinism) axiom: `∀ inputs, ∀ r1 r2, (pred inputs r1 ∧ pred inputs r2) → r1 = r2`.
    fn build_functional_axiom_for(prepared: &PreparedBinding) -> Axiom {
        let binding = &prepared.binding;
        let return_type = prepared.return_type.clone();

        let [r1, r2] = DETERMINISM_PARAMS;

        let pred_r1 = Proposition::build_relation_predicate(binding, r1);
        let pred_r2 = Proposition::build_relation_predicate(binding, r2);
        let r1_eq_r2 = Proposition::Expr(Expression::BinaryOp(
            Box::new(Expression::Variable(VarName::new(r1))),
            BinaryOp::Eq,
            Box::new(Expression::Variable(VarName::new(r2))),
        ));
        let body = transform_and_equality(Proposition::Implication(
            Box::new(Proposition::And(vec![pred_r1, pred_r2])),
            Box::new(r1_eq_r2),
        ));

        let mut params = Parameter::from_vars(&binding.params);
        params.push(Parameter::universal(r1, return_type.clone()));
        params.push(Parameter::universal(r2, return_type));

        Axiom::new(format!("{}_functional", binding.name), params, body)
    }

    /// Total (existence) axiom: `∀ inputs, ∃ res, pred inputs res`.
    fn build_total_axiom_for(prepared: &PreparedBinding) -> Axiom {
        let binding = &prepared.binding;
        let pred = Proposition::build_relation_predicate(binding, RESULT_PARAM);
        let body = transform_and_equality(Proposition::Existential(
            Parameter::existential(RESULT_PARAM, prepared.return_type.clone()),
            Box::new(pred),
        ));

        let params = Parameter::from_vars(&binding.params);

        Axiom::new(format!("{}_total", binding.name), params, body)
    }

    /// TODO: Do we actually need this or can this be inlined away?
    /// One `_functional`, one `_total`, and two axioms per branch (an intro `{pred}_{idx}` and a
    /// forward-elimination `{pred}_{idx}_fwd`) for the given prepared binding.
    fn build_axioms_for(prepared: &PreparedBinding) -> Vec<Axiom> {
        let functional = Self::build_functional_axiom_for(prepared).with_suggested_proof();
        let total = Self::build_total_axiom_for(prepared).with_suggested_proof();
        let branches = prepared
            .body_propositions
            .iter()
            .enumerate()
            .flat_map(|(idx, body_prop)| {
                let intro = Self::build_branch_axiom_for(prepared, idx, body_prop.clone())
                    .with_suggested_proof();
                let fwd = Self::build_branch_elim_axiom_for(prepared, idx, body_prop.clone())
                    .with_suggested_proof();
                [intro, fwd]
            });

        [functional, total].into_iter().chain(branches).collect()
    }

    /// Domain axioms (e.g. `len_geq_0`) for each prepared binding, emitted ahead of regular axioms
    /// so they appear first in downstream output.
    fn domain_axioms(&self) -> Vec<Axiom> {
        self.prepared
            .iter()
            .flat_map(|p| domain_axiom_builder::generate(&p.binding))
            .collect()
    }

    /// Regular (functional, total, per-branch) axioms across every prepared binding.
    fn regular_axioms(&self) -> Vec<Axiom> {
        self.prepared
            .iter()
            .flat_map(|p| Self::build_axioms_for(p))
            .collect()
    }

    /// Build every axiom for every prepared binding, in emission order, and validate the result.
    /// Validation failures here indicate a builder bug (free variables, quantifier ordering, etc.)
    /// and panic with the offending axiom's diagnostic.
    pub(crate) fn generate_all(&self) -> Vec<Axiom> {
        let mut axioms = self.domain_axioms();
        axioms.extend(self.regular_axioms());

        for axiom in &axioms {
            if let Err(e) = axiom.validate() {
                panic!("axiom `{}` failed validation: {}", axiom.name, e);
            }
        }

        axioms
    }

    /// Subset of axioms that should appear in OCaml output (internal axioms excluded).
    pub(crate) fn exported_axioms(axioms: &[Axiom]) -> Vec<Axiom> {
        axioms
            .iter()
            .filter(|a| !a.is_internal())
            .cloned()
            .collect()
    }

    /// Run the Lean validator over a pre-built axiom set. On failure, returns the failing message
    /// along with the bindings under validation and the generated Lean source.
    pub(crate) fn validate_with_lean(
        &self,
        axioms: Vec<Axiom>,
        nodes: Vec<crate::prog_ir::AstNode>,
        type_decls: &[crate::prog_ir::TypeDecl],
    ) -> Result<(), String> {
        use crate::lean_backend::LeanContextBuilder;
        use crate::lean_validation::validate_lean_code;

        let mut context_builder = LeanContextBuilder::new();
        for type_decl in type_decls {
            let theorems = type_decl.generate_complete_lawful_beq();
            context_builder = context_builder
                .with_type_theorems(&type_decl.name, theorems)
                .with_helper_predicates(&type_decl.name);
        }

        let lean_code = context_builder
            .with_nodes(nodes)
            .with_axioms(axioms)
            .build();

        validate_lean_code(&lean_code).map_err(|e| {
            let bindings = self
                .prepared
                .iter()
                .map(|p| p.binding.name.0.as_str())
                .collect::<Vec<_>>()
                .join(", ");
            format!(
                "Lean validation failed for bindings [{bindings}]: {e}\n--- generated Lean code ---\n{lean_code}"
            )
        })
    }
}

#[cfg(test)]
mod tests {
    use crate::ToLean;
    use crate::spec_ir::Axiom;
    use crate::test_helpers;

    use super::AxiomBuilderState;

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
    fn test_sorted_axiom_structures() {
        let program_str = "type [@grind] ilist = Nil | Cons of { head : int; tail : ilist }\nlet [@simp] [@grind] rec sorted (l : ilist) : bool = match l with | Nil -> true | Cons { head = x; tail = xs } -> match xs with | Nil -> true | Cons { head = y; tail = ys } -> (x <= y) && sorted xs";
        let (parsed_nodes, axioms) = test_helpers::generate_axioms_with_wrapper(program_str);

        let sorted_0_expected = "theorem sorted_0 : ∀ l : ilist, ∀ res : Bool, (((is_nil l) ∧ (true = res)) → (sorted l res)) := by prove_axiom";
        let sorted_1_expected = "theorem sorted_1 : ∀ l : ilist, ∀ x : Int, ∀ xs : ilist, ∀ res : Bool, ((((is_cons l) ∧ ((head l) = x) ∧ ((tail l) = xs)) ∧ (is_nil xs) ∧ (true = res)) → (sorted l res)) := by prove_axiom";
        let sorted_2_expected = "theorem sorted_2 : ∀ l : ilist, ∀ x : Int, ∀ xs : ilist, ∀ y : Int, ∀ ys : ilist, ∀ res_0 : Bool, ∀ res : Bool, ((((is_cons l) ∧ ((head l) = x) ∧ ((tail l) = xs)) ∧ ((is_cons xs) ∧ ((head xs) = y) ∧ ((tail xs) = ys)) ∧ (sorted xs res_0) ∧ ((((x ≤ y) ∧ res_0) ∧ res) ∨ (¬(((x ≤ y) ∧ res_0)) ∧ ¬(res)))) → (sorted l res)) := by prove_axiom";

        let sorted_0_fwd_expected = "theorem sorted_0_fwd : ∀ l : ilist, ∀ res : Bool, (((sorted l res) ∧ (is_nil l)) → (true = res)) := by prove_axiom";
        let sorted_1_fwd_expected = "theorem sorted_1_fwd : ∀ l : ilist, ∀ res : Bool, ∀ x : Int, ∀ xs : ilist, (((sorted l res) ∧ ((is_cons l) ∧ ((head l) = x) ∧ ((tail l) = xs)) ∧ (is_nil xs)) → (true = res)) := by prove_axiom";
        let sorted_2_fwd_expected = "theorem sorted_2_fwd : ∀ l : ilist, ∀ res : Bool, ∀ x : Int, ∀ xs : ilist, ∀ y : Int, ∀ ys : ilist, (((sorted l res) ∧ ((is_cons l) ∧ ((head l) = x) ∧ ((tail l) = xs)) ∧ ((is_cons xs) ∧ ((head xs) = y) ∧ ((tail xs) = ys))) → (∃ res_0 : Bool, ((sorted xs res_0) ∧ ((((x ≤ y) ∧ res_0) ∧ res) ∨ (¬(((x ≤ y) ∧ res_0)) ∧ ¬(res)))))) := by prove_axiom";

        assert_axiom_lean_output(
            &axioms,
            &[
                ("sorted_0", sorted_0_expected),
                ("sorted_1", sorted_1_expected),
                ("sorted_2", sorted_2_expected),
                ("sorted_0_fwd", sorted_0_fwd_expected),
                ("sorted_1_fwd", sorted_1_fwd_expected),
                ("sorted_2_fwd", sorted_2_fwd_expected),
            ],
        );

        test_helpers::validate_axioms(parsed_nodes, axioms);
    }

    #[test]
    fn test_generate_axioms_from_mem_function() {
        let program_str = "type [@grind] ilist = Nil | Cons of { head : int; tail : ilist }\nlet [@simp] [@grind] rec mem (l : ilist) (x : int) : bool = match l with | Nil -> false | Cons { head = h; tail = t } -> (h = x) || mem t x";
        let (parsed_nodes, axioms) = test_helpers::generate_axioms_with_wrapper(program_str);

        let mem_0_expected = "theorem mem_0 : ∀ l : ilist, ∀ x : Int, ∀ res : Bool, (((is_nil l) ∧ (false = res)) → (mem l x res)) := by prove_axiom";
        let mem_1_expected = "theorem mem_1 : ∀ l : ilist, ∀ x : Int, ∀ h : Int, ∀ t : ilist, ∀ res_0 : Bool, ∀ res : Bool, ((((is_cons l) ∧ ((head l) = h) ∧ ((tail l) = t)) ∧ (mem t x res_0) ∧ ((((h = x) ∨ res_0) ∧ res) ∨ (¬(((h = x) ∨ res_0)) ∧ ¬(res)))) → (mem l x res)) := by prove_axiom";

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

        let all_eq_0_expected = "theorem all_eq_0 : ∀ l : ilist, ∀ x : Int, ∀ res : Bool, (((is_nil l) ∧ (true = res)) → (all_eq l x res)) := by prove_axiom";
        let all_eq_1_expected = "theorem all_eq_1 : ∀ l : ilist, ∀ x : Int, ∀ h : Int, ∀ t : ilist, ∀ res_0 : Bool, ∀ res : Bool, ((((is_cons l) ∧ ((head l) = h) ∧ ((tail l) = t)) ∧ (all_eq t x res_0) ∧ ((((h = x) ∧ res_0) ∧ res) ∨ (¬(((h = x) ∧ res_0)) ∧ ¬(res)))) → (all_eq l x res)) := by prove_axiom";

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

        let lb_0_expected = "theorem lower_bound_0 : ∀ t : tree, ∀ x : Int, ∀ res : Bool, (((is_leaf t) ∧ (true = res)) → (lower_bound t x res)) := by prove_axiom";
        let lb_1_expected = "theorem lower_bound_1 : ∀ t : tree, ∀ x : Int, ∀ y : Int, ∀ l : tree, ∀ r : tree, ∀ res_0 : Bool, ∀ res_1 : Bool, ∀ res : Bool, ((((is_node t) ∧ ((value t) = y) ∧ ((left t) = l) ∧ ((right t) = r)) ∧ (lower_bound l x res_0) ∧ (lower_bound r x res_1) ∧ ((((x ≤ y) ∧ (res_0 ∧ res_1)) ∧ res) ∨ (¬(((x ≤ y) ∧ (res_0 ∧ res_1))) ∧ ¬(res)))) → (lower_bound t x res)) := by prove_axiom";

        let lb_1_fwd_expected = "theorem lower_bound_1_fwd : ∀ t : tree, ∀ x : Int, ∀ res : Bool, ∀ y : Int, ∀ l : tree, ∀ r : tree, (((lower_bound t x res) ∧ ((is_node t) ∧ ((value t) = y) ∧ ((left t) = l) ∧ ((right t) = r))) → (∃ res_0 : Bool, (∃ res_1 : Bool, ((lower_bound l x res_0) ∧ (lower_bound r x res_1) ∧ ((((x ≤ y) ∧ (res_0 ∧ res_1)) ∧ res) ∨ (¬(((x ≤ y) ∧ (res_0 ∧ res_1))) ∧ ¬(res))))))) := by prove_axiom";

        assert_axiom_lean_output(
            &axioms,
            &[
                ("lower_bound_0", lb_0_expected),
                ("lower_bound_1", lb_1_expected),
                ("lower_bound_1_fwd", lb_1_fwd_expected),
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

        let expected = "theorem upper_bound_0 : ∀ t : tree, ∀ x : Int, ∀ res : Bool, (((is_leaf t) ∧ (true = res)) → (upper_bound t x res)) := by prove_axiom";
        assert_axiom_lean_output(&axioms, &[("upper_bound_0", expected)]);

        test_helpers::validate_axioms(parsed_nodes, axioms);
    }

    #[test]
    fn test_len_1_axiom_structure() {
        let program_str = "type [@grind] ilist = Nil | Cons of { head : int; tail : ilist }\nlet [@simp] [@grind] rec len (l : ilist) : int = match l with | Nil -> 0 | Cons { head = x; tail = xs } -> 1 + len xs";
        let (parsed_nodes, axioms) = test_helpers::generate_axioms_with_wrapper(program_str);

        let len_1_expected = "theorem len_1 : ∀ l : ilist, ∀ x : Int, ∀ xs : ilist, ∀ res_0 : Int, ∀ res : Int, ((((is_cons l) ∧ ((head l) = x) ∧ ((tail l) = xs)) ∧ (len xs res_0) ∧ ((1 + res_0) = res)) → (len l res)) := by prove_axiom";

        assert_axiom_lean_output(&axioms, &[("len_1", len_1_expected)]);

        test_helpers::validate_axioms(parsed_nodes, axioms);
    }

    #[test]
    fn test_len_fwd_axiom_structures() {
        let program_str = "type [@grind] ilist = Nil | Cons of { head : int; tail : ilist }\nlet [@simp] [@grind] rec len (l : ilist) : int = match l with | Nil -> 0 | Cons { head = x; tail = xs } -> 1 + len xs";
        let (parsed_nodes, axioms) = test_helpers::generate_axioms_with_wrapper(program_str);

        let len_0_fwd_expected = "theorem len_0_fwd : ∀ l : ilist, ∀ res : Int, (((len l res) ∧ (is_nil l)) → (0 = res)) := by prove_axiom";
        let len_1_fwd_expected = "theorem len_1_fwd : ∀ l : ilist, ∀ res : Int, ∀ x : Int, ∀ xs : ilist, (((len l res) ∧ ((is_cons l) ∧ ((head l) = x) ∧ ((tail l) = xs))) → (∃ res_0 : Int, ((len xs res_0) ∧ ((1 + res_0) = res)))) := by prove_axiom";

        assert_axiom_lean_output(
            &axioms,
            &[
                ("len_0_fwd", len_0_fwd_expected),
                ("len_1_fwd", len_1_fwd_expected),
            ],
        );

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
        let all_axioms = builder.generate_all();
        let axioms = AxiomBuilderState::exported_axioms(&all_axioms);

        let height_1_expected = "theorem height_1 : ∀ t : tree, ∀ v : Int, ∀ l : tree, ∀ r : tree, ∀ res_0 : Int, ∀ res_1 : Int, ∀ res : Int, ((((is_node t) ∧ ((value t) = v) ∧ ((left t) = l) ∧ ((right t) = r)) ∧ ((height l res_0) ∧ (height r res_1) ∧ (res_0 > res_1)) ∧ (height l res_0) ∧ ((1 + res_0) = res)) → (height t res)) := by prove_axiom";

        let height_2_expected = "theorem height_2 : ∀ t : tree, ∀ v : Int, ∀ l : tree, ∀ r : tree, ∀ res_0 : Int, ∀ res_1 : Int, ∀ res : Int, ((((is_node t) ∧ ((value t) = v) ∧ ((left t) = l) ∧ ((right t) = r)) ∧ ((height l res_0) ∧ (height r res_1) ∧ ¬((res_0 > res_1))) ∧ (height r res_1) ∧ ((1 + res_1) = res)) → (height t res)) := by prove_axiom";

        // Guard-pushed `res_0`/`res_1` occur in the input constraints (the ite guard), so the
        // `_fwd` direction binds them as outer universals, not consequent existentials.
        let height_1_fwd_expected = "theorem height_1_fwd : ∀ t : tree, ∀ res : Int, ∀ v : Int, ∀ l : tree, ∀ r : tree, ∀ res_0 : Int, ∀ res_1 : Int, (((height t res) ∧ ((is_node t) ∧ ((value t) = v) ∧ ((left t) = l) ∧ ((right t) = r)) ∧ ((height l res_0) ∧ (height r res_1) ∧ (res_0 > res_1))) → ((height l res_0) ∧ ((1 + res_0) = res))) := by prove_axiom";

        let height_2_fwd_expected = "theorem height_2_fwd : ∀ t : tree, ∀ res : Int, ∀ v : Int, ∀ l : tree, ∀ r : tree, ∀ res_0 : Int, ∀ res_1 : Int, (((height t res) ∧ ((is_node t) ∧ ((value t) = v) ∧ ((left t) = l) ∧ ((right t) = r)) ∧ ((height l res_0) ∧ (height r res_1) ∧ ¬((res_0 > res_1)))) → ((height r res_1) ∧ ((1 + res_1) = res))) := by prove_axiom";

        assert_axiom_lean_output(
            &axioms,
            &[
                ("height_1", height_1_expected),
                ("height_2", height_2_expected),
                ("height_1_fwd", height_1_fwd_expected),
                ("height_2_fwd", height_2_fwd_expected),
            ],
        );

        parsed_nodes = crate::wrap_all_functions(parsed_nodes);
        builder
            .validate_with_lean(all_axioms, parsed_nodes, &type_constructors)
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
        let all_axioms = builder.generate_all();
        let axioms = AxiomBuilderState::exported_axioms(&all_axioms);

        let domain_axiom = axioms
            .iter()
            .find(|a| a.name == "len_geq_0")
            .expect("len function should generate len_geq_0 axiom due to non-negativity patterns");

        assert!(domain_axiom.is_domain_specific());

        parsed_nodes = crate::wrap_all_functions(parsed_nodes);
        builder
            .validate_with_lean(all_axioms, parsed_nodes, &type_constructors)
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
        let all_axioms = builder.generate_all();
        let axioms = AxiomBuilderState::exported_axioms(&all_axioms);

        let domain_axiom_count = axioms.iter().filter(|a| a.is_domain_specific()).count();
        assert_eq!(
            domain_axiom_count, 0,
            "bool-returning function should not generate domain axioms"
        );

        parsed_nodes = crate::wrap_all_functions(parsed_nodes);
        builder
            .validate_with_lean(all_axioms, parsed_nodes, &type_constructors)
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
        let all_axioms = builder.generate_all();

        all_axioms
            .iter()
            .find(|a| a.name == "height_geq_0")
            .expect("height function should generate height_geq_0 axiom");

        let height_geq_0_expected = "@[simp, grind] theorem height_geq_0 : ∀ t : tree, ∀ n : Int, ((height t n) → (n ≥ 0)) := by prove_axiom";

        assert_axiom_lean_output(&all_axioms, &[("height_geq_0", height_geq_0_expected)]);

        parsed_nodes = crate::wrap_all_functions(parsed_nodes);
        builder
            .validate_with_lean(all_axioms, parsed_nodes, &type_constructors)
            .expect("Failed to validate axioms with Lean");
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
        let all_axioms = builder.generate_all();
        let axioms = AxiomBuilderState::exported_axioms(&all_axioms);

        assert_axiom_lean_output(
            &axioms,
            &[
                (
                    "is_even_0",
                    "theorem is_even_0 : ∀ x : Int, ∀ res : Bool, (((x = 0) ∧ (true = res)) → (is_even x res)) := by prove_axiom",
                ),
                (
                    "is_even_1",
                    "theorem is_even_1 : ∀ x : Int, ∀ res : Bool, ((¬((x = 0)) ∧ (x = 1) ∧ (false = res)) → (is_even x res)) := by prove_axiom",
                ),
                (
                    "is_even_2",
                    "theorem is_even_2 : ∀ x : Int, ∀ res : Bool, ((¬((x = 0)) ∧ ¬((x = 1)) ∧ (x = (0 - 1)) ∧ (false = res)) → (is_even x res)) := by prove_axiom",
                ),
                (
                    "is_even_3",
                    "theorem is_even_3 : ∀ x : Int, ∀ res_0 : Bool, ∀ res : Bool, ((¬((x = 0)) ∧ ¬((x = 1)) ∧ ¬((x = (0 - 1))) ∧ (x > 1) ∧ (is_even (x - 2) res_0) ∧ (res_0 = res)) → (is_even x res)) := by prove_axiom",
                ),
                (
                    "is_even_4",
                    "theorem is_even_4 : ∀ x : Int, ∀ res_1 : Bool, ∀ res : Bool, ((¬((x = 0)) ∧ ¬((x = 1)) ∧ ¬((x = (0 - 1))) ∧ ¬((x > 1)) ∧ (is_even (x + 2) res_1) ∧ (res_1 = res)) → (is_even x res)) := by prove_axiom",
                ),
            ],
        );

        parsed_nodes = crate::wrap_all_functions(parsed_nodes);
        builder
            .validate_with_lean(all_axioms, parsed_nodes, &type_constructors)
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

        let all_even_0_expected = "theorem all_even_0 : ∀ l : ilist, ∀ res : Bool, (((is_nil l) ∧ (true = res)) → (all_even l res)) := by prove_axiom";
        let all_even_1_expected = "theorem all_even_1 : ∀ l : ilist, ∀ x : Int, ∀ xs : ilist, ∀ res_2 : Bool, ∀ res_3 : Bool, ∀ res : Bool, ((((is_cons l) ∧ ((head l) = x) ∧ ((tail l) = xs)) ∧ (is_even_num x res_2) ∧ (all_even xs res_3) ∧ (((res_2 ∧ res_3) ∧ res) ∨ (¬((res_2 ∧ res_3)) ∧ ¬(res)))) → (all_even l res)) := by prove_axiom";

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

use itertools::Itertools as _;

use crate::VarName;
use crate::create_wrapper::{RESULT_PARAM, wrapper_name};
use crate::prog_ir::{LetBinding, TypeDecl};
use crate::spec_ir::{Axiom, Expression, Parameter, Proposition, Quantifier};

/// Type alias for proof tactic closure
pub type ProofTacticFn = Box<dyn Fn(&Axiom) -> String>;

/// Data for a single axiom body with its parameters
/// The proposition_steps are composed into an implication chain during axiom generation
#[derive(Debug, Clone)]
pub struct BodyPropositionData {
    pub proposition_steps: Vec<Proposition>,
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
        // Build implication chain from proposition steps
        let mut steps_body = body_prop.proposition_steps.last().unwrap().clone();
        for step in body_prop.proposition_steps[..body_prop.proposition_steps.len() - 1]
            .iter()
            .rev()
        {
            steps_body = Proposition::Implication(Box::new(step.clone()), Box::new(steps_body));
        }

        let wrapper_params = self.build_wrapper_params_for(binding);
        let body = Proposition::Implication(
            Box::new(Proposition::Predicate(
                wrapper_name(&binding.name),
                wrapper_params,
            )),
            Box::new(steps_body),
        );

        let params = self.build_and_partition_params_for(binding, &body_prop.additional_parameters);

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
        let wrapper_params = self.build_wrapper_params_for(binding);
        let mut steps_body = Proposition::Predicate(wrapper_name(&binding.name), wrapper_params);

        for step in body_prop.proposition_steps.iter().rev() {
            steps_body = Proposition::Implication(Box::new(step.clone()), Box::new(steps_body));
        }

        let params = self.build_and_partition_params_for(binding, &body_prop.additional_parameters);

        let mut axiom = Axiom {
            name: format!("{}_{}_rev", binding.name, idx),
            params,
            body: steps_body,
            proof: None,
        };

        axiom.proof = Some(proof_fn(&axiom));
        axiom
    }

    /// Build wrapper predicate parameters for a given binding
    fn build_wrapper_params_for(&self, binding: &LetBinding) -> Vec<Expression> {
        let mut params = binding
            .params
            .iter()
            .map(|p| Expression::Variable(p.0.clone()))
            .collect_vec();
        params.push(Expression::Variable(VarName(RESULT_PARAM.to_string())));
        params
    }

    /// Build and partition parameters for a given binding
    fn build_and_partition_params_for(
        &self,
        binding: &LetBinding,
        additional_parameters: &[Parameter],
    ) -> Vec<Parameter> {
        let mut params = Parameter::from_vars(&binding.params);
        let (uni, ext): (Vec<_>, Vec<_>) = additional_parameters
            .iter()
            .cloned()
            .partition(|p| p.quantifier == Quantifier::Universal);

        params.extend(uni);
        params.push(Parameter::universal(
            VarName::new(RESULT_PARAM),
            binding
                .return_type
                .clone()
                .expect("return_type must be Some after prepare_function validation"),
        ));
        params.extend(ext);
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

        // Forward axioms
        axioms.extend(body_props.iter().enumerate().map(|(idx, body_prop)| {
            self.build_forward_axiom_for(binding, idx, body_prop, proof_fn)
        }));

        // Reverse axioms
        axioms.extend(body_props.iter().enumerate().map(|(idx, body_prop)| {
            self.build_reverse_axiom_for(binding, idx, body_prop, proof_fn)
        }));

        Ok(axioms)
    }

    /// Build all axioms from the stored prepared functions
    pub fn build(&self) -> Result<Vec<Axiom>, String> {
        let proof_fn = self
            .proof
            .as_ref()
            .ok_or_else(|| "No proof function available. Use with_proof()".to_string())?;

        let mut axioms = Vec::new();

        for (binding, body_propositions) in &self.prepared {
            axioms.extend(self.build_axioms_for(binding, body_propositions, proof_fn)?);
        }

        axioms.iter().try_for_each(|axiom| axiom.validate())?;
        Ok(axioms)
    }
}

#[cfg(test)]
mod tests {
    use crate::ToLean;
    use crate::prog_ir::AstNode;
    use crate::test_helpers;

    #[test]
    fn test_generate_axioms_from_length_function() {
        let program_str = "
    type [@grind] ilist = Nil | Cons of int * ilist\n

    let [@simp] [@grind] rec len (l : ilist) : int =
    match l with
    | Nil -> 0
    | Cons (x, xs) -> 1 + len xs";

        let (mut parsed_nodes, axioms, wrapper) =
            test_helpers::generate_axioms_with_wrapper(program_str, "len");
        assert_eq!(axioms.len(), 4);
        parsed_nodes.push(AstNode::LetBinding(wrapper));
        test_helpers::validate_axioms(parsed_nodes, axioms);
    }

    #[test]
    fn test_generate_axioms_from_sorted_function() {
        let program_str = "type [@grind] ilist = Nil | Cons of int * ilist\nlet [@simp] [@grind] rec sorted (l : ilist) : bool = match l with | Nil -> true | Cons (x, xs) -> match xs with | Nil -> true | Cons (y, ys) -> (x <= y) && sorted xs";
        let (mut parsed_nodes, axioms, wrapper) =
            test_helpers::generate_axioms_with_wrapper(program_str, "sorted");
        assert_eq!(axioms.len(), 6);
        parsed_nodes.push(AstNode::LetBinding(wrapper));
        test_helpers::validate_axioms(parsed_nodes, axioms);
    }

    #[test]
    fn test_sorted_2_axiom_structure() {
        let program_str = "type [@grind] ilist = Nil | Cons of int * ilist\nlet [@simp] [@grind] rec sorted (l : ilist) : bool = match l with | Nil -> true | Cons (x, xs) -> match xs with | Nil -> true | Cons (y, ys) -> (x <= y) && sorted xs";
        let (_, axioms, _) = test_helpers::generate_axioms_with_wrapper(program_str, "sorted");

        // Find the sorted_2 axiom (forward version of Cons/Cons case)
        let sorted_2 = axioms
            .iter()
            .find(|a| a.name == "sorted_2")
            .expect("sorted_2 axiom should exist");

        let lean_output = sorted_2.to_lean();

        let expected = "theorem sorted_2 : ∀ l : ilist, ∀ x : Int, ∀ xs : ilist, ∀ y : Int, ∀ ys : ilist, ∀ res : Bool, ∃ res_0 : Bool, ((sorted_wrapper l res) → ((l = (.Cons x xs)) → ((xs = (.Cons y ys)) → ((sorted_wrapper xs res_0) → (((x ≤ y) ∧ res_0) = res))))) := by \ntry aesop (config := { maxRuleHeartbeats := 20000 })\nintros\nrefine ⟨?_, ?_⟩\nrotate_left\nall_goals try grind\nall_goals try aesop\n";
        assert_eq!(
            lean_output, expected,
            "sorted_2 axiom has incorrect structure"
        );
    }

    #[test]
    fn test_sorted_2_rev_axiom_structure() {
        let program_str = "type [@grind] ilist = Nil | Cons of int * ilist\nlet [@simp] [@grind] rec sorted (l : ilist) : bool = match l with | Nil -> true | Cons (x, xs) -> match xs with | Nil -> true | Cons (y, ys) -> (x <= y) && sorted xs";
        let (_, axioms, _) = test_helpers::generate_axioms_with_wrapper(program_str, "sorted");

        // Find the sorted_2_rev axiom (reverse version of Cons/Cons case)
        let sorted_2_rev = axioms
            .iter()
            .find(|a| a.name == "sorted_2_rev")
            .expect("sorted_2_rev axiom should exist");

        let lean_output = sorted_2_rev.to_lean();
        assert_eq!(
            lean_output,
            "theorem sorted_2_rev : ∀ l : ilist, ∀ x : Int, ∀ xs : ilist, ∀ y : Int, ∀ ys : ilist, ∀ res : Bool, ∃ res_0 : Bool, ((l = (.Cons x xs)) → ((xs = (.Cons y ys)) → ((sorted_wrapper xs res_0) → ((((x ≤ y) ∧ res_0) = res) → (sorted_wrapper l res))))) := by \ntry aesop (config := { maxRuleHeartbeats := 20000 })\nintros\nrefine ⟨?_, ?_⟩\nrotate_left\nall_goals try grind\nall_goals try aesop\n"
        );
    }

    #[test]
    fn test_generate_axioms_from_mem_function() {
        let program_str = "type [@grind] ilist = Nil | Cons of int * ilist\nlet [@simp] [@grind] rec mem (x : int) (l : ilist) : bool = match l with | Nil -> false | Cons (h, t) -> (h = x) || mem x t";
        let (mut parsed_nodes, axioms, wrapper) =
            test_helpers::generate_axioms_with_wrapper(program_str, "mem");
        assert_eq!(axioms.len(), 4);
        parsed_nodes.push(AstNode::LetBinding(wrapper));
        test_helpers::validate_axioms(parsed_nodes, axioms);
    }

    #[test]
    fn test_generate_axioms_from_all_eq_function() {
        let program_str = "type [@grind] ilist = Nil | Cons of int * ilist\nlet [@simp] [@grind] rec all_eq (l : ilist) (x : int) : bool = match l with | Nil -> true | Cons (h, t) -> (h = x) && all_eq t x";
        let (mut parsed_nodes, axioms, wrapper) =
            test_helpers::generate_axioms_with_wrapper(program_str, "all_eq");
        assert_eq!(axioms.len(), 4);
        assert_eq!(axioms[0].params.len(), 3);
        assert_eq!(axioms[1].params.len(), 6);
        parsed_nodes.push(AstNode::LetBinding(wrapper));
        test_helpers::validate_axioms(parsed_nodes, axioms);
    }

    #[test]
    fn test_generate_axioms_from_lower_bound_function() {
        let program_str = "type [@grind] tree = Leaf | Node of int * tree * tree\n

        let [@simp] [@grind] rec lower_bound (t : tree) (x : int) : bool =
            match t with
            | Leaf -> true
            | Node (y, l, r) -> x <= y && lower_bound l x && lower_bound r x";
        let (mut parsed_nodes, axioms, wrapper) =
            test_helpers::generate_axioms_with_wrapper(program_str, "lower_bound");
        assert_eq!(axioms.len(), 4);
        parsed_nodes.push(AstNode::LetBinding(wrapper));
        test_helpers::validate_axioms(parsed_nodes, axioms);
    }

    #[test]
    fn test_generate_axioms_from_upper_bound_function() {
        let program_str = "type [@grind] tree = Leaf | Node of int * tree * tree\n

        let [@simp] [@grind] rec upper_bound (t : tree) (x : int) : bool =
            match t with
            | Leaf -> true
            | Node (y, l, r) -> y <= x && upper_bound l x && upper_bound r x";
        let (mut parsed_nodes, axioms, wrapper) =
            test_helpers::generate_axioms_with_wrapper(program_str, "upper_bound");
        assert_eq!(axioms.len(), 4);
        parsed_nodes.push(AstNode::LetBinding(wrapper));
        test_helpers::validate_axioms(parsed_nodes, axioms);
    }

    #[test]
    fn test_len_1_axiom_structure() {
        let program_str = "type [@grind] ilist = Nil | Cons of int * ilist\nlet [@simp] [@grind] rec len (l : ilist) : int = match l with | Nil -> 0 | Cons (x, xs) -> 1 + len xs";
        let (_, axioms, _) = test_helpers::generate_axioms_with_wrapper(program_str, "len");

        // Find the len_1 axiom (forward version of Cons case)
        let len_1 = axioms
            .iter()
            .find(|a| a.name == "len_1")
            .expect("len_1 axiom should exist");

        // Check the complete Lean representation
        let lean_output = len_1.to_lean();
        let expected = "theorem len_1 : ∀ l : ilist, ∀ x : Int, ∀ xs : ilist, ∀ res : Int, ∃ res_0 : Int, ((len_wrapper l res) → ((l = (.Cons x xs)) → ((len_wrapper xs res_0) → ((1 + res_0) = res)))) := by \ntry aesop (config := { maxRuleHeartbeats := 20000 })\nintros\nrefine ⟨?_, ?_⟩\nrotate_left\nall_goals try grind\nall_goals try aesop\n";
        assert_eq!(lean_output, expected, "len_1 axiom has incorrect structure");
    }

    #[test]
    fn test_mem_1_rev_axiom_structure() {
        let program_str = "type [@grind] ilist = Nil | Cons of int * ilist\nlet [@simp] [@grind] rec mem (x : int) (l : ilist) : bool = match l with | Nil -> false | Cons (h, t) -> (h = x) || mem x t";
        let (_, axioms, _) = test_helpers::generate_axioms_with_wrapper(program_str, "mem");

        // Find the mem_1_rev axiom (reverse version of Cons case)
        let mem_1_rev = axioms
            .iter()
            .find(|a| a.name == "mem_1_rev")
            .expect("mem_1_rev axiom should exist");

        // Check the complete Lean representation
        let lean_output = mem_1_rev.to_lean();
        let expected = "theorem mem_1_rev : ∀ x : Int, ∀ l : ilist, ∀ h : Int, ∀ t : ilist, ∀ res : Bool, ∃ res_0 : Bool, ((l = (.Cons h t)) → ((mem_wrapper x t res_0) → ((((h = x) ∨ res_0) = res) → (mem_wrapper x l res)))) := by \ntry aesop (config := { maxRuleHeartbeats := 20000 })\nintros\nrefine ⟨?_, ?_⟩\nrotate_left\nall_goals try grind\nall_goals try aesop\n";
        assert_eq!(
            lean_output, expected,
            "mem_1_rev axiom has incorrect structure"
        );
    }

    #[test]
    fn test_generate_axioms_from_height_and_complete_functions() {
        use crate::axiom_generator::AxiomGenerator;
        use crate::create_wrapper;

        let program_str = "type [@grind] tree = Leaf | Node of int * tree * tree\n\nlet [@simp] [@grind] rec height (t : tree) : int = match t with | Leaf -> 0 | Node (v, l, r) -> 1 + ite (height l > height r) (height l) (height r)\n\nlet [@simp] [@grind] rec complete (t : tree) : bool = match t with | Leaf -> true | Node (x, l, r) -> complete l && complete r && height l = height r";

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

        let height_wrapper = create_wrapper::create_wrapper(&height_fn);
        let complete_wrapper = create_wrapper::create_wrapper(&complete_fn);
        parsed_nodes.push(AstNode::LetBinding(height_wrapper));
        parsed_nodes.push(AstNode::LetBinding(complete_wrapper));

        test_helpers::validate_axioms(parsed_nodes, axioms);
    }

    #[test]
    fn test_generate_axioms_from_bst_functions() {
        use crate::axiom_generator::AxiomGenerator;
        use crate::create_wrapper;

        let program_str = "type [@grind] tree = Leaf | Node of int * tree * tree\n\n    let [@simp] [@grind] rec lower_bound (t : tree) (x : int) : bool =\n  match t with\n  | Leaf -> true\n  | Node (y, l, r) -> x <= y && lower_bound l x && lower_bound r x\n\n    let [@simp] [@grind] rec upper_bound (t : tree) (x : int) : bool =\n  match t with\n  | Leaf -> true\n  | Node (y, l, r) -> y <= x && upper_bound l x && upper_bound r x\n\n    let [@simp] [@grind] rec bst (t : tree) : bool =\n  match t with\n  | Leaf -> true\n  | Node (x, l, r) -> bst l && bst r && upper_bound l x && lower_bound r x";

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

        let lower_bound_wrapper = create_wrapper::create_wrapper(&lower_bound_fn);
        let upper_bound_wrapper = create_wrapper::create_wrapper(&upper_bound_fn);
        let bst_wrapper = create_wrapper::create_wrapper(&bst_fn);
        parsed_nodes.push(AstNode::LetBinding(lower_bound_wrapper));
        parsed_nodes.push(AstNode::LetBinding(upper_bound_wrapper));
        parsed_nodes.push(AstNode::LetBinding(bst_wrapper));

        test_helpers::validate_axioms(parsed_nodes, axioms);
    }
}

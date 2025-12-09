use itertools::Itertools as _;

use crate::VarName;
use crate::create_wrapper::RESULT_PARAM;
use crate::prog_ir::{LetBinding, Type, TypeDecl};
use crate::spec_ir::{Axiom, Expression, Parameter, Proposition, Quantifier};

/// Data for a single axiom body with its parameters
/// The proposition_steps are composed into an implication chain during axiom generation
#[derive(Debug)]
pub struct BodyPropositionData {
    pub proposition_steps: Vec<Proposition>,
    pub additional_parameters: Vec<Parameter>,
}

/// Intermediate builder state for axiom generation
/// Separates the analysis phase from the generation phase, allowing
/// flexible generation of different axiom variants
pub struct AxiomBuilderState {
    /// Type constructors for analysis
    pub type_constructors: Vec<TypeDecl>,
    /// The function binding being analyzed
    pub function_binding: LetBinding,
    /// Body propositions with their associated parameters
    pub body_propositions: Vec<BodyPropositionData>,
    /// Universal parameters from function signature
    pub universal_params: Vec<Parameter>,
    /// Optional closure to determine proof technique for each axiom
    pub proof: Option<Box<dyn Fn(&Axiom) -> String>>,
    /// Cached wrapper binding (set by create_wrapper)
    /// TODO: we just guessed before with the name... that might end up
    /// happening here too
    wrapper_binding: Option<LetBinding>,
}

impl std::fmt::Debug for AxiomBuilderState {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("AxiomBuilderState")
            .field("type_constructors", &self.type_constructors)
            .field("function_binding", &self.function_binding)
            .field("body_propositions", &self.body_propositions)
            .field("universal_params", &self.universal_params)
            .field("proof", &self.proof.as_ref().map(|_| "<closure>"))
            .field("wrapper_binding", &self.wrapper_binding)
            .finish()
    }
}

impl AxiomBuilderState {
    /// Create a new AxiomBuilderState
    pub fn new(
        type_constructors: Vec<TypeDecl>,
        function_binding: LetBinding,
        body_propositions: Vec<BodyPropositionData>,
        universal_params: Vec<Parameter>,
    ) -> Self {
        Self {
            type_constructors,
            function_binding,
            body_propositions,
            universal_params,
            proof: None,
            wrapper_binding: None,
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

    /// Helper: extract return type from the stored function binding
    /// Panics if return_type is None (should be validated in prepare_function)
    pub fn return_type(&self) -> Type {
        self.function_binding
            .return_type
            .clone()
            .expect("return_type must be Some after prepare_function validation")
    }

    /// Apply proof function to axioms
    pub fn apply_proof(&self, mut axioms: Vec<Axiom>) -> Vec<Axiom> {
        if let Some(ref proof_fn) = self.proof {
            for axiom in &mut axioms {
                axiom.proof = Some(proof_fn(axiom));
            }
        }
        axioms
    }

    /// Generate forward axioms with integrated wrapper predicate handling
    pub fn build_forward_with_wrapper(&self) -> Result<Vec<Axiom>, String> {
        let axioms: Vec<Axiom> = self
            .body_propositions
            .iter()
            .enumerate()
            .map(|(idx, body_prop)| {
                let mut steps_body = body_prop.proposition_steps.last().unwrap().clone();
                for step in body_prop.proposition_steps[..body_prop.proposition_steps.len() - 1]
                    .iter()
                    .rev()
                {
                    steps_body =
                        Proposition::Implication(Box::new(step.clone()), Box::new(steps_body));
                }

                let mut func_params_wrapper = self
                    .universal_params
                    .iter()
                    .map(|p| Expression::Variable(p.name.clone()))
                    .collect_vec();

                func_params_wrapper.push(Expression::Variable(VarName(RESULT_PARAM.to_string())));

                let body = Proposition::Implication(
                    Box::new(Proposition::Predicate(
                        format!("{}_wrapper", self.function_binding.name),
                        func_params_wrapper,
                    )),
                    Box::new(steps_body),
                );

                let mut params = self.universal_params.clone();
                let (uni, ext): (Vec<_>, Vec<_>) = body_prop
                    .additional_parameters
                    .clone()
                    .into_iter()
                    .partition(|p| p.quantifier == Quantifier::Universal);

                params.extend(uni);
                params.push(Parameter::universal(
                    VarName::new(RESULT_PARAM),
                    self.return_type(),
                ));
                params.extend(ext);

                Axiom {
                    name: format!("{}_{}", self.function_binding.name, idx),
                    params,
                    body,
                    proof: None,
                }
            })
            .collect();

        let axioms = self.apply_proof(axioms);
        self.validate_axioms(&axioms)?;
        Ok(axioms)
    }

    /// Generate reverse axioms with integrated wrapper predicate handling
    pub fn build_reverse_with_wrapper(&self) -> Result<Vec<Axiom>, String> {
        let axioms: Vec<Axiom> = self
            .body_propositions
            .iter()
            .enumerate()
            .map(|(idx, body_prop)| {
                assert!(
                    !body_prop.proposition_steps.is_empty(),
                    "Expected at least one proposition step"
                );

                let mut func_params_wrapper = self
                    .universal_params
                    .iter()
                    .map(|p| Expression::Variable(p.name.clone()))
                    .collect_vec();

                func_params_wrapper.push(Expression::Variable(VarName(RESULT_PARAM.to_string())));

                let mut steps_body = Proposition::Predicate(
                    format!("{}_wrapper", self.function_binding.name),
                    func_params_wrapper,
                );
                /* body_prop.proposition_steps.last().unwrap().clone(); */
                for step in body_prop.proposition_steps[..body_prop.proposition_steps.len()]
                    .iter()
                    .rev()
                {
                    steps_body =
                        Proposition::Implication(Box::new(step.clone()), Box::new(steps_body));
                }

                let body = steps_body;

                let mut params = self.universal_params.clone();
                let (uni, ext): (Vec<_>, Vec<_>) = body_prop
                    .additional_parameters
                    .clone()
                    .into_iter()
                    .partition(|p| p.quantifier == Quantifier::Universal);

                params.extend(uni);
                params.push(Parameter::universal(
                    VarName::new(RESULT_PARAM),
                    self.return_type(),
                ));
                params.extend(ext);

                Axiom {
                    name: format!("{}_{}_rev", self.function_binding.name, idx),
                    params,
                    body,
                    proof: None,
                }
            })
            .collect();

        let axioms = self.apply_proof(axioms);
        self.validate_axioms(&axioms)?;
        Ok(axioms)
    }

    /// Generate both forward and reverse axioms with wrapper
    pub fn build_both(&self) -> Result<Vec<Axiom>, String> {
        let forward = self.build_forward_with_wrapper()?;
        let reverse = self.build_reverse_with_wrapper()?;
        Ok([forward, reverse].concat())
    }

    /// Create a wrapper function for the stored function binding and cache it
    pub fn create_wrapper(&mut self) -> LetBinding {
        use crate::create_wrapper;
        let binding = create_wrapper::create_wrapper(&self.function_binding);
        self.wrapper_binding = Some(binding.clone());
        binding
    }

    /// Validate that all variables in axioms are declared as parameters
    /// and that all universal quantifiers come before existential quantifiers
    fn validate_axioms(&self, axioms: &[Axiom]) -> Result<(), String> {
        axioms.iter().try_for_each(|axiom| axiom.validate())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ToLean;
    use crate::VarName;
    use crate::axiom_generator::AxiomGenerator;
    use crate::lean_backend::LeanContextBuilder;
    use crate::lean_validation::validate_lean_code;
    use crate::ocamlparser::OcamlParser;
    use crate::prog_ir::{AstNode, LetBinding};
    use crate::spec_ir::create_ilist_type;

    /// Helper: parse program, extract type and function definitions
    fn parse_program(program_str: &str) -> Vec<AstNode> {
        let nodes = OcamlParser::parse_nodes(program_str).expect("Failed to parse program");
        assert_eq!(
            nodes.len(),
            2,
            "Expected exactly two nodes (type + function)"
        );
        nodes
    }

    /// Helper: find a function binding by name
    fn find_function(nodes: &[AstNode], name: &str) -> LetBinding {
        nodes
            .iter()
            .find_map(|node| match node {
                AstNode::LetBinding(binding) if binding.name == VarName::new(name) => {
                    Some(binding.clone())
                }
                _ => None,
            })
            .expect(&format!("Expected to find {} function binding", name))
    }

    /// Helper: validate generated axioms through Lean backend
    fn validate_axioms(mut parsed_nodes: Vec<AstNode>, axioms: Vec<Axiom>, wrapper: LetBinding) {
        // Add wrapper to the nodes
        parsed_nodes.push(AstNode::LetBinding(wrapper));
        let lean_code = LeanContextBuilder::new()
            .with_nodes(parsed_nodes)
            .with_axioms(axioms)
            .build();

        validate_lean_code(&lean_code).unwrap_or_else(|e| {
            eprintln!("Generated Lean code:\n{}", lean_code);
            panic!("Generated axioms failed Lean validation:\n{}", e)
        });
    }

    /// Helper: generate axioms from a program string and function name
    fn generate_axioms_for(
        program_str: &str,
        func_name: &str,
    ) -> (Vec<AstNode>, Vec<Axiom>, LetBinding) {
        let parsed_nodes = parse_program(program_str);
        let function = find_function(&parsed_nodes, func_name);
        let mut generator = AxiomGenerator::new(vec![create_ilist_type()]);
        let mut builder = generator
            .prepare_function(&function)
            .expect("Failed to prepare function");
        let wrapper = builder.create_wrapper();
        let axioms = builder
            .with_proof(|a| a.suggest_proof_tactic())
            .build_both()
            .expect("Failed to generate axioms");
        (parsed_nodes, axioms, wrapper)
    }

    #[test]
    fn test_generate_axioms_from_length_function() {
        let program_str = "
    type [@grind] ilist = Nil | Cons of int * ilist\n

    let [@simp] [@grind] rec len (l : ilist) : int =
    match l with
    | Nil -> 0
    | Cons (x, xs) -> 1 + len xs";

        let (parsed_nodes, axioms, wrapper) = generate_axioms_for(program_str, "len");
        assert_eq!(axioms.len(), 4);
        validate_axioms(parsed_nodes, axioms, wrapper);
    }

    #[test]
    fn test_generate_axioms_from_sorted_function() {
        let program_str = "type [@grind] ilist = Nil | Cons of int * ilist\nlet [@simp] [@grind] rec sorted (l : ilist) : bool = match l with | Nil -> true | Cons (x, xs) -> match xs with | Nil -> true | Cons (y, ys) -> (x <= y) && sorted xs";
        let (parsed_nodes, axioms, wrapper) = generate_axioms_for(program_str, "sorted");
        assert_eq!(axioms.len(), 6);
        validate_axioms(parsed_nodes, axioms, wrapper);
    }

    #[test]
    fn test_sorted_2_axiom_structure() {
        let program_str = "type [@grind] ilist = Nil | Cons of int * ilist\nlet [@simp] [@grind] rec sorted (l : ilist) : bool = match l with | Nil -> true | Cons (x, xs) -> match xs with | Nil -> true | Cons (y, ys) -> (x <= y) && sorted xs";
        let (_, axioms, _) = generate_axioms_for(program_str, "sorted");

        // Find the sorted_2 axiom (forward version of Cons/Cons case)
        let sorted_2 = axioms
            .iter()
            .find(|a| a.name == "sorted_2")
            .expect("sorted_2 axiom should exist");

         let lean_output = sorted_2.to_lean();

         let expected = "theorem sorted_2 : ∀ l : ilist, ∀ x : Int, ∀ xs : ilist, ∀ y : Int, ∀ ys : ilist, ∀ res : Bool, ∃ res_0 : Bool, ((sorted_wrapper l res) → ((l = (.Cons x xs)) → ((xs = (.Cons y ys)) → ((sorted_wrapper xs res_0) → (((x ≤ y) ∧ res_0) = res))))) := by \ntry aesop (config := { maxRuleHeartbeats := 20000 })\nintros\nrefine ⟨?_, ?_⟩ <;> aesop\n";
         assert_eq!(lean_output, expected, "sorted_2 axiom has incorrect structure");
    }

    #[test]
    fn test_sorted_2_rev_axiom_structure() {
        let program_str = "type [@grind] ilist = Nil | Cons of int * ilist\nlet [@simp] [@grind] rec sorted (l : ilist) : bool = match l with | Nil -> true | Cons (x, xs) -> match xs with | Nil -> true | Cons (y, ys) -> (x <= y) && sorted xs";
        let (_, axioms, _) = generate_axioms_for(program_str, "sorted");

        // Find the sorted_2_rev axiom (reverse version of Cons/Cons case)
        let sorted_2_rev = axioms
            .iter()
            .find(|a| a.name == "sorted_2_rev")
            .expect("sorted_2_rev axiom should exist");

        // Check that the reverse axiom has the expected structure:
        // For reverse axioms, when we have And(Predicate, Expr) in a step,
        // the predicate appears as a separate antecedent, followed by the equality.
        // Pattern: (sorted_wrapper xs res_0) → ((res_0 ∧ (x ≤ y)) = res → (sorted_wrapper l res))
        let lean_output = sorted_2_rev.to_lean();
        assert_eq!(
            lean_output,
            "theorem sorted_2_rev : ∀ l : ilist, ∀ x : Int, ∀ xs : ilist, ∀ y : Int, ∀ ys : ilist, ∀ res : Bool, ∃ res_0 : Bool, ((l = (.Cons x xs)) → ((xs = (.Cons y ys)) → ((sorted_wrapper xs res_0) → ((((x ≤ y) ∧ res_0) = res) → (sorted_wrapper l res))))) := by \ntry aesop (config := { maxRuleHeartbeats := 20000 })\nintros\nrefine ⟨?_, ?_⟩ <;> aesop\n"
        );
    }

    #[test]
    fn test_generate_axioms_from_mem_function() {
        let program_str = "type [@grind] ilist = Nil | Cons of int * ilist\nlet [@simp] [@grind] rec mem (x : int) (l : ilist) : bool = match l with | Nil -> false | Cons (h, t) -> (h = x) || mem x t";
        let (parsed_nodes, axioms, wrapper) = generate_axioms_for(program_str, "mem");
        assert_eq!(axioms.len(), 4);
        validate_axioms(parsed_nodes, axioms, wrapper);
    }

    #[test]
    fn test_generate_axioms_from_all_eq_function() {
        let program_str = "type [@grind] ilist = Nil | Cons of int * ilist\nlet [@simp] [@grind] rec all_eq (l : ilist) (x : int) : bool = match l with | Nil -> true | Cons (h, t) -> (h = x) && all_eq t x";
        let (parsed_nodes, axioms, wrapper) = generate_axioms_for(program_str, "all_eq");
        assert_eq!(axioms.len(), 4);
        assert_eq!(axioms[0].params.len(), 3);
        assert_eq!(axioms[1].params.len(), 6);
        validate_axioms(parsed_nodes, axioms, wrapper);
    }

    #[test]
    fn test_len_1_axiom_structure() {
        let program_str = "type [@grind] ilist = Nil | Cons of int * ilist\nlet [@simp] [@grind] rec len (l : ilist) : int = match l with | Nil -> 0 | Cons (x, xs) -> 1 + len xs";
        let (_, axioms, _) = generate_axioms_for(program_str, "len");

        // Find the len_1 axiom (forward version of Cons case)
        let len_1 = axioms
            .iter()
            .find(|a| a.name == "len_1")
            .expect("len_1 axiom should exist");

        // Check the complete Lean representation
        let lean_output = len_1.to_lean();
        let expected = "theorem len_1 : ∀ l : ilist, ∀ x : Int, ∀ xs : ilist, ∀ res : Int, ∃ res_0 : Int, ((len_wrapper l res) → ((l = (.Cons x xs)) → ((len_wrapper xs res_0) → ((1 + res_0) = res)))) := by \ntry aesop (config := { maxRuleHeartbeats := 20000 })\nintros\nrefine ⟨?_, ?_⟩ <;> aesop\n";
        assert_eq!(lean_output, expected, "len_1 axiom has incorrect structure");
    }

    #[test]
    fn test_mem_1_rev_axiom_structure() {
        let program_str = "type [@grind] ilist = Nil | Cons of int * ilist\nlet [@simp] [@grind] rec mem (x : int) (l : ilist) : bool = match l with | Nil -> false | Cons (h, t) -> (h = x) || mem x t";
        let (_, axioms, _) = generate_axioms_for(program_str, "mem");

        // Find the mem_1_rev axiom (reverse version of Cons case)
        let mem_1_rev = axioms
            .iter()
            .find(|a| a.name == "mem_1_rev")
            .expect("mem_1_rev axiom should exist");

        // Check the complete Lean representation
        let lean_output = mem_1_rev.to_lean();
        let expected = "theorem mem_1_rev : ∀ x : Int, ∀ l : ilist, ∀ h : Int, ∀ t : ilist, ∀ res : Bool, ∃ res_0 : Bool, ((l = (.Cons h t)) → ((mem_wrapper x t res_0) → ((((h = x) ∨ res_0) = res) → (mem_wrapper x l res)))) := by \ntry aesop (config := { maxRuleHeartbeats := 20000 })\nintros\nrefine ⟨?_, ?_⟩ <;> aesop\n";
        assert_eq!(
            lean_output, expected,
            "mem_1_rev axiom has incorrect structure"
        );
    }
}

use crate::VarName;
use crate::create_wrapper::RESULT_PARAM;
use crate::prog_ir::{LetBinding, Type, TypeDecl};
use crate::spec_ir::{Axiom, Expression, Parameter, Proposition, Quantifier};

/// Suggests an appropriate proof tactic based on axiom characteristics.
/// Uses "aesop" for axioms with existential quantifiers, "grind" otherwise.
pub fn suggest_proof_tactic(axiom: &Axiom) -> String {
    if axiom
        .params
        .iter()
        .find(|p| p.quantifier == Quantifier::Existential)
        .is_some()
    {
        "\ntry aesop (config := { maxRuleHeartbeats := 20000 })
intros
refine ⟨?_, ?_⟩ <;> aesop
"
        .to_string()
    } else {
        "grind".to_string()
    }
}

/// Generates axioms in the spec IR from parsed program IR functions.
pub struct AxiomGenerator {
    /// Type declarations for looking up constructor types
    type_constructors: Vec<TypeDecl>,
}

/// Data for a single axiom body with its parameters
/// The proposition_steps are composed into an implication chain during axiom generation
#[derive(Debug)]
pub struct BodyPropositionData {
    pub proposition_steps: Vec<Proposition>,
    pub additional_universals: Vec<Parameter>,
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
    /// The function predicate: predicate(param1, param2, ...)
    pub func_prop: Proposition,
    /// Optional closure to determine proof technique for each axiom
    pub proof: Option<Box<dyn Fn(&Axiom) -> String>>,
    /// Cached wrapper binding (set by create_wrapper)
    wrapper_binding: Option<LetBinding>,
}

impl std::fmt::Debug for AxiomBuilderState {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("AxiomBuilderState")
            .field("type_constructors", &self.type_constructors)
            .field("function_binding", &self.function_binding)
            .field("body_propositions", &self.body_propositions)
            .field("universal_params", &self.universal_params)
            .field("func_prop", &self.func_prop)
            .field("proof", &self.proof.as_ref().map(|_| "<closure>"))
            .field("wrapper_binding", &self.wrapper_binding)
            .finish()
    }
}

impl AxiomBuilderState {
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
    fn return_type(&self) -> Type {
        self.function_binding
            .return_type
            .clone()
            .expect("return_type must be Some after prepare_function validation")
    }

    /// Apply proof function to axioms
    fn apply_proof(&self, mut axioms: Vec<Axiom>) -> Vec<Axiom> {
        if let Some(ref proof_fn) = self.proof {
            for axiom in &mut axioms {
                axiom.proof = Some(proof_fn(axiom));
            }
        }
        axioms
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

impl AxiomGenerator {
    /// Create a new AxiomGenerator with the given type constructors
    pub fn new(type_constructors: Vec<TypeDecl>) -> Self {
        Self { type_constructors }
    }

    /// Convert a list of (VarName, Type) pairs into universal parameters
    fn varnames_to_universals(params: &[(VarName, Type)]) -> Vec<Parameter> {
        params
            .iter()
            .map(|(name, typ)| Parameter {
                name: name.clone(),
                typ: typ.clone(),
                quantifier: Quantifier::Universal,
            })
            .collect()
    }

    /// Look up the type of a constructor parameter by constructor name and field index
    fn get_constructor_field_type(&self, constructor_name: &str, field_index: usize) -> Type {
        self.type_constructors
            .iter()
            .find_map(|type_decl| {
                type_decl
                    .variants
                    .iter()
                    .find(|variant| variant.name == constructor_name)
                    .and_then(|variant| variant.fields.get(field_index).cloned())
            })
            .expect(&format!(
                "Failed to find constructor {} at index {}",
                constructor_name, field_index
            ))
    }

    /// Extract all variables introduced by a pattern
    fn vars_from_pattern(&self, pattern: &crate::prog_ir::Pattern) -> Vec<(VarName, Type)> {
        match pattern {
            crate::prog_ir::Pattern::Variable(_name) => {
                unimplemented!("Need to infer or track the type of variable pattern")
            }
            crate::prog_ir::Pattern::Constructor(constructor_name, nested_patterns) => {
                nested_patterns
                    .iter()
                    .enumerate()
                    .flat_map(|(index, p)| match p {
                        crate::prog_ir::Pattern::Variable(name) => {
                            let typ = self.get_constructor_field_type(
                                constructor_name.get_simple_name(),
                                index,
                            );
                            vec![(name.clone(), typ)]
                        }
                        _ => self.vars_from_pattern(p),
                    })
                    .collect()
            }
            crate::prog_ir::Pattern::Literal(_) => vec![],
            crate::prog_ir::Pattern::Wildcard => unimplemented!(),
        }
    }

    /// Convert a pattern to a spec_ir Expression
    fn expr_from_pattern(&self, pattern: &crate::prog_ir::Pattern) -> Expression {
        match pattern {
            crate::prog_ir::Pattern::Variable(name) => Expression::Variable(name.clone()),
            crate::prog_ir::Pattern::Constructor(name, nested_patterns) => {
                let converted_patterns: Vec<_> = nested_patterns
                    .iter()
                    .map(|p| self.expr_from_pattern(p))
                    .collect();
                Expression::Constructor(name.clone(), converted_patterns)
            }
            crate::prog_ir::Pattern::Literal(lit) => Expression::Literal(lit.clone()),
            crate::prog_ir::Pattern::Wildcard => {
                unimplemented!()
            }
        }
    }

    /// Helper: Extract the result variable name from a predicate in an Or.
    /// Given Predicate(f, args), looks it up in var_map and returns the result variable.

                // Combine pattern constraint with branch proposition
                let combined_prop = Proposition::Implication(
                    Box::new(pattern_constraint),
                    Box::new(branch_prop),
                );

                // Combine pattern variables with branch variables
                let mut all_vars = pattern_vars;
                all_vars.extend(branch_vars);

                (combined_prop, all_vars)
            })
            .collect()
    }

    /// Augment a single proposition step for forward axioms.
            }
            _ => {
                Proposition::Implication(Box::new(prop.clone()), Box::new(func_prop.clone()))
            }
        }
    }

    /// Analyze a function and return an intermediate builder state
    pub fn prepare_function(&self, binding: &LetBinding) -> Result<AxiomBuilderState, String> {
        // Validate that binding has a return type annotation
        if binding.return_type.is_none() {
            return Err(format!(
                "Function '{}' must have an explicit return type annotation",
                binding.name
            ));
        }

        // 1. Extract parameters as universals
        let universal_params = Self::varnames_to_universals(&binding.params);

        // 2. Create function proposition
        let func_prop = Proposition::Predicate(
            binding.name.to_string(),
            binding
                .params
                .iter()
                .map(|(n, _)| Expression::Variable(n.clone()))
                .collect(),
        );

        // 3. Analyze body: extract propositions with their parameters
        let body_propositions = self.analyze_body(&binding.body)?;

        Ok(AxiomBuilderState {
            type_constructors: self.type_constructors.clone(),
            function_binding: binding.clone(),
            body_propositions,
            universal_params,
            func_prop,
            proof: None,
            wrapper_binding: None,
        })
    }

    /// Analyze function body to extract propositions with their parameters
    fn analyze_body(
        &self,
        body: &crate::prog_ir::Expression,
    ) -> Result<Vec<BodyPropositionData>, String> {
        let results = self.from_expression(body);

        Ok(results
            .into_iter()
            .map(|(proposition_steps, params)| {
                let additional_universals: Vec<_> = params
                    .into_iter()
                    .filter(|p| p.quantifier == Quantifier::Universal)
                    .collect();
                BodyPropositionData {
                    proposition_steps,
                    additional_universals,
                }
            })
            .collect())
    }

    /// Analyze expressions, building propositions
    fn from_expression(
        &self,
        body: &crate::prog_ir::Expression,
    ) -> Vec<(Vec<Proposition>, Vec<Parameter>)> {
        match body {
            crate::prog_ir::Expression::Variable(var_name) => vec![(
                vec![Proposition::Expr(Expression::Variable(var_name.clone()))],
                vec![],
            )],
            crate::prog_ir::Expression::Constructor(constructor_name, expressions) => {
                let converted_expressions: Vec<_> = expressions
                    .iter()
                    .map(|expr| {
                        let results = self.from_expression(expr);
                        assert_eq!(
                            results.len(),
                            1,
                            "Constructor argument should have exactly one result"
                        );
                        let (steps, vars) = results.into_iter().next().unwrap();
                        assert_eq!(
                            steps.len(),
                            1,
                            "Constructor argument should return exactly one step"
                        );
                        assert!(
                            vars.is_empty(),
                            "Constructor argument should not introduce variables"
                        );
                        match &steps[0] {
                            Proposition::Expr(e) => e.clone(),
                            _ => panic!("Constructor argument must be an expression"),
                        }
                    })
                    .collect();
                vec![(
                    vec![Proposition::Expr(Expression::Constructor(
                        constructor_name.clone(),
                        converted_expressions,
                    ))],
                    vec![],
                )]
            }
            crate::prog_ir::Expression::Literal(literal) => vec![(
                vec![Proposition::Expr(Expression::Literal(literal.clone()))],
                vec![],
            )],
            crate::prog_ir::Expression::UnaryOp(unary_op, expression) => {
                let results = self.from_expression(expression);
                assert_eq!(
                    results.len(),
                    1,
                    "UnaryOp operand should have exactly one result"
                );
                let (steps, vars) = results.into_iter().next().unwrap();
                assert_eq!(
                    steps.len(),
                    1,
                    "UnaryOp operand should return exactly one step"
                );
                assert!(
                    vars.is_empty(),
                    "UnaryOp operand should not introduce variables"
                );
                match &steps[0] {
                    Proposition::Expr(e) => vec![(
                        vec![Proposition::Expr(Expression::UnaryOp(
                            *unary_op,
                            Box::new(e.clone()),
                        ))],
                        vec![],
                    )],
                    _ => panic!("UnaryOp operand must be an expression"),
                }
            }
            crate::prog_ir::Expression::BinaryOp(expression, binary_op, expression1) => {
                let left_results = self.from_expression(expression);
                assert_eq!(
                    left_results.len(),
                    1,
                    "BinaryOp left operand should have exactly one result"
                );
                let (left_steps, left_vars) = left_results.into_iter().next().unwrap();
                assert_eq!(
                    left_steps.len(),
                    1,
                    "BinaryOp left operand should return exactly one step"
                );
                let left_prop = &left_steps[0];

                let right_results = self.from_expression(expression1);
                assert_eq!(
                    right_results.len(),
                    1,
                    "BinaryOp right operand should have exactly one result"
                );
                let (right_steps, right_vars) = right_results.into_iter().next().unwrap();
                assert_eq!(
                    right_steps.len(),
                    1,
                    "BinaryOp right operand should return exactly one step"
                );
                let right_prop = &right_steps[0];

                match binary_op {
                    crate::prog_ir::BinaryOp::And => vec![(
                        Proposition::And(Box::new(left_prop), Box::new(right_prop)),
                        vec![],
                    )],
                    crate::prog_ir::BinaryOp::Or => vec![(
                        Proposition::Or(Box::new(left_prop), Box::new(right_prop)),
                        vec![],
                    )],
                    _ => match (left_prop, right_prop) {
                        (Proposition::Expr(left_e), Proposition::Expr(right_e)) => vec![(
                            Proposition::Expr(Expression::BinaryOp(
                                Box::new(left_e),
                                *binary_op,
                                Box::new(right_e),
                            )),
                            vec![],
                        )],
                        _ => panic!("Non-boolean BinaryOp operands must be expressions"),
                    },
                }
            }
            crate::prog_ir::Expression::Application(func_expr, arg_exprs) => {
                let func_results = self.from_expression(func_expr);
                assert_eq!(
                    func_results.len(),
                    1,
                    "Application function should have exactly one result"
                );
                let (func_steps, func_vars) =
                    func_results.into_iter().next().unwrap();
                assert_eq!(
                    func_steps.len(),
                    1,
                    "Application function should return exactly one step"
                );
                assert!(
                    func_vars.is_empty(),
                    "Application function should not introduce variables"
                );

                let converted_args: Vec<_> = arg_exprs
                    .iter()
                    .map(|expr| {
                        let results = self.from_expression(expr);
                        assert_eq!(
                            results.len(),
                            1,
                            "Application argument should have exactly one result"
                        );
                        let (steps, vars) = results.into_iter().next().unwrap();
                        assert_eq!(
                            steps.len(),
                            1,
                            "Application argument should return exactly one step"
                        );
                        assert!(
                            vars.is_empty(),
                            "Application argument should not introduce variables"
                        );
                        match &steps[0] {
                            Proposition::Expr(e) => e.clone(),
                            _ => panic!("Application argument must be an expression"),
                        }
                    })
                    .collect();

                match func_prop {
                    Proposition::Expr(Expression::Variable(func_name)) => {
                        vec![(
                            )],
                            vec![],
                        )]
                    }
                    _ => panic!("Application function must be a variable"),
                }
            }
            crate::prog_ir::Expression::Match(scrutinee, cases) => {
                // Analyze scrutinee once to get its expression for pattern matching
                let scrutinee_results = self.from_expression(scrutinee);
                assert_eq!(
                    scrutinee_results.len(),
                    1,
                    "Match scrutinee should have exactly one result"
                );
                let (scrutinee_steps, scrutinee_vars) =
                    scrutinee_results.into_iter().next().unwrap();
                assert_eq!(
                    scrutinee_steps.len(),
                    1,
                    "Match scrutinee should have exactly one step"
                );
                assert!(
                    scrutinee_vars.is_empty(),
                    "Match scrutinee should not introduce variables"
                );

                let pattern_constraint_base = match &scrutinee_steps[0] {
                    Proposition::Expr(scrutinee_expr) => scrutinee_expr.clone(),
                    _ => panic!("Match scrutinee must be an expression"),
                };

                // For each branch of the match, create a result with pattern constraint and branch steps
                let mut all_results = vec![];
                for (pattern, branch_expr) in cases.iter() {
                    let branch_results = self.from_expression(branch_expr);

                    // Process each branch result separately
                    for (branch_steps, branch_vars) in branch_results {
                        // Extract variables introduced by the pattern
                        let pattern_vars = self.vars_from_pattern(pattern);

                        // Create pattern constraint: scrutinee = pattern
                        let pattern_expr = self.expr_from_pattern(pattern);
                        let pattern_constraint = Proposition::Expr(Expression::BinaryOp(
                            Box::new(pattern_constraint_base.clone()),
                            crate::prog_ir::BinaryOp::Eq,
                            Box::new(pattern_expr),
                        ));

                        let mut final_steps = vec![pattern_constraint];
                        final_steps.extend(branch_steps);

                        // Combine pattern variables with branch variables
                        let mut all_vars = Self::varnames_to_universals(&pattern_vars);
                        all_vars.extend(branch_vars);

                        all_results.push((final_steps, all_vars));
                    }
                }
                all_results
            }
            crate::prog_ir::Expression::Tuple(_expressions) => todo!(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ToLean;
    use crate::VarName;
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
        let generator = AxiomGenerator::new(vec![create_ilist_type()]);
        let mut builder = generator
            .prepare_function(&function)
            .expect("Failed to prepare function");
        let wrapper = builder.create_wrapper();
        let axioms = builder
            .with_proof(suggest_proof_tactic)
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

        // Check that it has the correct Lean representation with implication and equality wrapping
        let lean_output = sorted_2.to_lean();

        // The axiom should have an implication from the wrapper predicate to a conjunction
        // wrapped with equality to res. Pattern: (sorted_wrapper xs res_0) → (res_0 ∧ (x ≤ y)) = res
        assert!(
            lean_output.contains("(sorted_wrapper xs res_0) → (res_0 ∧ (x ≤ y)) = res"),
            "sorted_2 should have implication from wrapper to equality-wrapped conjunction. Got: {}",
            lean_output
        );
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
            "theorem sorted_2_rev : ∀ l : ilist, ∀ x : Int, ∀ xs : ilist, ∀ y : Int, ∀ ys : ilist, ∀ res : Bool, ∃ res_0 : Bool, ((l = (.Cons x xs)) → ((xs = (.Cons y ys)) → ((sorted_wrapper xs res_0) → ((res_0 ∧ (x ≤ y)) = res → (sorted_wrapper l res))))) := by \ntry aesop (config := { maxRuleHeartbeats := 20000 })\nintros\nrefine ⟨?_, ?_⟩ <;> aesop\n"
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
        // Nil branch: l, x, res (no existentials)
        assert_eq!(axioms[0].params.len(), 3);
        // Cons branch: l, x, h, t, res, res_0 (one existential for all_eq predicate)
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
        let expected = "theorem mem_1_rev : ∀ x : Int, ∀ l : ilist, ∀ h : Int, ∀ t : ilist, ∀ res : Bool, ∃ res_0 : Bool, ((l = (.Cons h t)) → ((mem_wrapper x t res_0) → ((res_0 ∨ (h = x)) = res → (mem_wrapper x l res)))) := by \ntry aesop (config := { maxRuleHeartbeats := 20000 })\nintros\nrefine ⟨?_, ?_⟩ <;> aesop\n";
        assert_eq!(
            lean_output, expected,
            "mem_1_rev axiom has incorrect structure"
        );
    }
}

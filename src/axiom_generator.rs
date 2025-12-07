use crate::VarName;
use crate::free_variable_validation::ValidateNoFreeVariables;
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
        "aesop".to_string()
    } else {
        "grind".to_string()
    }
}

/// Generates axioms in the spec IR from parsed program IR functions.
pub struct AxiomGenerator {
    /// Type declarations for looking up constructor types
    pub type_constructors: Vec<TypeDecl>,
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

    /// Process a single match branch: create a proposition combining the pattern constraint and branch result
    fn process_match_branch(
        &self,
        pattern: &crate::prog_ir::Pattern,
        branch_expr: &crate::prog_ir::Expression,
        scrutinee: &crate::prog_ir::Expression,
    ) -> Vec<(Proposition, Vec<(VarName, Type)>)> {
        let branch_results = self.from_expression(branch_expr);

        branch_results
            .into_iter()
            .map(|(branch_prop, branch_vars)| {
                // Extract variables introduced by the pattern
                let pattern_vars = self.vars_from_pattern(pattern);

                // Create pattern constraint: scrutinee = pattern
                let scrutinee_results = self.from_expression(scrutinee);
                assert_eq!(
                    scrutinee_results.len(),
                    1,
                    "Match scrutinee should have exactly one result"
                );
                let (scrutinee_prop, scrutinee_vars) =
                    scrutinee_results.into_iter().next().unwrap();
                assert!(
                    scrutinee_vars.is_empty(),
                    "Match scrutinee should not introduce variables"
                );

                let pattern_constraint = match scrutinee_prop {
                    Proposition::Expr(scrutinee_expr) => {
                        let pattern_expr = self.expr_from_pattern(pattern);
                        Proposition::Expr(Expression::BinaryOp(
                            Box::new(scrutinee_expr),
                            crate::prog_ir::BinaryOp::Eq,
                            Box::new(pattern_expr),
                        ))
                    }
                    _ => panic!("Match scrutinee must be an expression"),
                };

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

    /// Build axioms for a given direction (forward or reverse)
    fn build_axioms_for_direction(
        &self,
        binding: &LetBinding,
        possible_bodies: &[(Proposition, Vec<(VarName, Type)>)],
        universals: &[Parameter],
        func_prop_start: &Proposition,
        reverse: bool,
    ) -> Vec<Axiom> {
        possible_bodies
            .iter()
            .enumerate()
            .map(|(idx, (prop, additional_vars))| {
                let mut params = universals.to_vec();
                params.extend(Self::varnames_to_universals(additional_vars));
                // Sort parameters by name for consistent ordering
                params.sort_by(|a, b| a.name.cmp(&b.name));

                let body_prop = if reverse {
                    // For reverse direction, append func_prop_start as a new final consequent
                    Self::append_to_implication_chain(prop, func_prop_start)
                } else {
                    Proposition::Implication(Box::new(func_prop_start.clone()), Box::new(prop.clone()))
                };

                Axiom {
                    name: format!(
                        "{}_{}{}",
                        binding.name,
                        idx,
                        if reverse { "_rev" } else { "" }
                    ),
                    params,
                    body: body_prop,
                    proof: None,
                }
            })
            .collect()
    }

    /// Append a new consequent to the end of an implication chain.
    /// For (A → B → C), appends func_prop to create (A → B → C → func_prop).
    fn append_to_implication_chain(prop: &Proposition, func_prop: &Proposition) -> Proposition {
        match prop {
            Proposition::Implication(antecedent, consequent) => {
                let inner = Self::append_to_implication_chain(consequent, func_prop);
                Proposition::Implication(antecedent.clone(), Box::new(inner))
            }
            _ => {
                Proposition::Implication(Box::new(prop.clone()), Box::new(func_prop.clone()))
            }
        }
    }

    /// Generate axioms from a function definition
    pub fn from_let_binding(&self, binding: &LetBinding) -> Result<Vec<Axiom>, String> {
        // Extract parameters from the let binding and convert them to universals
        let universals = Self::varnames_to_universals(&binding.params);

        let func_prop_start = Proposition::Predicate(
            binding.name.to_string(),
            binding
                .params
                .iter()
                .map(|(n, _)| crate::spec_ir::Expression::Variable(n.clone()))
                .collect(),
        );

        let possible_bodies = self.from_expression(&binding.body);

        // Generate forward axioms
        let mut axioms =
            self.build_axioms_for_direction(binding, &possible_bodies, &universals, &func_prop_start, false);

        // Generate reverse axioms
        axioms.extend(self.build_axioms_for_direction(
            binding,
            &possible_bodies,
            &universals,
            &func_prop_start,
            true,
        ));

        // Validate that all variables in each axiom body are declared as parameters
        for axiom in &axioms {
            axiom.validate_no_free_variables()?;
        }

        Ok(axioms)
    }

    fn from_expression(
        &self,
        body: &crate::prog_ir::Expression,
    ) -> Vec<(Proposition, Vec<(VarName, Type)>)> {
        match body {
            crate::prog_ir::Expression::Variable(var_name) => vec![(
                Proposition::Expr(Expression::Variable(var_name.clone())),
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
                        let (prop, vars) = results.into_iter().next().unwrap();
                        assert!(
                            vars.is_empty(),
                            "Constructor argument should not introduce variables"
                        );
                        match prop {
                            Proposition::Expr(e) => e,
                            _ => panic!("Constructor argument must be an expression"),
                        }
                    })
                    .collect();
                vec![(
                    Proposition::Expr(Expression::Constructor(
                        constructor_name.clone(),
                        converted_expressions,
                    )),
                    vec![],
                )]
            }
            crate::prog_ir::Expression::Literal(literal) => vec![(
                Proposition::Expr(Expression::Literal(literal.clone())),
                vec![],
            )],
            crate::prog_ir::Expression::UnaryOp(unary_op, expression) => {
                let results = self.from_expression(expression);
                assert_eq!(
                    results.len(),
                    1,
                    "UnaryOp operand should have exactly one result"
                );
                let (prop, vars) = results.into_iter().next().unwrap();
                assert!(
                    vars.is_empty(),
                    "UnaryOp operand should not introduce variables"
                );
                match prop {
                    Proposition::Expr(e) => vec![(
                        Proposition::Expr(Expression::UnaryOp(*unary_op, Box::new(e))),
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
                let (left_prop, left_vars) = left_results.into_iter().next().unwrap();
                assert!(
                    left_vars.is_empty(),
                    "BinaryOp left operand should not introduce variables"
                );

                let right_results = self.from_expression(expression1);
                assert_eq!(
                    right_results.len(),
                    1,
                    "BinaryOp right operand should have exactly one result"
                );
                let (right_prop, right_vars) = right_results.into_iter().next().unwrap();
                assert!(
                    right_vars.is_empty(),
                    "BinaryOp right operand should not introduce variables"
                );

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
                let (func_prop, func_vars) = func_results.into_iter().next().unwrap();
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
                        let (prop, vars) = results.into_iter().next().unwrap();
                        assert!(
                            vars.is_empty(),
                            "Application argument should not introduce variables"
                        );
                        match prop {
                            Proposition::Expr(e) => e,
                            _ => panic!("Application argument must be an expression"),
                        }
                    })
                    .collect();

                match func_prop {
                    Proposition::Expr(Expression::Variable(func_name)) => {
                        vec![(
                            Proposition::Predicate(func_name.to_string(), converted_args),
                            vec![],
                        )]
                    }
                    _ => panic!("Application function must be a variable"),
                }
            }
            crate::prog_ir::Expression::Match(scrutinee, cases) => {
                // For each branch of the match, create a proposition
                // The proposition includes both the pattern constraint and the branch result
                cases
                    .iter()
                    .flat_map(|(pattern, branch_expr)| {
                        self.process_match_branch(pattern, branch_expr, scrutinee)
                    })
                    .collect()
            }
            crate::prog_ir::Expression::Tuple(_expressions) => todo!(),
        }
    }

    /// Generate axioms from an AST node
    pub fn from_ast_node(&self, node: &AstNode) -> Result<Vec<Axiom>, String> {
        match node {
            AstNode::TypeDeclaration(_) => {
                Err("Cannot generate axioms from type declarations".to_string())
            }
            AstNode::LetBinding(binding) => self.from_let_binding(binding),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lean_backend::LeanContextBuilder;
    use crate::lean_validation::validate_lean_code;
    use crate::ocamlparser::OcamlParser;
    use crate::spec_ir::create_ilist_type;
    use crate::{ToLean as _, VarName};



    #[test]
    fn test_generate_axioms_from_length_function() {
        let program_str = "type [@grind] ilist = Nil | Cons of int * ilist\nlet [@simp] [@grind] rec len (l : ilist) (n : int) : bool = match l with | Nil -> n = 0 | Cons (x, xs) -> len xs (n - 1)";
        let parsed_nodes =
            OcamlParser::parse_nodes(program_str).expect("Failed to parse program");
        assert_eq!(parsed_nodes.len(), 2, "Expected exactly two nodes (type + function)");

        let len_function = parsed_nodes
            .iter()
            .find_map(|node| match node {
                AstNode::LetBinding(binding) if binding.name == VarName::new("len") => {
                    Some(binding.clone())
                }
                _ => None,
            })
            .expect("Expected to find len function binding");

        let generator = AxiomGenerator::new(vec![create_ilist_type()]);
        let mut axioms = generator
            .from_let_binding(&len_function)
            .expect("Failed to generate axioms");

        // Set proof to grind for all axioms
        for axiom in &mut axioms {
            axiom.proof = Some("grind".to_string());
        }

        // Should generate exactly the expected axioms for len: len_nil, len_cons, and their reverses
        assert_eq!(axioms.len(), 4, "Expected 4 axioms (forward and reverse)");

        // len_nil (forward): ∀ l : ilist, ∀ n : Int, ((len l n) → ((l = .Nil) → (n = 0)))
        let len_nil = &axioms[0];
        assert_eq!(
            len_nil.to_lean(),
            "theorem len_0 : ∀ l : ilist, ∀ n : Int, ((len l n) → ((l = .Nil) → (n = 0))) := by grind"
        );

        // len_cons (forward)
        let len_cons = &axioms[1];
        let forward_axiom = len_cons.to_lean();
        assert_eq!(
            forward_axiom,
            "theorem len_1 : ∀ l : ilist, ∀ n : Int, ∀ x : Int, ∀ xs : ilist, ((len l n) → ((l = (.Cons x xs)) → (len xs (n - 1)))) := by grind"
        );

        // Verify that reverse axioms exist at indices 2 and 3
        let len_nil_rev = &axioms[2];
        assert_eq!(len_nil_rev.name, "len_0_rev");
        let len_cons_rev = &axioms[3];
        assert_eq!(len_cons_rev.name, "len_1_rev");

        // Validate generated theorems through Lean backend
        let lean_code = LeanContextBuilder::new()
            .with_nodes(parsed_nodes)
            .with_axioms(axioms)
            .build();

        validate_lean_code(&lean_code)
            .unwrap_or_else(|e| panic!("Generated axioms failed Lean validation:\n{}", e));
    }

    #[test]
    fn test_generate_axioms_from_sorted_function() {
        let program_str = "type [@grind] ilist = Nil | Cons of int * ilist\nlet [@simp] [@grind] rec sorted (l : ilist) : bool = match l with | Nil -> true | Cons (x, xs) -> match xs with | Nil -> true | Cons (y, ys) -> (x <= y) && sorted xs";
        let parsed_nodes = OcamlParser::parse_nodes(program_str)
            .expect("Failed to parse program");
        assert_eq!(parsed_nodes.len(), 2, "Expected exactly two nodes (type + function)");

        let sorted_function = parsed_nodes
            .iter()
            .find_map(|node| match node {
                AstNode::LetBinding(binding) if binding.name == VarName::new("sorted") => {
                    Some(binding.clone())
                }
                _ => None,
            })
            .expect("Expected to find sorted function binding");

        let generator = AxiomGenerator::new(vec![create_ilist_type()]);
        let mut axioms = generator
            .from_let_binding(&sorted_function)
            .expect("Failed to generate axioms");

        // Set proof to grind for all axioms
        for axiom in &mut axioms {
            axiom.proof = Some("grind".to_string());
        }

        // Should generate axioms for the sorted function
        assert!(axioms.len() == 6, "Expected at least 4 axioms for sorted (forward and reverse)");

        // Validate generated theorems through Lean backend
        let lean_code = LeanContextBuilder::new()
            .with_nodes(parsed_nodes)
            .with_axioms(axioms)
            .build();

        validate_lean_code(&lean_code)
            .unwrap_or_else(|e| panic!("Generated axioms failed Lean validation:\n{}", e));
    }

    #[test]
    fn test_generate_axioms_from_mem_function() {
        let program_str = "type [@grind] ilist = Nil | Cons of int * ilist\n

        let [@simp] [@grind] rec mem (x : int) (l : ilist) : bool = match l with | Nil -> false | Cons (h, t) -> (h = x) || mem x t";
        let parsed_nodes =
            OcamlParser::parse_nodes(program_str).expect("Failed to parse program");
        assert_eq!(parsed_nodes.len(), 2, "Expected exactly two nodes (type + function)");

        let mem_function = parsed_nodes
            .iter()
            .find_map(|node| match node {
                AstNode::LetBinding(binding) if binding.name == VarName::new("mem") => {
                    Some(binding.clone())
                }
                _ => None,
            })
            .expect("Expected to find mem function binding");

        let generator = AxiomGenerator::new(vec![create_ilist_type()]);
        let mut axioms = generator
            .from_let_binding(&mem_function)
            .expect("Failed to generate axioms");

        // Set proof to grind for all axioms
        for axiom in &mut axioms {
            axiom.proof = Some("grind".to_string());
        }

        // Should generate axioms for mem: mem_nil, mem_cons, and their reverses
        assert_eq!(axioms.len(), 4, "Expected 4 axioms for mem (forward and reverse)");

        // Validate generated theorems through Lean backend
        let lean_code = LeanContextBuilder::new()
            .with_nodes(parsed_nodes)
            .with_axioms(axioms)
            .build();

        validate_lean_code(&lean_code)
            .unwrap_or_else(|e| panic!("Generated axioms failed Lean validation:\n{}", e));
    }

    #[test]
    fn test_generate_axioms_from_all_eq_function() {
        let program_str = "type [@grind] ilist = Nil | Cons of int * ilist\n

        let [@simp] [@grind] rec all_eq (l : ilist) (x : int) : bool =
        match l with | Nil -> true | Cons (h, t) -> (h = x) && all_eq t x";
        let parsed_nodes =
            OcamlParser::parse_nodes(program_str).expect("Failed to parse program");
        assert_eq!(parsed_nodes.len(), 2, "Expected exactly two nodes (type + function)");

        let all_eq_function = parsed_nodes
            .iter()
            .find_map(|node| match node {
                AstNode::LetBinding(binding) if binding.name == VarName::new("all_eq") => {
                    Some(binding.clone())
                }
                _ => None,
            })
            .expect("Expected to find all_eq function binding");

        let generator = AxiomGenerator::new(vec![create_ilist_type()]);
        let mut axioms = generator
            .from_let_binding(&all_eq_function)
            .expect("Failed to generate axioms");

        // Set proof to grind for all axioms
        for axiom in &mut axioms {
            axiom.proof = Some("grind".to_string());
        }

        // Should generate axioms for all_eq: all_eq_nil, all_eq_cons, and their reverses
        assert_eq!(axioms.len(), 4, "Expected 4 axioms for all_eq (forward and reverse)");

        // Validate generated theorems through Lean backend
        let lean_code = LeanContextBuilder::new()
            .with_nodes(parsed_nodes)
            .with_axioms(axioms)
            .build();

        validate_lean_code(&lean_code)
            .unwrap_or_else(|e| panic!("Generated axioms failed Lean validation:\n{}", e));
    }
}

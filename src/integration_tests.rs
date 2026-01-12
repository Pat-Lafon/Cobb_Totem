#[cfg(test)]
mod integration_tests {
    use crate::axiom_generator::AxiomGenerator;
    use crate::create_wrapper;
    use crate::lean_backend::LeanContextBuilder;
    use crate::lean_validation::validate_lean_code;
    use crate::ocamlparser::OcamlParser;
    use crate::prog_ir::AstNode;

    fn validate_program(program_str: &str, func_names: &[&str]) {
        let parsed_nodes = OcamlParser::parse_nodes(program_str)
            .unwrap_or_else(|e| panic!("Failed to parse program: {}", e));

        let type_decls = parsed_nodes
            .iter()
            .filter_map(|node| match node {
                AstNode::TypeDeclaration(type_decl) => Some(type_decl.clone()),
                _ => None,
            })
            .collect::<Vec<_>>();

        let mut all_nodes = parsed_nodes.clone();
        let mut generator = AxiomGenerator::new(type_decls.clone());

        // Prepare all functions in the program
        for func_name in func_names {
            let function = parsed_nodes
                .iter()
                .find_map(|node| match node {
                    AstNode::LetBinding(binding) if binding.name.as_str() == *func_name => {
                        Some(binding.clone())
                    }
                    _ => None,
                })
                .unwrap_or_else(|| panic!("Expected to find {} function", func_name));

            generator
                .prepare_function(&function)
                .expect("Failed to prepare function");

            let wrapper = create_wrapper::create_wrapper(&function);
            all_nodes.push(AstNode::LetBinding(wrapper));
        }

        // Build all axioms at once
        let builder = generator.build_all();
        let all_axioms = builder
            .with_proof(|a| a.suggest_proof_tactic())
            .build()
            .expect("Failed to generate axioms");

        let mut context_builder = LeanContextBuilder::new();
        for type_decl in type_decls {
            let theorems = type_decl.generate_complete_lawful_beq();
            context_builder = context_builder.with_type_theorems(&type_decl.name, theorems);
        }

        let lean_code = context_builder
            .with_nodes(all_nodes)
            .with_axioms(all_axioms)
            .build();

        validate_lean_code(&lean_code).unwrap_or_else(|e| {
            eprintln!("Generated Lean code:\n{}", lean_code);
            panic!("Generated axioms failed Lean validation:\n{}", e)
        });
    }

    #[test]
    fn test_sorted_list_program() {
        let program_str = "type [@grind] ilist = Nil | Cons of int * ilist

let [@simp] [@grind] rec sorted (l : ilist) : bool = match l with
| Nil -> true
| Cons (x, xs) -> match xs with
| Nil -> true
| Cons (y, ys) -> (x <= y) && sorted xs";

        validate_program(program_str, &["sorted"]);
    }

    #[test]
    fn test_list_length_program() {
        let program_str = "type [@grind] ilist = Nil | Cons of int * ilist

let [@simp] [@grind] rec len (l : ilist) : int =
match l with
| Nil -> 0
| Cons (x, xs) -> 1 + len xs";

        validate_program(program_str, &["len"]);
    }

    #[test]
    fn test_tree_height_program() {
        let program_str = "type [@grind] tree = Leaf | Node of int * tree * tree

let [@simp] [@grind] rec height (t : tree) : int = match t with | Leaf -> 0 | Node (v, l, r) -> 1 + ite (height l > height r) (height l) (height r)";

        validate_program(program_str, &["height"]);
    }

    #[test]
    fn test_tree_height_and_complete_program() {
        let program_str = "type [@grind] tree = Leaf | Node of int * tree * tree

let [@simp] [@grind] rec height (t : tree) : int = match t with | Leaf -> 0 | Node (v, l, r) -> 1 + ite (height l > height r) (height l) (height r)

let [@simp] [@grind] rec complete (t : tree) : bool =
match t with
| Leaf -> true
| Node (x, l, r) -> complete l && complete r && height l = height r";

        validate_program(program_str, &["height", "complete"]);
    }

    #[test]
    fn test_bst_tree_program() {
        let program_str = "type [@grind] tree = Leaf | Node of int * tree * tree

let [@simp] [@grind] rec lower_bound (t : tree) (x : int) : bool =
match t with
| Leaf -> true
| Node (y, l, r) -> x <= y && lower_bound l x && lower_bound r x

let [@simp] [@grind] rec upper_bound (t : tree) (x : int) : bool =
match t with
| Leaf -> true
| Node (y, l, r) -> y <= x && upper_bound l x && upper_bound r x

let [@simp] [@grind] rec bst (t : tree) : bool =
match t with
| Leaf -> true
| Node (x, l, r) -> bst l && bst r && upper_bound l x && lower_bound r x";

        validate_program(program_str, &["lower_bound", "upper_bound", "bst"]);
    }

    #[test]
    fn test_rbtree_invariants_program() {
        let program_str = "type [@grind] rbtree = Rbtleaf | Rbtnode of bool * rbtree * int * rbtree

let [@simp] [@grind] rec num_black (t : rbtree) (h : int) : bool =
  match t with
  | Rbtleaf -> h = 0
  | Rbtnode (c, l, v, r) ->
      if c then num_black l (h - 1) && num_black r (h - 1)
      else num_black l h && num_black r h

let [@simp] [@grind] rec no_red_red (t : rbtree) : bool =
  match t with
  | Rbtleaf -> true
  | Rbtnode (c, l, v, r) ->
      if not c then no_red_red l && no_red_red r
      else
        match (l, r) with
        | Rbtnode (c', l1, v1, r1), Rbtnode (c'', l2, v2, r2) ->
            (not c') && (not c'') && no_red_red l && no_red_red r
        | Rbtnode (c', l1, v1, r1), Rbtleaf -> (not c') && no_red_red l
        | Rbtleaf, Rbtnode (c'', l2, v2, r2) -> (not c'') && no_red_red r
        | Rbtleaf, Rbtleaf -> true

let [@simp] [@grind] rec rb_root_color (t : rbtree) (c : bool) : bool =
  match t with Rbtleaf -> false | Rbtnode (c', l, v, r) -> c = c'

let [@simp] [@grind] rec rbtree_invariant (t : rbtree) (h : int) : bool =
  match t with
  | Rbtleaf -> h = 0
  | Rbtnode (c, l, v, r) ->
      if not c then rbtree_invariant l (h - 1) && rbtree_invariant r (h - 1)
      else
        ((not (rb_root_color l true)) && not (rb_root_color r true))
        && rbtree_invariant l h && rbtree_invariant r h

let [@simp] [@grind] rec rbdepth (t : rbtree) : int =
  match t with
  | Rbtleaf -> 0
  | Rbtnode (c, l, v, r) -> 1 + ite (rbdepth l > rbdepth r) (rbdepth l) (rbdepth r)";

        validate_program(
            program_str,
            &[
                "num_black",
                "no_red_red",
                "rb_root_color",
                "rbtree_invariant",
                "rbdepth",
            ],
        );
    }
}

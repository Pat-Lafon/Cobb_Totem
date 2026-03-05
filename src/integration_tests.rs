#[cfg(test)]
mod integration_tests {
    use crate::axiom_generator::AxiomGenerator;
    use crate::ocamlparser::OcamlParser;
    use crate::prog_ir::AstNode;

    fn validate_program(program_str: &str) {
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
        for node in &parsed_nodes {
            if let AstNode::LetBinding(binding) = node {
                generator
                    .prepare_function(binding)
                    .expect("Failed to prepare function");
            }
        }

        // Wrap all functions with impl+wrapper
        all_nodes = crate::wrap_all_functions(all_nodes);

        // Build all axioms at once
        let builder = generator.build_all();

        // Validate through Lean backend
        builder
            .validate_with_lean(all_nodes.clone(), &type_decls)
            .unwrap_or_else(|e| panic!("Generated axioms failed Lean validation:\n{}", e));
    }

    #[test]
    fn test_sorted_list_program() {
        let program_str = "type [@grind] ilist = Nil | Cons of { head : int; tail : ilist }

let [@simp] [@grind] rec sorted (l : ilist) : bool = match l with
| Nil -> true
| Cons { head = x; tail = xs } -> match xs with
| Nil -> true
| Cons { head = y; tail = ys } -> (x <= y) && sorted xs";

        validate_program(program_str);
    }

    #[test]
    fn test_list_length_program() {
        let program_str = "type [@grind] ilist = Nil | Cons of { head : int; tail : ilist }

    let [@simp] [@grind] rec len (l : ilist) : int =
    match l with
    | Nil -> 0
    | Cons { head = x; tail = xs } -> 1 + len xs";

        validate_program(program_str);
    }

    #[test]
    fn test_tree_height_program() {
        let program_str = "type [@grind] tree = Leaf | Node of { value : int; left : tree; right : tree }

let [@simp] [@grind] rec height (t : tree) : int = match t with | Leaf -> 0 | Node { value = v; left = l; right = r } -> ite (height l > height r) (1 + height l) (1 + height r)";

        validate_program(program_str);
    }

    #[test]
    fn test_tree_height_and_complete_program() {
        let program_str = "type [@grind] tree = Leaf | Node of { value : int; left : tree; right : tree }

let [@simp] [@grind] rec height (t : tree) : int = match t with | Leaf -> 0 | Node { value = v; left = l; right = r } -> ite (height l > height r) (1 + height l) (1 + height r)

let [@simp] [@grind] rec complete (t : tree) : bool =
match t with
| Leaf -> true
| Node { value = x; left = l; right = r } -> complete l && complete r && height l = height r";

        validate_program(program_str);
    }

    #[test]
    fn test_bst_tree_program() {
        let program_str =
            "type [@grind] tree = Leaf | Node of { value : int; left : tree; right : tree }

let [@simp] [@grind] rec lower_bound (t : tree) (x : int) : bool =
match t with
| Leaf -> true
| Node { value = y; left = l; right = r } -> x <= y && lower_bound l x && lower_bound r x

let [@simp] [@grind] rec upper_bound (t : tree) (x : int) : bool =
match t with
| Leaf -> true
| Node { value = y; left = l; right = r } -> y <= x && upper_bound l x && upper_bound r x

let [@simp] [@grind] rec bst (t : tree) : bool =
match t with
| Leaf -> true
| Node { value = x; left = l; right = r } -> bst l && bst r && upper_bound l x && lower_bound r x";

        validate_program(program_str);
    }

    #[test]
    fn test_rbtree_invariants_program() {
        let program_str = "type [@grind] rbtree = Rbtleaf | Rbtnode of { color : bool; left : rbtree; value : int; right : rbtree }

let [@simp] [@grind] rec num_black (t : rbtree) (h : int) : bool =
  match t with
  | Rbtleaf -> h = 0
  | Rbtnode { color = c; left = l; value = _; right = r } ->
      if not c then num_black l (h - 1) && num_black r (h - 1)
      else num_black l h && num_black r h

let [@simp] [@grind] rec no_red_red (t : rbtree) : bool =
  match t with
  | Rbtleaf -> true
  | Rbtnode { color = c; left = l; value = _; right = r } ->
      if c then no_red_red l && no_red_red r
      else
        match l with
        | Rbtnode { color = c'; left = _; value = _; right = _ } ->
            (match r with
            | Rbtnode { color = c''; left = _; value = _; right = _ } ->
                c' && c'' && no_red_red l && no_red_red r
            | Rbtleaf -> c' && no_red_red l)
        | Rbtleaf ->
            (match r with
            | Rbtnode { color = c''; left = _; value = _; right = _ } -> c'' && no_red_red r
            | Rbtleaf -> true)

let [@simp] [@grind] rb_root_color (t : rbtree) (c : bool) : bool =
  match t with Rbtleaf -> false | Rbtnode { color = c'; left = _; value = _; right = _ } -> c = c'

let [@simp] [@grind] rbtree_invariant (t : rbtree) (h : int) : bool =
  no_red_red t && num_black t h && rb_root_color t false";

        validate_program(program_str);
    }
}

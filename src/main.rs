use cobb_totem::ToLean as _;
use cobb_totem::axiom_generator::AxiomGenerator;
use cobb_totem::create_wrapper::create_wrapper;
use cobb_totem::lean_backend::LeanContextBuilder;
use cobb_totem::lean_validation::validate_lean_code;
use cobb_totem::ocamlparser::OcamlParser;
use cobb_totem::prog_ir::AstNode;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    /* let program_str = "
    type [@grind] ilist = Nil | Cons of int * ilist\n

    let [@simp] [@grind] rec sorted (l : ilist) : bool = match l with
    | Nil -> true
    | Cons (x, xs) -> match xs with
    | Nil -> true
    | Cons (y, ys) -> (x <= y) && sorted xs"; */

    /* let program_str = "
    type [@grind] ilist = Nil | Cons of int * ilist\n

    let [@simp] [@grind] rec len (l : ilist) : int =
    match l with
    | Nil -> 0
    | Cons (x, xs) -> 1 + len xs"; */

    /*     let program_str = "type [@grind] tree = Leaf | Node of int * tree * tree

    let [@simp] [@grind] rec height (t : tree) : int = match t with | Leaf -> 0 | Node (v, l, r) -> 1 + ite (height l > height r) (height l) (height r)"; */

    /* let program_str = "type [@grind] tree = Leaf | Node of int * tree * tree

    let [@simp] [@grind] rec height (t : tree) : int = match t with | Leaf -> 0 | Node (v, l, r) -> 1 + ite (height l > height r) (height l) (height r)

    let [@simp] [@grind] rec complete (t : tree) : bool =
  match t with
  | Leaf -> true
  | Node (x, l, r) -> complete l && complete r && height l = height r"; */

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

    let mut parsed_nodes = OcamlParser::parse_nodes(program_str).expect("Failed to parse program");
    /*     assert_eq!(
        parsed_nodes.len(),
        2,
        "Expected exactly two nodes (type + function)"
    ); */

    let data_type = parsed_nodes
        .iter()
        .find_map(|node| match node {
            AstNode::TypeDeclaration(type_decl) => Some(type_decl.clone()),
            _ => None,
        })
        .expect("Expected to find tree type declaration");

    let functions: Vec<_> = parsed_nodes
        .iter()
        .filter_map(|node| match node {
            AstNode::LetBinding(binding) => Some(binding.clone()),
            _ => None,
        })
        .collect();

    let mut generator = AxiomGenerator::new(vec![data_type.clone()]);

    // Prepare all functions for batch processing
    for function in &functions {
        generator.prepare_function(function)?;
    }

    // Create wrappers for all functions
    for function in &functions {
        let wrapper_binding = create_wrapper(function);
        parsed_nodes.push(AstNode::LetBinding(wrapper_binding));
    }

    // Build all axioms in batch
    let builder = generator.build_all();
    let axioms = builder.with_proof(|a| a.suggest_proof_tactic()).build()?;

    println!("Generated axioms:");
    for axiom in &axioms {
        println!("{}", axiom.to_lean());
    }

    // Validate generated theorems through Lean backend
    let lean_code = LeanContextBuilder::new()
        .with_nodes(parsed_nodes)
        .with_axioms(axioms)
        .with_type_theorems(&data_type.name, data_type.generate_complete_lawful_beq())
        .build();

    println!("\nLean Code:\n{lean_code}");

    validate_lean_code(&lean_code)
        .unwrap_or_else(|e| panic!("Generated axioms failed Lean validation:\n{}", e));

    println!("Lean validation passed!");

    Ok(())
}

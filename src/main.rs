use cobb_totem::ToLean as _;
use cobb_totem::axiom_generator::AxiomGenerator;
use cobb_totem::lean_backend::LeanContextBuilder;
use cobb_totem::lean_validation::validate_lean_code;
use cobb_totem::ocamlparser::OcamlParser;
use cobb_totem::prog_ir::AstNode;

fn main() -> Result<(), Box<dyn std::error::Error>> {
  /*   let program_str = "
    type [@grind] ilist = Nil | Cons of int * ilist\n

    let [@simp] [@grind] rec sorted (l : ilist) : bool = match l with
    | Nil -> true
    | Cons (x, xs) -> match xs with
    | Nil -> true
    | Cons (y, ys) -> (x <= y) && sorted xs"; */

        let program_str = "
    type [@grind] ilist = Nil | Cons of int * ilist\n

    let [@simp] [@grind] rec len (l : ilist) (n : int) : bool =
    match l with
    | Nil -> n = 0
    | Cons (x, xs) -> len xs (n - 1)";

    let parsed_nodes = OcamlParser::parse_nodes(program_str).expect("Failed to parse program");
    assert_eq!(
        parsed_nodes.len(),
        2,
        "Expected exactly two nodes (type + function)"
    );

    let ilist_type = parsed_nodes
        .iter()
        .find_map(|node| match node {
            AstNode::TypeDeclaration(type_decl) => Some(type_decl.clone()),
            _ => None,
        })
        .expect("Expected to find ilist type declaration");

    let sorted_function = parsed_nodes
        .iter()
        .find_map(|node| match node {
            AstNode::LetBinding(binding) => Some(binding.clone()),
            _ => None,
        })
        .expect("Expected to find sorted function binding");

    let generator = AxiomGenerator::new(vec![ilist_type.clone()]);
    let mut axioms = generator
        .from_let_binding(&sorted_function)
        .expect("Failed to generate axioms");

    // Set proof to grind for all axioms
    for axiom in &mut axioms {
        axiom.proof = Some("grind".to_string());
    }

    println!("Generated axioms:");
    for axiom in &axioms {
        println!("{}", axiom.to_lean());

        /* todo add display */
        /* Use a typical form for length functions and transform */
        /* Consider variations that include existentials */
        /* Work on the reverse direction */
        /* Alternative proof structures */
        /* Weakest postcondition connection? */
        /* Relational encoding phrase */
    }

    // Validate generated theorems through Lean backend
    let lean_code = LeanContextBuilder::new()
        .with_nodes(parsed_nodes)
        .with_axioms(axioms)
        .with_type_theorems("ilist", ilist_type.generate_complete_lawful_beq())
        .build();

    println!("\nLean Code:\n{lean_code}");

    validate_lean_code(&lean_code)
        .unwrap_or_else(|e| panic!("Generated axioms failed Lean validation:\n{}", e));

    println!("\nLean validation passed!");

    Ok(())
}

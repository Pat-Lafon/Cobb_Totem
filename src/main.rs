use cobb_totem::ToLean as _;
use cobb_totem::axiom_generator::AxiomGenerator;
use cobb_totem::create_wrapper::create_wrapper;
use cobb_totem::lean_backend::LeanContextBuilder;
use cobb_totem::lean_validation::validate_lean_code;
use cobb_totem::ocamlparser::OcamlParser;
use cobb_totem::prog_ir::AstNode;
use std::env;
use std::fs;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Read example file from command line argument or use default
    let file_path = env::args()
        .nth(1)
        .unwrap_or_else(|| "examples/list_len.ml".to_string());

    let program_str = fs::read_to_string(&file_path)
        .unwrap_or_else(|e| panic!("Failed to read file '{}': {}", file_path, e));

    let mut parsed_nodes = OcamlParser::parse_nodes(&program_str).expect("Failed to parse program");

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
        .with_axioms(axioms.clone())
        .with_type_theorems(&data_type.name, data_type.generate_complete_lawful_beq())
        .build();

    println!("\nLean Code:\n{lean_code}");

    validate_lean_code(&lean_code)
        .unwrap_or_else(|e| panic!("Generated axioms failed Lean validation:\n{}", e));

    println!("Lean validation passed!");

    let axiom_strings: Vec<String> = axioms.iter().map(|a| a.to_string()).collect();
    println!("Axioms for Cobb use\n{}", axiom_strings.join("\n"));

    Ok(())
}

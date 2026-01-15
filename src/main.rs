use clap::Parser;
use cobb_totem::ToLean as _;
use cobb_totem::axiom_generator::AxiomGenerator;
use cobb_totem::create_wrapper::create_wrapper;
use cobb_totem::lean_backend::LeanContextBuilder;
use cobb_totem::lean_validation::validate_lean_code;
use cobb_totem::ocamlparser::OcamlParser;
use cobb_totem::prog_ir::AstNode;
use std::fs;

#[derive(Parser, Debug)]
#[command(name = "cobb_totem")]
#[command(about = "Generate axioms from OCaml programs in OCaml format")]
struct Args {
    /// Path to OCaml program file to analyze
    #[arg(value_name = "FILE")]
    program: Option<String>,

    /// Export axioms to this file (if not specified, prints to stdout)
    #[arg(long, value_name = "PATH")]
    export_axioms: Option<String>,
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args = Args::parse();

    let file_path = args
        .program
        .unwrap_or_else(|| "examples/list_len.ml".to_string());
    let export_path = args.export_axioms;

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

    eprintln!("Generated axioms:");
    for axiom in &axioms {
        eprintln!("{}", axiom.to_lean());
    }

    // Validate generated theorems through Lean backend
    let lean_code = LeanContextBuilder::new()
        .with_nodes(parsed_nodes)
        .with_axioms(axioms.clone())
        .with_type_theorems(&data_type.name, data_type.generate_complete_lawful_beq())
        .build();

    eprintln!("\nLean Code:\n{lean_code}");

    validate_lean_code(&lean_code)
        .unwrap_or_else(|e| panic!("Generated axioms failed Lean validation:\n{}", e));

    eprintln!("Lean validation passed!");

    // Generate OCaml axiom output
    let axiom_strings: Vec<String> = axioms.iter().map(|a| a.to_string()).collect();
    let axiom_output = axiom_strings.join("\n");

    // Write to file if --export-axioms specified, otherwise print to stdout
    if let Some(path) = export_path {
        fs::write(&path, &axiom_output)
            .unwrap_or_else(|e| panic!("Failed to write axioms to '{}': {}", path, e));
        eprintln!("Axioms exported to: {}", path);
    } else {
        println!("{}", axiom_output);
    }

    Ok(())
}

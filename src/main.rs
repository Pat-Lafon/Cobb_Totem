use clap::Parser;
use cobb_totem::ToLean as _;
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

    // Generate and validate axioms using unified helper
    let (_parsed_nodes, axioms) = cobb_totem::generate_and_validate_axioms(&program_str)?;

    eprintln!("Generated axioms:");
    for axiom in &axioms {
        eprintln!("{}", axiom.to_lean());
    }

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

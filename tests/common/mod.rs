use cobb_totem::lean_backend::LeanContextBuilder;
use cobb_totem::prog_ir::AstNode;
use std::fs;

pub fn process_example_file(file_path: &str) -> Result<String, Box<dyn std::error::Error>> {
    let program_str = fs::read_to_string(file_path)
        .unwrap_or_else(|e| panic!("Failed to read file '{}': {}", file_path, e));

    // Generate and validate axioms using unified helper
    let (parsed_nodes, axioms) = cobb_totem::generate_and_validate_axioms(&program_str)?;

    // Extract type declaration for final Lean code generation
    let type_decl = parsed_nodes
        .iter()
        .find_map(|node| match node {
            AstNode::TypeDeclaration(type_decl) => Some(type_decl.clone()),
            _ => None,
        })
        .expect("Expected to find type declaration");

    // Rebuild lean code for return (already validated by helper)
    let lean_code = LeanContextBuilder::new()
        .with_nodes(parsed_nodes)
        .with_axioms(axioms)
        .with_type_theorems(&type_decl.name, type_decl.generate_complete_lawful_beq())
        .build();

    Ok(lean_code)
}

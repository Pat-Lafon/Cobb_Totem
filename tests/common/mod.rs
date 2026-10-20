use std::fs;

pub fn process_example_file(file_path: &str) -> Result<(), Box<dyn std::error::Error>> {
    let program_str = fs::read_to_string(file_path)
        .unwrap_or_else(|e| panic!("Failed to read file '{}': {}", file_path, e));

    cobb_totem::generate_axioms(&program_str)?;
    Ok(())
}

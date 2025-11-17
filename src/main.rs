use std::fs;

use cobb_totem::ocamlparser::OcamlParser;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let source = fs::read_to_string("input_files/list_len.ml")?;

    let mut parser = tree_sitter::Parser::new();
    let lang = tree_sitter_ocaml::LANGUAGE_OCAML.into();
    parser.set_language(&lang)?;

    let tree = parser.parse(&source, None).ok_or("Failed to parse file")?;

    let ocaml_parser = OcamlParser::new(source);
    let ast = ocaml_parser.parse(&tree)?;

    println!("Parsed OCaml AST:");
    for node in &ast {
        println!("{:#?}", node);
    }

    for node in ast {
        println!("{}", node);
    }

    Ok(())
}

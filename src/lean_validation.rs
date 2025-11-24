/// Validation module for Lean code
use std::io::Write;
use std::process::Command;

/// Check if debug output is enabled via feature flag
fn debug_enabled() -> bool {
    cfg!(feature = "debug")
}

/// Validate generated Lean code by running the lean type checker via stdin
pub fn validate_lean_code(code: &str) -> Result<(), String> {
    // Wrap in namespace for recursive types and to isolate scope
    let wrapped_code = format!("namespace GeneratedCode\n\n{}\n\nend GeneratedCode\n", code);

    if debug_enabled() {
        debug_print_lean(code);
    }

    // Run lean with code piped via stdin
    let mut child = Command::new("lean")
        .arg("--stdin")
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .map_err(|e| format!("Failed to spawn lean: {}", e))?;

    // Write code to stdin
    if let Some(mut stdin) = child.stdin.take() {
        stdin
            .write_all(wrapped_code.as_bytes())
            .map_err(|e| format!("Failed to write to stdin: {}", e))?;
    }

    let output = child
        .wait_with_output()
        .map_err(|e| format!("Failed to run lean: {}", e))?;

    if output.status.success() {
        Ok(())
    } else {
        Err(String::from_utf8_lossy(&output.stdout).to_string())
    }
}

/// Print generated Lean code for debugging
pub fn debug_print_lean(code: &str) {
    eprintln!("\n=== Generated Lean Code ===");
    for line in code.lines() {
        eprintln!("{}", line);
    }
    eprintln!("===========================\n");
}

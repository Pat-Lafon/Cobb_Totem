/// Validation module for Lean code
use std::io::Write;
use std::process::Command;

/// Check if debug output is enabled via feature flag
fn debug_enabled() -> bool {
    cfg!(feature = "debug")
}

/// Validate generated Lean code by running the lean type checker via stdin
pub fn validate_lean_code(code: &str) -> Result<(), String> {
    if debug_enabled() {
        debug_print_lean(code);
    }

    // Run lean with code piped via stdin using lake env
    let mut child = Command::new("lake")
        .arg("env")
        .arg("lean")
        .arg("--stdin")
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .map_err(|e| {
            format!(
                "Lean code validation failed:\n{}\n\nFailed to spawn lean: {}",
                code, e
            )
        })?;

    // Write code to stdin
    {
        let mut stdin = child.stdin.take()
            .ok_or_else(|| format!("Lean code validation failed:\n{}\n\nFailed to open stdin", code))?;
        stdin.write_all(code.as_bytes()).map_err(|e| {
            format!(
                "Lean code validation failed:\n{}\n\nFailed to write to stdin: {}",
                code, e
            )
        })?;
    }

    let output = child.wait_with_output().map_err(|e| {
        format!(
            "Lean code validation failed:\n{}\n\nFailed to run lean: {}",
            code, e
        )
    })?;

    if output.status.success() {
        Ok(())
    } else {
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        let mut error_msg = format!(
            "Lean code validation failed:\n{}\n\nError:\n{}",
            code, stdout
        );
        if !stderr.is_empty() {
            error_msg.push_str(&format!("\nStderr:\n{}", stderr));
        }
        Err(error_msg)
    }
}

/// Print generated Lean code for debugging
pub fn debug_print_lean(code: &str) {
    // Limit output to prevent spam from very large code
    const MAX_DEBUG_LINES: usize = 1000;
    let line_count = code.lines().count();

    eprintln!("\n=== Generated Lean Code ===");
    if line_count > MAX_DEBUG_LINES {
        eprintln!("(Truncated: {} total lines, showing first {})", line_count, MAX_DEBUG_LINES);
    }
    for (i, line) in code.lines().enumerate() {
        if i >= MAX_DEBUG_LINES {
            break;
        }
        eprintln!("{}", line);
    }
    eprintln!("===========================\n");
}

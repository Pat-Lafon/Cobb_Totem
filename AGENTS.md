# Agent Instructions for Cobb_Totem

## Error Handling

**Promote explicit failures whenever possible.** Avoid silent failures and fallthrough behavior.

- Use `.ok_or()` / `.ok_or_else()` to convert `Option` to `Result` with clear error messages
- Use early `return Err()` for validation failures instead of nested `if let Some()` blocks
- Validate node types with explicit checks: `if node.kind() != "expected_kind"` rather than silent skipping
- Provide descriptive error messages that indicate what was expected vs. what was found

Example pattern:
```rust
let node = children.next().ok_or("Expected child node")?;
if node.kind() != "expected_type" {
    return Err(format!("Expected 'expected_type', got '{}'", node.kind()));
}
// Use node directly here without nested conditions
```

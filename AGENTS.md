# Agent Instructions for Cobb_Totem

## Error Handling

**Promote explicit failures whenever possible.** Avoid silent failures and fallthrough behavior.

- Use `panic!()` for validation failures when parsing is expected to succeed (parser invariant violations)
- Validate node types with explicit checks: `if node.kind() != "expected_kind"` rather than silent skipping
- Provide descriptive panic messages that indicate what was expected vs. what was found
- **Always include the underlying error message when panicking on an error**, using patterns like `panic!("Failed to parse: {}", e)` to preserve diagnostic information
- **Never create dummy nodes or placeholder values** as fallback values (e.g., `Expression::Variable("")`, `vec![]`, etc.). Use `unimplemented!()` with a descriptive message instead.
- **Never silently discard return values with `let _ = result;`** - always explicitly handle the result with assertions or explicit error handling

Example pattern:
```rust
let node = children.next().expect("Expected child node");
assert_eq!(node.kind(), "expected_type", "Expected 'expected_type', got '{}'", node.kind());
// Use node directly here without nested conditions
```

## Testing and Binaries

- Do not create additional binaries during development or testing
- Use tests instead: add test cases to verify functionality
- Tests in the codebase serve as both validation and documentation
- **Tests must make assertions, not just print output.** Every test should verify behavior with `assert!()`, `assert_eq!()`, or similar macros
- Use `println!()` only for debugging during development; remove before committing

## Git Operations

- Do not modify or create `.gitignore` rules
- Do not use git commands unless explicitly requested by the user
- Let the user manage their own git workflow (commits, branches, etc.)

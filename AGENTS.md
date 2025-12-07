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
- **Never create temporary/debug files** of any kind (e.g., `debug_tree.rs`, `test_parse.rs`, `debug_list_pattern.rs`)
  - Analyze tree structures and behavior using the test suite within the module
  - Use the test failures and output to understand behavior
  - Do not create standalone files just to inspect output
- Use tests instead: add test cases directly to the module's test module to explore functionality and verify behavior
- Tests in the codebase serve as both validation and documentation
- **Tests must make assertions, not just print output.** Every test should verify behavior with `assert!()`, `assert_eq!()`, or similar macros
- Use `eprintln!()` or `println!()` only for debugging during test development; remove before committing
- Remove debug tests after gathering information (e.g., tests that only print tree structure for investigation)
- **For string assertions, use `assert_eq!()` to compare the full expected string rather than multiple `assert!(string.contains(...))` checks.** This provides clearer error messages and is more precise.
- **Use precise assertions with exact values, not inequalities.** Never use `assert!(value >= expected)` or `assert!(value <= expected)` when you know the exact expected value. Use `assert_eq!(value, expected)` instead. Imprecise assertions hide bugs and make tests less meaningful.
- **Never suppress error messages in tests.** When validating Results, use `.unwrap_or_else(|e| panic!(...))` to include the error details instead of `.is_ok()`, `.unwrap()`, or similar patterns that hide the actual error.
- **Test observable behavior, not just naming or structure.** Don't just assert that a field has an expected name; verify the actual content, relationships, and output of generated objects.
  - Instead of `assert_eq!(axiom.name, "len_0")`, assert the complete Lean output with `assert_eq!(axiom.to_lean(), "theorem ...")`
  - Verify parameter counts and types: `assert_eq!(axiom.params.len(), 2)`
  - Check structural properties: `assert!(matches!(axiom.body, Proposition::Implication(_, _)))`
  - This catches semantic errors that a name alone cannot reveal

Example (avoid):
```rust
assert!(result.contains("def foo"));
assert!(result.contains("(x : Int)"));
assert!(validate().is_ok(), "validation failed");
validate().unwrap();
```

Example (preferred):
```rust
assert_eq!(result, "def foo(x : Int)");
validate().unwrap_or_else(|e| panic!("validation failed: {}", e));
```

## Git Operations

- Do not modify or create `.gitignore` rules
- Do not use git commands unless explicitly requested by the user
- **Never use `git reset`** - this can lose work
- Let the user manage their own git workflow (commits, branches, etc.)

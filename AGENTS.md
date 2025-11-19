# Agent Instructions for Cobb_Totem

## Error Handling

**Promote explicit failures whenever possible.** Avoid silent failures and fallthrough behavior.

- Use `panic!()` for validation failures when parsing is expected to succeed (parser invariant violations)
- Validate node types with explicit checks: `if node.kind() != "expected_kind"` rather than silent skipping
- Provide descriptive panic messages that indicate what was expected vs. what was found
- **Never create dummy nodes** as fallback values (e.g., `Expression::Variable("")`). Panic instead.

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

## Git Operations

- Do not modify or create `.gitignore` rules
- Do not use git commands unless explicitly requested by the user
- Let the user manage their own git workflow (commits, branches, etc.)

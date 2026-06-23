# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

Cobb_Totem generates formal verification axioms (theorems) in Lean 4 from OCaml program specifications. It parses OCaml functions and type declarations, then synthesizes proof obligations that can be verified by Lean's type checker.

## Build Commands

```bash
cargo build                          # Build the project
cargo run -- examples/list_len.ml    # Run with an example file
cargo test                           # Run all tests
cargo test test_list_len             # Run a specific test
cargo test -- --nocapture            # Run tests with output visible
```

**Lean setup** (if you get `unknown module prefix 'ProofAutomation'` errors):
```bash
lake update
lake build ProofAutomation.ProveAxiom    # build the tactic from the required root package
lake build
```

## Architecture

**Data Flow:**
```
OCaml Source (.ml)
    → OcamlParser (tree-sitter)
    → Program IR (prog_ir.rs)
    → AxiomGenerator
    → Specification IR (spec_ir.rs)
    → LeanContextBuilder
    → Lean 4 Code
    → lean_validation (lake env lean --stdin)
```

**Key Modules:**
- `ocamlparser.rs` - Parses OCaml using tree-sitter into AST nodes
- `prog_ir.rs` - Program IR: TypeDecl, LetBinding, Expression, Pattern, Type
- `spec_ir.rs` - Specification IR: Axiom, Proposition, Parameter, Quantifier
- `axiom_generator.rs` - Generates axioms from program IR
- `axiom_builder_state.rs` - Builder state for axiom generation
- `create_wrapper.rs` - Creates wrapper functions (`{func}_wrapper`) for axioms
- `lean_backend.rs` - Converts IR to Lean 4 syntax via `ToLean` trait
- `lean_validation.rs` - Validates generated Lean code via `lake env lean --stdin`
- `axiom_validation.rs` - Validates quantifier ordering and free variables

**Proof Tactics**: every axiom is discharged by the shared `prove_axiom` tactic
(`ProofAutomation.ProveAxiom`, in the root `TotemArtifact` package). `Axiom::generate_proof_tactic`
in `spec_ir.rs` emits a uniform `prove_axiom`; `domain_axiom_builder.rs` does the same for its
domain axioms. There is no per-axiom tactic synthesis — `prove_axiom` subsumes the former
existential/non-existential split and adds twin-fact grind patterns for inductive-converse axioms.
`lean_backend.rs::build` prepends `import ProofAutomation.ProveAxiom` whenever any axiom carries a
real (non-`sorry`) proof, and Cobb_Totem's `lakefile.lean` requires the root package
(`require «TotemArtifact» from "../"`) so the import resolves during `lake env lean --stdin`
validation. Both packages share the `v4.31.0` toolchain, as a local `require` demands.

## Testing

Tests are in `/tests/integration_tests.rs` (end-to-end) and unit tests within each module.

Example files in `/examples/`: `list_len.ml`, `list_sorted.ml`, `bst.ml`, `rbtree.ml`, `tree_height.ml`, `tree_complete.ml`

## Guidelines

### Visibility
- Prefer private > `pub(crate)` > `pub`
- `pub` only for public API: core domain types (`Axiom`, `Parameter`, `Proposition`, `Expression`, `Type`, `LetBinding`, `TypeDecl`) and top-level traits (`ToLean`)
- `pub(crate)` for internal cross-module items (builders, utilities, helper types)
- When the compiler warns about unused `pub(crate)` items, remove them — never use `#[allow(dead_code)]`

### Function Design
- Avoid thin wrapper functions that just delegate without adding logic, validation, or abstraction
- Only keep wrappers that provide semantic boundaries, add error handling, or significantly reduce duplication

### Error Handling
- Use `panic!()` for parser invariant violations with descriptive messages
- Always include underlying error messages: `panic!("Failed to parse: {}", e)`
- Never create dummy nodes or placeholder values (e.g., `Expression::Variable("")`); use `unimplemented!()` with a message instead

### Testing
- Remove debug/investigation tests after development
- Never create temporary/debug files; use tests within modules to explore functionality

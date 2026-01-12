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

**Lean setup** (if you get `unknown module prefix 'Aesop'` errors):
```bash
lake update
lake build aesop
lake build hammer
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

**Proof Tactics:**
- `grind` - Default tactic for axioms without existential quantifiers
- `aesop` - Used for axioms with existential quantifiers

## Testing

Tests are in `/tests/integration_tests.rs` (end-to-end) and unit tests within each module.

Example files in `/examples/`: `list_len.ml`, `list_sorted.ml`, `bst.ml`, `rbtree.ml`, `tree_height.ml`, `tree_complete.ml`

## Agent Rules (from AGENTS.md)

**Error Handling:**
- Use `panic!()` for parser invariant violations
- Always include underlying error messages in panics
- Never create dummy nodes or placeholder values as fallbacks

**Testing:**
- Tests must make assertions, not just print output
- Use `assert_eq!()` for string comparisons, not multiple `contains()` checks
- Use precise assertions with exact values, not inequalities
- Test observable behavior (e.g., `axiom.to_lean()` output), not just names
- Never suppress error messages - use `.unwrap_or_else(|e| panic!(...))` to include error details

**Git:**
- Do not use git commands - user manages version control

**Files:**
- Never create temporary/debug files
- Use tests within modules to explore functionality

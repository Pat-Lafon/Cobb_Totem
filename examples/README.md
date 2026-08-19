# Cobb_Totem Examples

OCaml programs Cobb_Totem turns into Lean 4 axioms. `tests/integration_tests.rs` runs one test per
file here, so each one is also a regression guard.

## Examples

| File | Shape it covers |
|------|-----------------|
| `list_len.ml` | Measure over a list — the smallest program that emits a `_geq_0` domain axiom |
| `list_mem.ml` | Two-argument predicate with `\|\|` in the recursive branch |
| `list_sorted.ml` | Nested `match` on the tail, giving three branch axioms from two constructors |
| `list_even.ml` | `is_even` recurses on `int` rather than a constructor, so it needs a termination proof |
| `tree_height.ml` | `ite` in the body — each arm becomes its own branch axiom |
| `tree_complete.ml` | One predicate calling another (`complete` over `height`) |
| `bst.ml` | Three predicates, the last calling the first two |
| `rbtree.ml` | Four predicates, `if` on a boolean field, and `match` nested two deep |

## OCaml Syntax Notes

- Every parameter and return type must be annotated. `create_wrapper.rs` asserts on a missing return
  type.
- `[@simp]` / `[@grind]` in these files are decoration only. `wrap_all_functions` (`src/lib.rs`)
  overwrites the attributes on every binding and datatype before anything is emitted, so stripping
  them from a source file gives byte-identical axioms.

## Running Examples

```bash
cargo run -- examples/list_len.ml                       # axioms to stdout
cargo run -- examples/rbtree.ml --export-axioms out.ml  # axioms to a file
```

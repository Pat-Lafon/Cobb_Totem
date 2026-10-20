# Cobb_Totem Examples

OCaml programs Cobb_Totem turns into `let[@axiom]` declarations. `tests/integration_tests.rs` runs one test per
file here, so each one is also a regression guard.

## Examples

| File | Shape it covers |
|------|-----------------|
| `list_len.ml` | Measure over a list — the smallest program that emits a `_geq_0` domain axiom |
| `list_mem.ml` | Two-argument predicate with `\|\|` in the recursive branch |
| `list_sorted.ml` | Nested `match` on the tail, giving three branch axioms from two constructors |
| `list_even.ml` | A recursive predicate calling a non-recursive one (`is_even`, via `mod`) |
| `tree_height.ml` | `ite` in the body — each arm becomes its own branch axiom |
| `tree_complete.ml` | One predicate calling another (`complete` over `height`) |
| `bst.ml` | Three predicates, the last calling the first two |
| `rbtree.ml` | Four predicates, `if` on a boolean field, and `match` nested two deep |

## OCaml Syntax Notes

- Every parameter and return type must be annotated. `prepare_function` rejects a missing return
  type.
- `[@simp]` / `[@grind]` in these files are decoration only: the parser skips attributes, so
  stripping them from a source file gives byte-identical axioms.

## Running Examples

```bash
cargo run -- examples/list_len.ml                       # axioms to stdout
cargo run -- examples/rbtree.ml --export-axioms out.ml  # axioms to a file
```

# Cobb_Totem Examples

This directory contains example OCaml programs that can be processed by Cobb_Totem to generate Lean 4 axioms.

## Examples

| File | Description |
|------|-------------|
| `list_len.ml` | Simple list length function |
| `list_sorted.ml` | Sorted list predicate with nested match |
| `tree_height.ml` | Binary tree height computation |
| `tree_complete.ml` | Complete tree predicate |
| `bst.ml` | Binary search tree invariants |
| `rbtree.ml` | Red-black tree invariants |

## OCaml Syntax Notes

- `[@grind]` and `[@simp]` attributes are passed through to Lean
- Types must be annotated on all parameters and return values

## Running Examples

```bash
cargo run -- examples/list_len.ml
```

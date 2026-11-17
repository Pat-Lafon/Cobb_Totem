# Cobb_Totem — OCaml axiom generator

Parses an OCaml program (one datatype plus recursive predicate/measure functions) and emits
`let[@axiom]` declarations that encode each function `f x = r` as a relation `f x r`.
`cargo run -- examples/list_len.ml` prints every kind of axiom it emits. The tool checks each axiom's
structure (`generate_all` panics on a malformed one), not its provability — that is proved downstream,
against the SMT encoding Cobb solves.

## Axiom format

Header parameters are universal, written `(name : type)`; existentials are
`fun ((name [@exists]) : type) -> …` binders inside the body; `#==>` is implication. Which axioms each
function gets, and their names: `build_axioms_for`.

## Rules

- **Emit each predicate as axioms, never as a definition** — no SMT-LIB `define-fun`, Lean `def`, or IR
  variant like an `IsFunction` on `Proposition`. Z3 unfolds a definition unconditionally:
  `(num_black (left t))` is always constructible, so a definition trades the skolem-witness blowup for
  unbounded `num_black (left (left …))` terms.
- **Pair each per-branch introduction `{pred}_{idx}` with a forward elimination `{pred}_{idx}_fwd`**,
  though `_fwd` follows logically from the intro, `_total`, and `_functional`. Z3's E-matching can't
  make that derivation: from `len (Cons h' l') s`, reaching `len l' (s-1)` needs a witness for the
  recursive-call result (`res_0` in `len xs res_0`), and no E-graph term anchors its Skolem. Omitting
  `_fwd` on that reasoning broke `sorted_non_emp`, `unique_emp_rev`, and `even_list_empty_rev`.
- **Judge an axiom shape by Z3 (Cobb's abduction and subtyping checks) and `grind` (`prove_axiom`)
  alone** — a `SimpHyps` regression gets a hand-added axiom in that benchmark's
  `program_axioms_proposed.ml`, not a generator change.
- **Start a new item `pub(crate)`**; make it `pub` only when `main.rs` or `tests/` (a separate crate)
  drives it.

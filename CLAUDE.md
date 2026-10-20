# Cobb_Totem — OCaml axiom generator

Parses an OCaml program (one datatype plus recursive predicate/measure functions) and emits
`let[@axiom]` declarations describing each function as a *relation* over its inputs and result.
It checks their structure, not their provability; that is proved downstream, against the SMT encoding
Cobb solves.

## Build and run

`cargo run -- examples/list_len.ml` prints the axioms, and is the fastest way to see the full emitted
vocabulary; `--export-axioms <path>` writes them to a file instead.

## Axiom format

- Relation predicates and naming: `build_axioms_for` in `src/axiom_builder_state.rs`.
- Every parameter in the header is universal, written `(name : type)`. Existentials appear only inside
  the body, as `fun ((name [@exists]) : type) -> …` binders.
- `#==>` is implication; everything else is ordinary OCaml-shaped syntax. `Proposition::Equality`,
  which renders `#==`, exists in the IR but is constructed only in `spec_ir.rs` tests — the generator
  never emits it.

**Predicates leave the tool as axioms, never as definitions.** Nothing in the exported set gives Z3 a
body to unfold — no SMT-LIB `define-fun`, no Lean `def`. Axioms give Z3 controllable quantifier
instantiation, while a function definition forces unconditional unfolding: a term like
`(num_black (left t))` is always constructible, so it trades the skolem-witness blowup for unbounded
`num_black(left(left(…)))` term generation. Don't propose IR variants (an `IsFunction` on
`Proposition`) or backend shortcuts that lower a predicate to a function definition. Dedup ideas that
operate at the axiom level are fine; ideas that change the *kind* of object emitted are not.

**Every per-branch introduction `{pred}_{idx}` needs a paired forward-elimination `{pred}_{idx}_fwd`**,
emitted by `build_branch_elim_axiom_for` in `src/axiom_builder_state.rs`.

Z3 cannot synthesize witnesses for the lifted body params — recursive-call results like `res_0` in
`len xs res_0` — when triggering `_functional`/`_total` against an opaque hypothesis `pred l res`,
because those params have no E-graph occurrence to anchor the Skolemized witness. The introduction
direction alone is unfireable when the hypothesis is `h : len (Cons h' l') s` and you need
`len l' (s-1)`. So don't accept "logically derivable from intro + `_total` + `_functional`" as grounds
to omit a shape when the consumer is Z3 E-matching: omitting `_fwd` on exactly that reasoning broke
`sorted_non_emp`, `unique_emp_rev`, and `even_list_empty_rev`. The rearrangement is the contribution.

**Evaluate an axiom shape against Z3 and `grind` only** — Z3 through Cobb's abduction and subtype
checker, `grind` through `prove_axiom`. Those are the two downstream consumers. `SimpHyps` is a Lean
tactic, not a design target; a `SimpHyps` regression on a specific test is handled by a per-test
hand-add to `_proposed.ml` at implementation time, not by keeping or adding an axiom.

## Architecture

Pipeline stages: `src/lib.rs` module doc. `generate_all` checks each axiom's structure
(`src/axiom_validation.rs`: quantifier order, free variables, duplicate binders) and panics on a
malformed one.

## Testing

Three layers: `tests/integration_tests.rs` (one end-to-end test per file in `examples/`),
`src/integration_tests.rs` (the same pipeline over inline program strings), and per-module
`#[cfg(test)]` units. The axiom-shape tests in `axiom_builder_state.rs` pin exact `let[@axiom]` output
string-for-string — those are what a shape change breaks first.

Every shape those tests pin is also proved by a Totem benchmark, except a measure recursing on an
`Int`, which nothing tests or proves.

## Visibility

`tests/` is a separate crate, so the pipeline stages it and `main.rs` drive are `pub`. Everything
reachable only from inside the crate is `pub(crate)`, and a new item starts there.

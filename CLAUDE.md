# Cobb_Totem — OCaml-to-Lean 4 axiom generator

Parses an OCaml program (one datatype plus recursive predicate/measure functions) and emits
`let[@axiom]` declarations describing each function as a *relation* over its inputs and result. Every
axiom is proved through Lean before it leaves the tool, so what Cobb consumes downstream is a set Lean
has already accepted.

## Build and run

`cargo run -- examples/list_len.ml` prints the axioms, and is the fastest way to see the full emitted
vocabulary; `--export-axioms <path>` writes them to a file instead, and `--features debug` dumps each
generated Lean file. `cargo test` takes minutes rather than seconds — every layer spawns
`lake env lean`.

`unknown module prefix 'ProofAutomation'` means the Lean side isn't built: `lake update`, then
`lake build ProofAutomation.ProveAxiom`. Bare `lake build` targets the default root `Main.lean`, which
is gitignored, so it fails in a fresh checkout.

## Axiom format

- `len l res` is the relation predicate: the OCaml function name applied to its inputs plus a result
  argument. `is_nil` / `is_cons` and field accessors like `head` / `tail` are helper predicates
  generated from the datatype (`TypeDecl::generate_helper_predicates`).
- Every parameter in the header is universal, written `(name : type)`. Existentials appear only inside
  the body, as `fun ((name [@exists]) : type) -> …` binders.
- `#==>` is implication; everything else is ordinary OCaml-shaped syntax. `Proposition::Equality`,
  which renders `#==`, exists in the IR but is constructed only in `spec_ir.rs` tests — the generator
  never emits it.
- Naming: `{f}_geq_0` (measure non-negativity, `DOMAIN_AXIOM_SUFFIX`), `{f}_functional` (determinism),
  `{f}_total` (existence), `{f}_{idx}` (branch introduction), `{f}_{idx}_fwd` (branch
  forward-elimination).

**Predicates leave the tool as axioms, never as definitions.** Nothing in the exported set gives Z3 a
body to unfold — no SMT-LIB `define-fun`, no Lean `def`. Axioms give Z3 controllable quantifier
instantiation, while a function definition forces unconditional unfolding: a term like
`(num_black (left t))` is always constructible, so it trades the skolem-witness blowup for unbounded
`num_black(left(left(…)))` term generation. Don't propose IR variants (an `IsFunction` on
`Proposition`) or backend shortcuts that lower a predicate to a function definition. Dedup ideas that
operate at the axiom level are fine; ideas that change the *kind* of object emitted are not.

That governs the *exported* axioms. The Lean file built for validation does define each predicate —
`wrap_all_functions` renames `f` to `f_impl` and adds `def f args res : Bool := f_impl args == res`,
which is what lets Lean discharge the axioms at all. That `def` never reaches Cobb.

**Every per-branch introduction `{pred}_{idx}` needs a paired forward-elimination `{pred}_{idx}_fwd`**,
emitted by `build_branch_elim_axiom_for` in `src/axiom_builder_state.rs`: antecedent
`pred(inputs, res) ∧ input_constraints_conj`, consequent `∃ body_params. (body_steps_conj ∧
result_eq)`, with an `additional_parameter` named by `input_constraints` universal and one appearing
only in `body_steps`/`result_expr` existential under the consequent.

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

The pipeline runs `ocamlparser.rs` (tree-sitter) → `prog_ir.rs` → `axiom_generator.rs`
(`prepare_function`, one `PreparedBinding` per function) → `axiom_builder_state.rs` (`generate_all`,
where the axiom shapes are decided) → `spec_ir.rs` → `lean_backend.rs` → `lean_validation.rs`
(`lake env lean --stdin`). `ls src/` for the current module roster.

`Axiom::validate` runs over every axiom inside `generate_all` and panics on a builder bug — free
variable, duplicate binder, universal-after-existential.

Every axiom is discharged by the shared `prove_axiom` tactic from the root `TotemArtifact` package;
`Axiom::generate_proof_tactic` and `domain_axiom_builder.rs` both emit it uniformly, so there is no
per-axiom tactic synthesis and a shape `prove_axiom` cannot close fails loudly at validation rather
than falling back. `lakefile.lean` requires the root package by relative path, which demands both
packages share the Lean toolchain pinned in `../lean-toolchain`.

## Testing

Three layers, all spawning `lake env lean`: `tests/integration_tests.rs` (one end-to-end test per file
in `examples/`), `src/integration_tests.rs` (the same pipeline over inline program strings), and
per-module `#[cfg(test)]` units. The axiom-shape tests in `axiom_builder_state.rs` pin exact Lean
output string-for-string — those are what a shape change breaks first.

## Visibility

`tests/` is a separate crate, so the pipeline stages it and `main.rs` drive are `pub`. Everything
reachable only from inside the crate is `pub(crate)`, and a new item starts there.

Never stand in a dummy node or placeholder value (`Expression::Variable("")`) — reach for
`unimplemented!()` with a message.

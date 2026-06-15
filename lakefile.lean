import Lake
open Lake DSL

package «Cobb_Totem» where
  -- You can add package metadata here if needed

-- Axioms are proved by the shared `prove_axiom` tactic, provided by the root
-- TotemArtifact package's `ProofAutomation` library. Requiring it locally puts
-- `ProofAutomation.ProveAxiom` on the lake graph so `lean_validation.rs`'s
-- `lake env lean --stdin` can resolve the generated `import`. Both packages are
-- pinned to the same toolchain (v4.29.0-rc2), as a local `require` demands.
require «TotemArtifact» from "../"
@[default_target]
lean_lib «Cobb_Totem» where
  roots := #[`Main]

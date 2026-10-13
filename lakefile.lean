import Lake
open Lake DSL

package «Cobb_Totem» where
  -- You can add package metadata here if needed

-- Axioms are proved by the shared `prove_axiom` tactic, provided by pasiv's
-- `ProofAutomation` library. Requiring it puts `ProofAutomation.ProveAxiom` on
-- the lake graph so `lean_validation.rs`'s `lake env lean --stdin` can resolve
-- the generated `import`. Both packages pin the same toolchain (v4.31.0).
require «Pasiv» from git "https://github.com/Pat-Lafon/pasiv" @ "42fc09a84c44411c95bfd52fcd154d61c7a4ca10"
@[default_target]
lean_lib «Cobb_Totem» where
  roots := #[`Main]

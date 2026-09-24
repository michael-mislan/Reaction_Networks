import Lake
open Lake DSL

package mathlib4_project where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.30.0"

/-- Every shipped proof module is covered by the recursive proof-source glob.
The exact expected module inventory is migration/modules.json. Use scripts/verify.py
for a sequential resource-limited build; an unrestricted lake build can be large. -/
@[default_target]
lean_lib PublicProofs where
  srcDir := ".."
  leanOptions := #[⟨`warningAsError, true⟩]
  roots := #[`proofs]
  globs := #[.submodules `proofs]

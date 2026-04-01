import Lake
open Lake DSL

package halo2Formal where
  leanOptions := #[⟨`autoImplicit, false⟩]

require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "main"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

@[default_target]
lean_lib Halo2Formal where

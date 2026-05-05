import Lake
open Lake DSL

package «proof-bench» where
  leanOptions := #[
    ⟨`autoImplicit, true⟩,
    ⟨`relaxedAutoImplicit, true⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.28.0"

@[default_target]
lean_lib problems where
  globs := #[.submodules `problems]

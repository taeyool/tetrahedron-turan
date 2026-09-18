-- Lake build configuration for the artifact: the `LeanFlagAlgebras`
-- library is the root manifest plus every module under `LeanFlagAlgebras/`.
import Lake
open Lake DSL

package «tetrahedron-turan» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.27.0"

@[default_target]
lean_lib «LeanFlagAlgebras» where
  globs := #[.andSubmodules `LeanFlagAlgebras]

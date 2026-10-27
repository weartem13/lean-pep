import Lake
open Lake DSL

package lean_pep_toy where
  -- This small project depends only on mathlib.

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.31.0"

lean_lib LeanPEP where

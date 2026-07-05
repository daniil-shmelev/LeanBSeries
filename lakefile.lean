import Lake
open Lake DSL

package «LeanBSeries» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

-- LeanRoughPaths is expected in a sibling checkout at ../lean-rough-paths
-- (CI checks both repositories out side by side; see .github/workflows/ci.yml).
-- Alternatively, swap to the git require below once the
-- LeanRoughPaths repository is published.
require «lean-rough-paths» from ".." / "lean-rough-paths"
-- require «lean-rough-paths» from git
--   "https://github.com/daniil-shmelev/LeanRoughPaths" @ "main"

@[default_target]
lean_lib «BSeries» where
  srcDir := "."

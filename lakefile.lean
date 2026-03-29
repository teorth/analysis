import Lake
open Lake DSL

package «Analysis» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`doc.verso, true⟩ -- use Verso-format docstrings
  ]
  -- Settings applied only to command line builds
  moreLeanArgs := #[
    "-Dwarn.sorry=false" -- suppress warnings about `sorry` on the command line; remove when project is complete
  ]
  -- add any additional package configuration options here

meta if get_config? env = some "dev" then
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "main"

require verso from git
  "https://github.com/leanprover/verso" @ "main"

-- Require Mathlib (the comprehensive library of mathematics in Lean)
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.29.0-rc8"


@[default_target]
lean_lib «Analysis» where
  -- add any library configuration options here

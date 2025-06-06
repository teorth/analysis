import Lake
open Lake DSL

package «analysis» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here


-- Require Batteries (a general-purpose utility library)
require batteries from git
  "https://github.com/leanprover-community/batteries" @ "v4.20.0"

-- Require ImportGraph (transitive dep, now made direct to override version)
require importGraph from git
  "https://github.com/leanprover-community/import-graph" @ "v4.20.0"

-- Require Mathlib (the comprehensive library of mathematics in Lean)
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.20.0"

-- Require Pantograph (a library for automated theorem proving)
-- require pantograph from git
--  "https://github.com/lenianiva/Pantograph.git" @ "v0.3.1"

-- Require Plausible (transitive dep, now made direct to override version)
require plausible from git
  "https://github.com/leanprover-community/plausible.git" @ "v4.20.0"

-- Require ProofWidgets4 (for interactive proof widgets)
require proofwidgets from git
  "https://github.com/leanprover-community/ProofWidgets4.git" @"v0.0.60"

-- Require quote4 (transitive dep, now made direct to override version)
require Qq from git
  "https://github.com/leanprover-community/quote4" @ "v4.20.0"




@[default_target]
lean_lib «Analysis» where
  -- add any library configuration options here

require checkdecls from git "https://github.com/PatrickMassot/checkdecls.git"

meta if get_config? env = some "dev" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "v4.20.0"

import Lake
open Lake DSL

package «Analysis» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

-- Require Mathlib (the comprehensive library of mathematics in Lean)
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.22.0"

-- This library is needed to build the online version.
-- If ../book/lakefile.lean requires verso @ "v4.X.Y", then this line should require
-- subverso @ "verso-v4.X.Y".
-- Right now, it's set to `main` instead to get newer improvements; next time Verso is
-- updated in `../book/`, this should be set to the corresponding tag again.
require subverso from git "https://github.com/leanprover/subverso" @ "main"

@[default_target]
lean_lib «Analysis» where
  -- add any library configuration options here

lean_exe "literate-extract" where
  root := `LiterateExtract
  supportInterpreter := true

meta if get_config? env = some "dev" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "v4.22.0"


module_facet literate mod : System.FilePath := do
  let ws ← getWorkspace
  let some extract ← findLeanExe? `«literate-extract»
    | error "The `literate-extract` executable was not found"

  let exeJob ← extract.exe.fetch
  let modJob ← mod.olean.fetch

  let buildDir := ws.root.buildDir
  let hlFile := mod.filePath (buildDir / "literate") "json"

  exeJob.bindM fun exeFile =>
    modJob.mapM fun _oleanPath => do
      buildFileUnlessUpToDate' (text := true) hlFile <|
        proc {
          cmd := exeFile.toString
          args :=  #[mod.name.toString, hlFile.toString]
          env := ← getAugmentedEnv
        }
      pure hlFile

library_facet literate lib : Array System.FilePath := do
  let mods ← (← lib.modules.fetch).await
  let modJobs ← mods.mapM (·.facet `literate |>.fetch)
  let out ← modJobs.mapM (·.await)
  pure (.pure out)

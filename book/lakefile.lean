import Lake
open Lake DSL

require verso from git "https://github.com/leanprover/verso.git"@"main"
require subverso from git
  "https://github.com/leanprover/subverso.git" @ "79c973b07e2f43c4ac1cec720bbe20b4fbfbd0e9"

package "analysis-book" where
  version := v!"0.1.0"

lean_lib «AnalysisBook» where
  -- add library configuration options here

@[default_target]
lean_exe "analysis-book" where
  root := `AnalysisBook

/-- The root of the `analysis` project (used for HTML generation here) -/
def analysisRoot : System.FilePath := "../analysis"

/--
A mapping from module names in the Lean code to the titles to be used for their sections.

A module is generated for each, containing the literate page. Its name is the module name from
`analysis` with `Book` prepended, so `Analysis.Section_2_1`'s literate page can be found by
importing `Book.Analysis.Section_2_1`. The page itself is named identically to its module.
-/
def sections := #[
  (`Analysis.Section_2_epilogue, "Equivalence of naturals"),
  (`Analysis.Section_2_1, "The Peano Axioms"),
  (`Analysis.Section_2_2, "Addition"),
  (`Analysis.Section_2_3, "Multiplication"),
  (`Analysis.Section_3_1, "Fundamentals"),
  (`Analysis.Section_3_2, "Russell's paradox"),
  (`Analysis.Section_3_3, "Functions"),
  (`Analysis.Section_3_4, "Images and inverse images"),
  (`Analysis.Section_3_5, "Cartesian products"),
  (`Analysis.Section_3_6, "Cardinality of sets"),
  (`Analysis.Section_4_1, "The integers"),
  (`Analysis.Section_4_2, "The rationals"),
  (`Analysis.Section_4_3, "Absolute value and exponentiation"),
  (`Analysis.Section_4_4, "Gaps in the rational numbers"),
  (`Analysis.Section_5_1, "Cauchy sequences"),
  (`Analysis.Section_5_2, "Equivalent Cauchy sequences"),
  (`Analysis.Section_5_3, "The construction of the real numbers"),
  (`Analysis.Section_5_4, "Ordering the reals"),
  (`Analysis.Section_5_5, "The least upper bound property"),
  (`Analysis.Section_5_epilogue, "Equivalence of reals"),
  (`Analysis.Section_6_1, "Convergence and limit laws"),
  (`Analysis.Section_6_2, "The extended real number system"),
  (`Analysis.Section_6_3, "Suprema and Infima of sequences"),
  (`Analysis.Section_6_4, "Limsup, Liminf, and limit points"),
  (`Analysis.Section_6_5, "Some standard limits"),
  (`Analysis.Section_6_6, "Subsequences"),
  (`Analysis.Section_6_epilogue, "Connections with Mathlib limits"),
  (`Analysis.Section_7_1, "Finite series"),
  (`Analysis.Section_7_2, "Infinite series"),
  (`Analysis.Section_7_3, "Sums of non-negative numbers"),
  (`Analysis.Section_7_4, "Rearrangement of series"),
  (`Analysis.Section_7_5, "The root and ratio tests"),
  (`Analysis.Section_9_1, "Subsets of the real line"),
  (`Analysis.Section_9_2, "The algebra of real-valued functions"),
  (`Analysis.Section_9_3, "Limiting values of functions"),
  (`Analysis.Section_9_4, "Continuous functions"),
  (`Analysis.Section_9_5, "Limits from the left and right"),
  (`Analysis.Section_9_6, "The maximum principle"),
  (`Analysis.Section_9_7, "The intermediate value theorem"),
  (`Analysis.Section_9_8, "Monotone functions"),
  (`Analysis.Section_9_9, "Uniform continuity"),
  (`Analysis.Section_9_10, "Limits at infinity"),
  (`Analysis.Section_10_1, "Basic definitions"),
  (`Analysis.Section_10_2, "Local maxima, local minima, and derivatives"),
  (`Analysis.Section_10_3, "Monotone functions and derivatives"),
  (`Analysis.Section_10_4, "The inverse function theorem"),
  (`Analysis.Section_10_5, "L'Hôpital's rule"),
  (`Analysis.Appendix_A_1, "Mathematical statements"),
  (`Analysis.Appendix_A_2, "Implication"),
  (`Analysis.Appendix_A_3, "The structure of proofs"),
  (`Analysis.Appendix_A_4, "Variables and quantifiers"),
  (`Analysis.Appendix_A_5, "Nested quantifiers"),
  (`Analysis.Appendix_A_6, "Some examples of proofs and quantifiers"),
  (`Analysis.Appendix_A_7, "Equality")
]

/--
Generates the JSON representation of the data needed for the literate page for the given module.

This is called as needed if the module has changed.
-/
def buildLiterateJson (pkg : NPackage n) (mod : String) : IO Unit := do
  let lakeVars :=
    #["LAKE", "LAKE_HOME", "LAKE_PKG_URL_MAP",
      "LEAN_SYSROOT", "LEAN_AR", "LEAN_PATH", "LEAN_SRC_PATH",
      "LEAN_GITHASH",
      "ELAN_TOOLCHAIN", "DYLD_LIBRARY_PATH", "LD_LIBRARY_PATH"]

  let lakefile := pkg.dir / analysisRoot / "lakefile.lean"
  let lakefile' := pkg.dir / analysisRoot / "lakefile.toml"
  let lakeConfig := if (← lakefile.pathExists) then lakefile else lakefile'


  let toolchainFile := pkg.dir / analysisRoot / "lean-toolchain"
  let toolchain := (← IO.FS.readFile toolchainFile).trim

  let f ← IO.FS.Handle.mk lakeConfig .read
  -- The locking here and in the generator prevent concurrent builds from interfering
  f.lock (exclusive := true)
  try
    let cmd := "elan"

    let args := #["run", "--install", toolchain, "lake", "build", s!"+{mod}:literate"]

    discard <| IO.Process.run {
      cmd, args, cwd := pkg.dir / analysisRoot,
      -- Unset Lake's environment variables
      env := lakeVars.map (·, none)
    }
  finally
    f.unlock


/-
**NOTE:** `genLib` needs to be built separately if an old version of
any of the generated modules with the correct imports does not yet exist.

This is because Lake currently traverses module imports before waiting on the
library's extra dependencies (i.e., the `genLib` job when part of `needs`).
This should fixed in a future Lake.
-/
target genLib (pkg) : Unit := do
  let j1 ← Job.mixArray <$> sections.mapM fun (module, title) => Job.async do
    let leanModName := `Book ++ module
    let declName := `Book ++ module
    -- This will fail if the `Book` library (below) is not defined
    let some mod ← findModule? leanModName
      | error s!"Failed to generate {leanModName}:\
          It has not been defined in the workspace."

    -- Get the name of the original Lean file that gives the chapter its content
    let origName := "/".intercalate (module.components.map (·.toString)) ++ ".lean"
    let origLeanFile : System.FilePath := pkg.dir / analysisRoot / origName
    -- Changes to the original Lean file should invalidate the generated code
    addTrace (← computeTrace <| TextFilePath.mk origLeanFile)
    -- We need to generate a file, but it doesn't need to be anything special. The sentinel file
    -- merely represents the fact that the JSON was updated in the main project. It's empty, but its
    -- trace file is important for cache invalidation.
    let jsonSentinel := defaultBuildDir / "originals" / module.toString
    buildFileUnlessUpToDate' jsonSentinel do
      logVerbose s!"Generating highlighting info for {module}"
      buildLiterateJson pkg module.toString
      createParentDirs jsonSentinel
      IO.FS.writeFile jsonSentinel "ok"

    -- Changes to the highlighting JSON should also invalidate the generated code
    let jsonName := "/".intercalate (module.components.map (·.toString)) ++ ".json"
    let jsonFile : System.FilePath := pkg.dir / analysisRoot / ".lake" / "build" / "literate" / jsonName
    addTrace (← computeTrace <| TextFilePath.mk jsonFile)

    -- The module itself contains the literate page
    let contents := s!"import AnalysisBook.LiterateModule\n\nset_option maxHeartbeats 1000000\n\nanalysis_page {declName} from {module} as {repr title}\n"
    addPureTrace contents "contents"

    buildFileUnlessUpToDate' mod.leanFile do
      logVerbose s!"Generating {mod.leanFile}"
      createParentDirs mod.leanFile
      IO.FS.writeFile mod.leanFile contents
      -- invalidate the module's build
      liftM (m := IO) <| try IO.FS.removeFile mod.oleanFile catch
        | .noFileOrDirectory .. => pure ()
        | e => throw e

  -- Also build a root module that imports all the modules, to avoid having to do it by hand in the
  -- main module
  let j2 ← Job.async do
    let rootName := `Book
    let some mod ← findModule? rootName
      | error s!"Failed to generate {rootName}:\
          It has not been defined in the workspace."
    let mut contents := ""
    for (module, title) in sections do
      contents := contents ++ s!"import {`Book ++ module} -- {title}\n"
    addPureTrace contents "contents"
    buildFileUnlessUpToDate' mod.leanFile do
      logVerbose s!"Generating {mod.leanFile}"
      createParentDirs mod.leanFile
      IO.FS.writeFile mod.leanFile contents
      -- invalidate the module's build
      liftM (m := IO) <| try IO.FS.removeFile mod.oleanFile catch
        | .noFileOrDirectory .. => pure ()
        | e => throw e
  pure <| Job.mix j1 j2

/-- Blocking until the job completes avoids the above caveat. -/
target genLibSync : Unit := do
  .pure <$> (← genLib.fetch).await

lean_lib Book where
  needs := #[genLibSync]
  srcDir := defaultBuildDir / "src"

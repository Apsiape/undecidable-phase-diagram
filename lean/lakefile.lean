import Lake
open Lake DSL
-- Release pin: Lean v4.35.0 (eb6cafb7290e8bd5f2937522d8d804f58f02bafc),
-- Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679, vendored as path packages under vendor/.
-- Builds go through scripts/replay.py (serial, -j1 -M6144, memory floor and process-tree cap);
-- the targets below call it so that `lake comparator` never rebuilds dependencies.
package UndecidablePhaseDiagram where
  moreLeanArgs := #["-j1", "-M6144"]
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]
require plausible from "vendor/plausible"
require LeanSearchClient from "vendor/LeanSearchClient"
require importGraph from "vendor/importGraph"
require proofwidgets from "vendor/proofwidgets"
require aesop from "vendor/aesop"
require Qq from "vendor/Qq"
require batteries from "vendor/batteries"
require Cli from "vendor/Cli"
require mathlib from "vendor/mathlib"
lean_lib UndecidablePhaseDiagram where
  globs := #[`UndecidablePhaseDiagram, `UndecidablePhaseDiagram.+]

target Challenge pkg : Unit := do
  Job.async do
    proc { cmd := if System.Platform.isWindows then "python" else "python3"
           args := #["-I", "-B", (pkg.dir / "scripts" / "replay.py").toString, "--resume"]
           cwd := some pkg.dir }

target Solution pkg : Unit := do
  Job.async do
    proc { cmd := if System.Platform.isWindows then "python" else "python3"
           args := #["-I", "-B", (pkg.dir / "scripts" / "replay.py").toString, "--resume"]
           cwd := some pkg.dir }

target Audit pkg : Unit := do
  Job.async do
    proc { cmd := if System.Platform.isWindows then "python" else "python3"
           args := #["-I", "-B", (pkg.dir / "scripts" / "replay.py").toString, "--resume"]
           cwd := some pkg.dir }

@[default_target]
target core pkg : Unit := do
  Job.async do
    proc { cmd := if System.Platform.isWindows then "python" else "python3"
           args := #["-I", "-B", (pkg.dir / "scripts" / "replay.py").toString, "--resume"]
           cwd := some pkg.dir }

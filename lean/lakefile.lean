import Lake
open Lake DSL

package UndecidablePhaseDiagram where
  moreLeanArgs := #["-j1", "-M6144"]
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]

require mathlib from git "https://github.com/leanprover-community/mathlib4" @
  "56a005855ea17e0b0958f73ec801ae140b0a1679"

-- Only this frozen statement module needs the Lean 4.35 compatibility option.
@[default_target]
lean_lib UPDStatements where
  roots := #[`UndecidablePhaseDiagram.Statements]
  moreLeanArgs := #["-Dbackward.isDefEq.respectTransparency=false"]

-- Together these two libraries preserve the original root/submodule coverage.
@[default_target]
lean_lib UndecidablePhaseDiagram where
  roots := #[]
  globs := #[.one `UndecidablePhaseDiagram, .one `UndecidablePhaseDiagram.Audit, .one `UndecidablePhaseDiagram.AuditCommand, .one `UndecidablePhaseDiagram.Background.BgMap, .one `UndecidablePhaseDiagram.Background.Computation, .one `UndecidablePhaseDiagram.Background.Conditioning, .one `UndecidablePhaseDiagram.Background.Construct, .one `UndecidablePhaseDiagram.Background.Freeze, .one `UndecidablePhaseDiagram.Background.Grids, .one `UndecidablePhaseDiagram.Background.Label, .one `UndecidablePhaseDiagram.Background.Line, .one `UndecidablePhaseDiagram.Background.Machine, .one `UndecidablePhaseDiagram.Background.Markers, .one `UndecidablePhaseDiagram.Background.Ready, .one `UndecidablePhaseDiagram.Background.Routing, .one `UndecidablePhaseDiagram.Background.Run, .one `UndecidablePhaseDiagram.Background.Split, .one `UndecidablePhaseDiagram.Background.Unique, .one `UndecidablePhaseDiagram.Compiler.Encode, .one `UndecidablePhaseDiagram.Compiler.Fold, .one `UndecidablePhaseDiagram.Compiler.OneSided, .one `UndecidablePhaseDiagram.Compiler.Universal, .one `UndecidablePhaseDiagram.Gibbs.Average, .one `UndecidablePhaseDiagram.Gibbs.Compare, .one `UndecidablePhaseDiagram.Gibbs.Cylinder, .one `UndecidablePhaseDiagram.Gibbs.Dobrushin, .one `UndecidablePhaseDiagram.Gibbs.Elim, .one `UndecidablePhaseDiagram.Gibbs.Existence, .one `UndecidablePhaseDiagram.Gibbs.Factor, .one `UndecidablePhaseDiagram.Gibbs.Hard, .one `UndecidablePhaseDiagram.Gibbs.Product, .one `UndecidablePhaseDiagram.Gibbs.Recode, .one `UndecidablePhaseDiagram.Gibbs.Site, .one `UndecidablePhaseDiagram.Gibbs.Transport, .one `UndecidablePhaseDiagram.Gibbs.Weights, .one `UndecidablePhaseDiagram.Hypotheses, .one `UndecidablePhaseDiagram.Interaction.Basic, .one `UndecidablePhaseDiagram.Main, .one `UndecidablePhaseDiagram.Payload.Bridge, .one `UndecidablePhaseDiagram.Payload.Coords, .one `UndecidablePhaseDiagram.Payload.EdgeSums, .one `UndecidablePhaseDiagram.Payload.Edges, .one `UndecidablePhaseDiagram.Payload.Effective, .one `UndecidablePhaseDiagram.Payload.Factor, .one `UndecidablePhaseDiagram.Payload.Graph, .one `UndecidablePhaseDiagram.Payload.Legal, .one `UndecidablePhaseDiagram.Payload.PayX, .one `UndecidablePhaseDiagram.Payload.Sensor, .one `UndecidablePhaseDiagram.Peierls.Contour, .one `UndecidablePhaseDiagram.Peierls.Flip, .one `UndecidablePhaseDiagram.Peierls.Lattice, .one `UndecidablePhaseDiagram.Peierls.Limit, .one `UndecidablePhaseDiagram.Peierls.Parity, .one `UndecidablePhaseDiagram.Proof.CorollaryB, .one `UndecidablePhaseDiagram.Proof.Main2, .one `UndecidablePhaseDiagram.Proof.MainTheorem, .one `UndecidablePhaseDiagram.Proof.Steps, .one `UndecidablePhaseDiagram.Proof.Thermal, .one `UndecidablePhaseDiagram.Proof.Windows, .one `UndecidablePhaseDiagram.Sanity, .one `UndecidablePhaseDiagram.Scaffold.Desub, .one `UndecidablePhaseDiagram.Scaffold.Frames, .one `UndecidablePhaseDiagram.Scaffold.Haar, .one `UndecidablePhaseDiagram.Scaffold.Legal, .one `UndecidablePhaseDiagram.Scaffold.Phase, .one `UndecidablePhaseDiagram.Scaffold.QuarterPhase, .one `UndecidablePhaseDiagram.Scaffold.Quarters, .one `UndecidablePhaseDiagram.Scaffold.Red, .one `UndecidablePhaseDiagram.Scaffold.Substitution, .one `UndecidablePhaseDiagram.Scaffold.TILaw, .one `UndecidablePhaseDiagram.Scaffold.Tables, .one `UndecidablePhaseDiagram.Scaffold.Tower, .one `UndecidablePhaseDiagram.Scaffold.Typical, .one `UndecidablePhaseDiagram.Scaffold.Walls]

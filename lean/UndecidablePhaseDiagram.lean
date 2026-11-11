/-
# Root module

Imports the whole formalization: the final theorems `UPD.theorem_A : UPD.TheoremA` and
`UPD.corollary_B : UPD.CorollaryB` (`Main.lean`; statements in `Statements.lean`), the named
hypotheses `H1`, `H2` (`Hypotheses.lean`, signed off in session 2), the Gibbs infrastructure
(`Gibbs/`, with products over components), Peierls' argument (`Peierls/`: `set:peierls` from `H2`), the scaffold of Section 3
(`Scaffold/`: `scf:desub`, `scf:phase`, `prop:scaffold-ti`, `scf:quarter`, `prop:quarter-ti`,
`scf:walls`, frames, typical phases, Haar measure on phases), the machine of App. C
(`Background/`: `mach:def-run`, `bg:ready`), Section 5 without measures (`Background/`:
`prop:routing`, `bg:grids`, `bg:grid`, `bg:markers`; `int:sub-split`; `prop:background`
(a)–(d), with the explicit construction of (b); `lem:freeze` (a)–(c), in the phase form of QB's
G.5 ruling), the payload coordinates of Section 6 with the frozen weight system and the
field-level bridge (`Payload/Coords.lean`), the measure-level bridge (`Payload/Bridge.lean`),
the transport of Gibbs measures, the cylinder characterization, factor specifications and
`pay:elim` for a general factor system (`Gibbs/Transport.lean`, `Cylinder.lean`, `Factor.lean`,
`Elim.lean`), the sensor sum of `pay:sum` (`Payload/Sensor.lean`), the legal payloads of the
background (`Payload/PayX.lean`, `Payload/Legal.lean`), the edges and their private coordinates
(`Payload/Edges.lean`), `pay:factor` (`Payload/Factor.lean`, with `Gibbs/Compare.lean`), the edge
sums (`Payload/EdgeSums.lean`), the graph `Γ_τ` and `pay:effective` (`Payload/Graph.lean`,
`Gibbs/Recode.lean`, `Payload/Effective.lean`), the proof of `thm:main` (`Proof/Steps.lean`,
`Proof/Main2.lean`, with averaging in `Gibbs/Average.lean`), the universal machine of Section 2.2
(`Compiler/`: one-sided machines over types, their numbering, the fold of a Mathlib `TM0` machine
onto a one-sided tape with unary input, Mathlib's halting problem; `exists_universal`), and the audit
of axioms (`Audit.lean`).
-/
import UndecidablePhaseDiagram.Main
import UndecidablePhaseDiagram.Hypotheses
import UndecidablePhaseDiagram.Gibbs.Existence
import UndecidablePhaseDiagram.Gibbs.Hard
import UndecidablePhaseDiagram.Gibbs.Product
import UndecidablePhaseDiagram.Peierls.Lattice
import UndecidablePhaseDiagram.Background.Ready
import UndecidablePhaseDiagram.Background.Markers
import UndecidablePhaseDiagram.Background.Computation
import UndecidablePhaseDiagram.Background.Freeze
import UndecidablePhaseDiagram.Payload.Coords
import UndecidablePhaseDiagram.Payload.Bridge
import UndecidablePhaseDiagram.Payload.Sensor
import UndecidablePhaseDiagram.Gibbs.Transport
import UndecidablePhaseDiagram.Gibbs.Cylinder
import UndecidablePhaseDiagram.Gibbs.Factor
import UndecidablePhaseDiagram.Gibbs.Elim
import UndecidablePhaseDiagram.Gibbs.Recode
import UndecidablePhaseDiagram.Gibbs.Compare
import UndecidablePhaseDiagram.Gibbs.Average
import UndecidablePhaseDiagram.Payload.Graph
import UndecidablePhaseDiagram.Payload.Legal
import UndecidablePhaseDiagram.Payload.Edges
import UndecidablePhaseDiagram.Payload.Factor
import UndecidablePhaseDiagram.Payload.EdgeSums
import UndecidablePhaseDiagram.Payload.Effective
import UndecidablePhaseDiagram.Proof.Steps
import UndecidablePhaseDiagram.Proof.Main2
import UndecidablePhaseDiagram.Compiler.OneSided
import UndecidablePhaseDiagram.Compiler.Encode
import UndecidablePhaseDiagram.Compiler.Fold
import UndecidablePhaseDiagram.Compiler.Universal
import UndecidablePhaseDiagram.Scaffold.TILaw
import UndecidablePhaseDiagram.Audit

set_option autoImplicit false

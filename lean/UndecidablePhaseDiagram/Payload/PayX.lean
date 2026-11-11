/-
# Section 6: the payloads compatible with `𝔟_τ` (definitions)

New in this project (session 10). The proof of `pay:factor` identifies the legal payloads of the
background `𝔟_τ` with explicit ones, parametrized by the spins `σ`, the switches `sw` at the roots
of the ready grids and the candidate free bits `yv` (`pay:factor`(a), (b): "the arm has all values
equal to `σ_u`", "the copies of each switch equal its value at the root", (C9)).

* `gB bv ι`: the mask `g⁻` (`ι` even) or `g⁺` (`ι` odd) of the cell record of a background value
  (`0` without a record): the `g^±` of (C9).
* `RCell U τ d j ξ`: `ξ = ξ(0, j)` in a grid of ready depth `d`; `RChan U τ d j ξ`: `ξ` lies on the
  column channel from `ξ(0, j)` up to (not including) `ξ(0, j + 1)` in a grid of ready depth `d`
  (where `ℓ^N ≠ ∘`).
* `colRoot τ d ξ`: the root `(ξ₁, r_d(m₂))` of the first column through `ξ`.
* **`payX U τ σ sw yv`**: the payload with spins `σ`, wire values from the spins at the roots
  (`wEc`, `wNc`, as in `cfg`), switch copies `sw (root) ι` at the cell records and along the first
  column of every ready grid (`ℓ^S` at `ξ` is `ℓ^N` at `ξ - e₂`, as in `cfg`), free bits
  `yv ξ ι ∧ x_ι ∧ g_ι`, and `0` elsewhere. `payX U τ σ (fun _ _ => false) (fun _ _ => false)` is
  the payload of `cfg U τ σ`.
-/
import UndecidablePhaseDiagram.Payload.Bridge

set_option autoImplicit false

noncomputable section

namespace UPD.BG

open UPD.Scaffold

variable (U : Machine) (τ : ℕ → Bool × Bool)

/-- The mask `g^±` of the cell record of a background value that goes with the free bit `y_ι` in
(C9) (`g⁻` for `ι = 0, 2`, `g⁺` for `ι = 1, 3`); `0` without a cell record. -/
def gB (bv : BgVal U) (ι : Fin 4) : Bool :=
  match bv.k with
  | some c => if ι.val % 2 = 0 then c.gm else c.gp
  | none => false

/-- `ξ = ξ(0, j)` in a grid of depth `d`, `d` ready. -/
def RCell (d j : ℕ) (ξ : Plane) : Prop := GPos τ (d, 0, j) ξ ∧ MachineM.ready U d

/-- `ξ` lies on the column channel above `ξ(0, j)` (`ζ_j ≤ ξ₂ < ζ_{j+1}` on the first column) of a
grid of depth `d`, `d` ready. -/
def RChan (d j : ℕ) (ξ : Plane) : Prop := VSeg τ (d, 0, j) ξ ∧ MachineM.ready U d

/-- The root of the first column through `ξ` at depth `d`: `(ξ₁, r_d(m₂))` with
`r_d(m₂) ≤ ξ₂ < r_d(m₂ + 1)`. -/
def colRoot (d : ℕ) (ξ : Plane) : Plane := (ξ.1, rootBelow (a2 τ) d ξ.2)

open Classical in
/-- The switch copies at `ξ`: `sw (root) ι` at the cell record of a site `ξ(0, j)` of a ready grid,
`0` elsewhere. -/
def kxX (sw : Plane → Fin 4 → Bool) (ξ : Plane) (ι : Fin 4) : Bool :=
  decide (∃ d j, RCell U τ d j ξ ∧ sw (colRoot τ d ξ) ι = true)

open Classical in
/-- The switch copies in `ℓ^N` at `ξ`: `sw (root) ι` on the first column of a ready grid where
`ℓ^N ≠ ∘`, `0` elsewhere. -/
def lNxX (sw : Plane → Fin 4 → Bool) (ξ : Plane) (ι : Fin 4) : Bool :=
  decide (∃ d j, RChan U τ d j ξ ∧ sw (colRoot τ d ξ) ι = true)

/-- **The payloads of `𝔟_τ`**: spins `σ`, wire values from the spins at the roots, switch copies
from `sw` along the first columns of the ready grids, free bits `yv ξ ι ∧ x_ι ∧ g_ι`, and `0`
elsewhere. -/
def payX (σ : Plane → Spin) (sw yv : Plane → Fin 4 → Bool) (ξ : Plane) : PayVal :=
  ⟨σ ξ, wEc τ σ (ξ.1 - 1, ξ.2), wEc τ σ ξ, wNc τ σ (ξ.1, ξ.2 - 1), wNc τ σ ξ,
    kxX U τ sw ξ,
    fun ι => yv ξ ι && kxX U τ sw ξ ι && gB U (bgMap U τ ξ) ι,
    lNxX U τ sw (ξ.1, ξ.2 - 1),
    lNxX U τ sw ξ⟩

/-- The rule (P3) on the free data: at a root of a ready grid, the switch pair `(0, 1)` of the
horizontal (vertical) sensor aligns the spin with the spin of the root to the west (south). -/
def P3X (σ : Plane → Spin) (sw : Plane → Fin 4 → Bool) : Prop :=
  ∀ d : ℕ, ∀ m1 m2 : ℤ, 1 ≤ d → MachineM.ready U d →
    ((sw (root τ d m1 m2) 0 = false ∧ sw (root τ d m1 m2) 1 = true) →
        σ (root τ d m1 m2) = σ (root τ d (m1 - 1) m2)) ∧
      ((sw (root τ d m1 m2) 2 = false ∧ sw (root τ d m1 m2) 3 = true) →
        σ (root τ d m1 m2) = σ (root τ d m1 (m2 - 1)))

end UPD.BG

/-
# Section 3.5: light walls of a tiling of `𝔸^q` (`scf:walls`)

New in this project: `scf:walls` for every tiling `Y` of `𝔸^q` with quarter phase `τ`,
`τ₁, τ₂ ∉ ℤ`, in terms of the statement-level walls `Quarter.VW`, `Quarter.HW` and the frames of
`scf:def-frames` (offsets `a^{(i)}_d = τ_i mod 4^{d+1}`, `phaseOffsets`). From the parent-tower
form (`walls_col`, `walls_row`, `Scaffold/Quarters.lean`) by the translation by `ε`.

* `NotInt c`: the 2-adic integer with digits `c` is not in `ℤ` (`z - τ_i ≠ 0` for every `z ∈ ℤ`:
  some binary digit of `z - τ_i` is `1`); then every coordinate of the parent tiling has a finite
  rank (`NotInt.tail`, `NotInt.exists_rank`), the remark after `scf:walls`.
* **`scf:walls`**: `walls_VW`, `walls_HW`.
-/
import UndecidablePhaseDiagram.Scaffold.QuarterPhase
import UndecidablePhaseDiagram.Scaffold.Frames

set_option autoImplicit false

namespace UPD.Scaffold

/-- `τ_i ∉ ℤ`, for the 2-adic integer `τ_i` with binary digits `c`: for every integer `z`, the
binary expansion of `z - τ_i` has a digit `1` (so `z - τ_i ≠ 0`). -/
def NotInt (c : ℕ → Bool) : Prop := ∀ z : ℤ, ∃ m, dig c m z = true

/-- `τ_i = ε_i + 2ϖ_i ∉ ℤ` gives `ϖ_i ∉ ℤ`. -/
theorem NotInt.tail {c : ℕ → Bool} (h : NotInt c) : NotInt (fun m => c (m + 1)) := by
  intro z
  obtain ⟨m, hm⟩ := h (2 * z + bitZ (c 0))
  cases m with
  | zero =>
    rw [dig_zero, decide_eq_true_iff] at hm
    omega
  | succ m =>
    rw [dig_succ] at hm
    refine ⟨m, ?_⟩
    have e : (2 * z + bitZ (c 0) - bitZ (c 0)) / 2 = z := by omega
    rwa [e] at hm

/-- The remark after `scf:walls`: if `ϖ_i ∉ ℤ`, every coordinate has a finite rank. -/
theorem NotInt.exists_rank {c : ℕ → Bool} (h : NotInt c) (z : ℤ) : ∃ r, IsRank c z r := by
  classical
  exact ⟨Nat.find (h z), Nat.find_spec (h z), fun m hm => by simpa using Nat.find_min (h z) hm⟩

theorem isLeftEnd_add (a : ℕ → ℤ) (e : ℤ) (d : ℕ) (z : ℤ) :
    IsLeftEnd (fun d => e + a d) d z ↔ IsLeftEnd a d (z - e) := by
  simp only [IsLeftEnd, frameLo]
  constructor <;> rintro ⟨m, hm⟩ <;> exact ⟨m, by linarith⟩

theorem isRightEnd_add (a : ℕ → ℤ) (e : ℤ) (d : ℕ) (z : ℤ) :
    IsRightEnd (fun d => e + a d) d z ↔ IsRightEnd a d (z - e) := by
  simp only [IsRightEnd, frameHi]
  constructor <;> rintro ⟨m, hm⟩ <;> exact ⟨m, by linarith⟩

theorem inFrame_add (a : ℕ → ℤ) (e : ℤ) (d : ℕ) (z : ℤ) :
    InFrame (fun d => e + a d) d z ↔ InFrame a d (z - e) := by
  simp only [InFrame, frameLo, frameHi]
  constructor <;> rintro ⟨m, h1, h2⟩ <;> exact ⟨m, by linarith, by linarith⟩

/-- `a_d = τ_i mod 4^{d+1} = ε_i + 2 (ϖ_i mod 2^{2d+1})`. -/
theorem phaseOffsets_eq (c : ℕ → Bool) :
    phaseOffsets c = fun d => bitZ (c 0) + 2 * wsum (fun m => c (m + 1)) (2 * d + 1) := by
  funext d; rfl

theorem map_toLR_eq_some (v : Option Side) (s : Side) : v.map Side.toLR = some s.toLR ↔ v = some s := by
  rcases v with _ | v
  · simp
  · cases v <;> cases s <;> simp [Side.toLR]

theorem map_toBT_eq_some (v : Option Side) (s : Side) : v.map Side.toBT = some s.toBT ↔ v = some s := by
  rcases v with _ | v
  · simp
  · cases v <;> cases s <;> simp [Side.toBT]

/-- **`scf:walls`** (vertical walls). Let `Y` be a tiling of `𝔸^q` with quarter phase `τ`, where
`τ₁ ∉ ℤ`. Then `Y(ξ)` lies on a light vertical wall as a left (right) side iff there are `d ≥ 1`
and `m, m'` such that `ξ₁` is the left (right) endpoint of the column frame `I^{(1)}_d(m)` and
`ξ₂ ∈ I^{(2)}_d(m')`. -/
theorem walls_VW {Y : Plane → Quarter} {τ : ℕ → Bool × Bool} (hY : IsQPhase Y τ)
    (hτ1 : NotInt (col τ)) (ξ : Plane) (s : Side) :
    (Y ξ).VW = some s.toLR ↔ ∃ d, 1 ≤ d ∧
      ((s = .lo ∧ IsLeftEnd (phaseOffsets (col τ)) d ξ.1) ∨
        (s = .hi ∧ IsRightEnd (phaseOffsets (col τ)) d ξ.1)) ∧
      InFrame (phaseOffsets (row τ)) d ξ.2 := by
  obtain ⟨f, -, rfl, F, hF, hF0⟩ := hY
  obtain ⟨r, hr⟩ := (NotInt.tail hτ1).exists_rank ((ξ - bvec (τ 0)).1 / 2)
  have hw := walls_col (hF.towerRel (r + 2))
    (a := fun d => 2 * wsum (col fun m => τ (m + 1)) (2 * d + 1))
    (a' := fun d => 2 * wsum (row fun m => τ (m + 1)) (2 * d + 1)) (fun d => rfl) (fun d => rfl)
    (ξ := ξ - bvec (τ 0)) hr le_rfl s
  have hV : (qshift (τ 0) f ξ).VW =
      (vWall (quad (ξ - bvec (τ 0))) (F 0 (half (ξ - bvec (τ 0))))).map Side.toLR := by
    rw [hF0]; exact VW_quartering f _
  rw [hV, map_toLR_eq_some, hw, phaseOffsets_eq, phaseOffsets_eq]
  simp only [isLeftEnd_add, isRightEnd_add, inFrame_add]
  rfl

/-- **`scf:walls`** (horizontal walls): if `τ₂ ∉ ℤ`, `Y(ξ)` lies on a light horizontal wall as a
bottom (top) side iff there are `d ≥ 1` and `m, m'` such that `ξ₂` is the left (right) endpoint of
the row frame `I^{(2)}_d(m')` and `ξ₁ ∈ I^{(1)}_d(m)`. -/
theorem walls_HW {Y : Plane → Quarter} {τ : ℕ → Bool × Bool} (hY : IsQPhase Y τ)
    (hτ2 : NotInt (row τ)) (ξ : Plane) (s : Side) :
    (Y ξ).HW = some s.toBT ↔ ∃ d, 1 ≤ d ∧
      ((s = .lo ∧ IsLeftEnd (phaseOffsets (row τ)) d ξ.2) ∨
        (s = .hi ∧ IsRightEnd (phaseOffsets (row τ)) d ξ.2)) ∧
      InFrame (phaseOffsets (col τ)) d ξ.1 := by
  obtain ⟨f, -, rfl, F, hF, hF0⟩ := hY
  obtain ⟨r, hr⟩ := (NotInt.tail hτ2).exists_rank ((ξ - bvec (τ 0)).2 / 2)
  have hw := walls_row (hF.towerRel (r + 2))
    (a := fun d => 2 * wsum (col fun m => τ (m + 1)) (2 * d + 1))
    (a' := fun d => 2 * wsum (row fun m => τ (m + 1)) (2 * d + 1)) (fun d => rfl) (fun d => rfl)
    (ξ := ξ - bvec (τ 0)) hr le_rfl s
  have hH : (qshift (τ 0) f ξ).HW =
      (hWall (quad (ξ - bvec (τ 0))) (F 0 (half (ξ - bvec (τ 0))))).map Side.toBT := by
    rw [hF0]; exact HW_quartering f _
  rw [hH, map_toBT_eq_some, hw, phaseOffsets_eq, phaseOffsets_eq]
  simp only [isLeftEnd_add, isRightEnd_add, inFrame_add]
  rfl

end UPD.Scaffold

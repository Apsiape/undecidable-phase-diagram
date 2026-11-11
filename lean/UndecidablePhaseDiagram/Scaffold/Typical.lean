/-
# Section 3.5: typical phases (`scf:def-typical`)

New in this project.

* **`scf:def-typical`** (`Typical`): a quarter phase `τ` is typical if it is resolving
  (`QResolving`), `τ₁, τ₂ ∉ ℤ` (`NotInt`, P-8), and for `i = 1, 2` and every `z ∈ ℤ` the base-4
  expansion of `z - τ_i` has the digit `2` in some position `d ≥ 1` (`Digit2`).
  **[choice] (proof side, as P-7)** The base-4 digit of `z - τ_i` at position `d` is read off its
  binary digits `2d`, `2d + 1`, which are `ς_{2d}(z)`, `ς_{2d+1}(z)` (`scf:eq-digits`,
  `emod_eq_wsum_dig`): the digit is `2` iff they are `0` and `1`. `digit2_iff` shows that this is
  the residue condition `(z - a_d) mod 4^{d+1} ∈ [2·4^d, 3·4^d)` of `scf:frames`(e).
* The remark after `scf:def-typical`: for a typical `τ` every integer lies in a frame in each
  direction, so it has a finite owner depth (`Typical.inFrame_col`, `Typical.inFrame_row`; the
  hypothesis of `own`).
-/
import UndecidablePhaseDiagram.Scaffold.Walls

set_option autoImplicit false

namespace UPD.Scaffold

/-- `scf:def-typical`: the base-4 digit of `z - τ_i` at position `d` is `2`, where `τ_i` has binary
digits `c`: the binary digits `ς_{2d}(z)`, `ς_{2d+1}(z)` of `z - τ_i` are `0` and `1`. -/
def Digit2 (c : ℕ → Bool) (z : ℤ) (d : ℕ) : Prop :=
  dig c (2 * d) z = false ∧ dig c (2 * d + 1) z = true

/-- **`scf:def-typical`**: the quarter phase `τ` is *typical* if it is resolving, `τ₁, τ₂ ∉ ℤ`,
and for `i = 1, 2` and every `z ∈ ℤ` the base-4 expansion of `z - τ_i` has the digit `2` in some
position `d ≥ 1`. -/
def Typical (τ : ℕ → Bool × Bool) : Prop :=
  QResolving τ ∧ NotInt (col τ) ∧ NotInt (row τ) ∧
    (∀ z : ℤ, ∃ d, 1 ≤ d ∧ Digit2 (col τ) z d) ∧ (∀ z : ℤ, ∃ d, 1 ≤ d ∧ Digit2 (row τ) z d)

/-- The base-4 digit `2` at position `d` is the residue condition of `scf:frames`(e):
`(z - a_d) mod 4^{d+1} ∈ [2·4^d, 3·4^d)`, `a_d = τ_i mod 4^{d+1}`. -/
theorem digit2_iff (c : ℕ → Bool) (z : ℤ) (d : ℕ) :
    Digit2 c z d ↔ 2 * 4 ^ d ≤ (z - phaseOffsets c d) % 4 ^ (d + 1) ∧
      (z - phaseOffsets c d) % 4 ^ (d + 1) < 3 * 4 ^ d := by
  have h := emod_eq_wsum_dig c (2 * d + 2) z
  rw [← four_pow_eq_two_pow'] at h
  simp only [phaseOffsets]
  rw [h, show 2 * d + 2 = 2 * d + 1 + 1 by ring, wsum_succ_top, wsum_succ_top]
  have hw0 := wsum_nonneg (fun m => dig c m z) (2 * d)
  have hw1 := wsum_lt (fun m => dig c m z) (2 * d)
  have e1 : (2 : ℤ) ^ (2 * d) = 4 ^ d := by rw [pow_mul]; norm_num
  have e2 : (2 : ℤ) ^ (2 * d + 1) = 2 * 4 ^ d := by rw [pow_succ, pow_mul]; norm_num; ring
  rw [e1] at hw1
  rw [e1, e2]
  generalize (4 : ℤ) ^ d = P at hw1 ⊢
  generalize wsum (fun m => dig c m z) (2 * d) = W at hw0 hw1 ⊢
  simp only [Digit2]
  cases dig c (2 * d) z <;> cases dig c (2 * d + 1) z <;> simp [bitZ] <;> omega

/-- The remark after `scf:def-typical` (by `scf:frames`(e)): for a typical `τ`, every integer lies
in the interior of a column frame. -/
theorem Typical.inFrame_col {τ : ℕ → Bool × Bool} (h : Typical τ) (z : ℤ) :
    ∃ d, 1 ≤ d ∧ InFrame (phaseOffsets (col τ)) d z := by
  obtain ⟨d, hd, h2⟩ := h.2.2.2.1 z
  obtain ⟨m, h1, h1'⟩ := interior_of_digit_two _ hd ((digit2_iff _ z d).1 h2).1
    ((digit2_iff _ z d).1 h2).2
  exact ⟨d, hd, m, h1.le, h1'.le⟩

/-- The remark after `scf:def-typical`: for a typical `τ`, every integer lies in the interior of a
row frame. -/
theorem Typical.inFrame_row {τ : ℕ → Bool × Bool} (h : Typical τ) (z : ℤ) :
    ∃ d, 1 ≤ d ∧ InFrame (phaseOffsets (row τ)) d z := by
  obtain ⟨d, hd, h2⟩ := h.2.2.2.2 z
  obtain ⟨m, h1, h1'⟩ := interior_of_digit_two _ hd ((digit2_iff _ z d).1 h2).1
    ((digit2_iff _ z d).1 h2).2
  exact ⟨d, hd, m, h1.le, h1'.le⟩

end UPD.Scaffold

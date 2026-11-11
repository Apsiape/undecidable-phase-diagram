/-
# Factor specifications (the paragraph after `set:def-gibbs`)

New in this project (session 9). "Let `(W_k)` be nonnegative factors, each depending on finitely
many coordinates, with every coordinate in finitely many of them. The kernel of a finite set `S`
of coordinates is proportional to the product of the factors that involve a coordinate of `S`."
`FactorSystem` records the factors `φ_k` with their supports and, for each coordinate, the finite
set of factors involving it (`at_`); `toHard` is the hard-constraint weight system
`W_S = ∏_{k meets S} φ_k` (`Gibbs/Hard.lean`): ratio and support properties hold because the
factors meeting `Δ` but not `S ⊆ Δ` do not involve the coordinates of `S`.
-/
import UndecidablePhaseDiagram.Gibbs.Hard

set_option autoImplicit false

noncomputable section

namespace UPD

namespace Gibbs

/-- Nonnegative factors `φ_k` with finite supports, every coordinate in finitely many supports. -/
structure FactorSystem (I E K : Type) [DecidableEq I] [DecidableEq K] where
  /-- The coordinates on which `φ_k` depends. -/
  supp : K → Finset I
  /-- The factor `φ_k`. -/
  φ : K → (I → E) → ℝ
  nonneg : ∀ (k : K) (x : I → E), 0 ≤ φ k x
  isLocal : ∀ (k : K) (x x' : I → E), (∀ i ∈ supp k, x i = x' i) → φ k x = φ k x'
  /-- The factors whose support contains the coordinate `i`. -/
  at_ : I → Finset K
  mem_at : ∀ (i : I) (k : K), k ∈ at_ i ↔ i ∈ supp k

namespace FactorSystem

variable {I E K : Type} [DecidableEq I] [DecidableEq K] (fs : FactorSystem I E K)

/-- The factors that involve a coordinate of `Λ`. -/
def meets (Λ : Finset I) : Finset K := Λ.biUnion fs.at_

theorem mem_meets {Λ : Finset I} {k : K} : k ∈ fs.meets Λ ↔ ∃ i ∈ Λ, i ∈ fs.supp k := by
  simp only [meets, Finset.mem_biUnion, fs.mem_at]

theorem meets_mono {Λ Δ : Finset I} (h : Λ ⊆ Δ) : fs.meets Λ ⊆ fs.meets Δ :=
  Finset.biUnion_subset_biUnion_of_subset_left _ h

/-- `W_Λ = ∏_{k meets Λ} φ_k`. -/
def W (Λ : Finset I) (x : I → E) : ℝ := ∏ k ∈ fs.meets Λ, fs.φ k x

/-- **The factor specification** as a hard-constraint weight system. -/
def toHard : HardWeightSystem I E where
  W := fs.W
  nonneg Λ x := Finset.prod_nonneg fun k _ => fs.nonneg k x
  range Λ := (fs.meets Λ).biUnion fs.supp
  isLocal Λ x x' h := Finset.prod_congr rfl fun k hk =>
    fs.isLocal k x x' fun i hi => h i (Finset.mem_biUnion.2 ⟨k, hk, hi⟩)
  ratio Λ Δ hΛΔ x x' hoff := by
    have hsub := fs.meets_mono hΛΔ
    have hR : ∏ k ∈ fs.meets Δ \ fs.meets Λ, fs.φ k x =
        ∏ k ∈ fs.meets Δ \ fs.meets Λ, fs.φ k x' :=
      Finset.prod_congr rfl fun k hk => fs.isLocal k x x' fun i hi =>
        hoff i fun hiΛ => (Finset.mem_sdiff.1 hk).2 (fs.mem_meets.2 ⟨i, hiΛ, hi⟩)
    show (∏ k ∈ fs.meets Δ, fs.φ k x) * (∏ k ∈ fs.meets Λ, fs.φ k x') =
      (∏ k ∈ fs.meets Δ, fs.φ k x') * ∏ k ∈ fs.meets Λ, fs.φ k x
    rw [← Finset.prod_sdiff hsub, ← Finset.prod_sdiff hsub (f := fun k => fs.φ k x'), hR]
    ring
  support Λ Δ hΛΔ x h0 := by
    obtain ⟨k, hk, hz⟩ := Finset.prod_eq_zero_iff.1 h0
    exact Finset.prod_eq_zero (fs.meets_mono hΛΔ hk) hz

theorem toHard_W (Λ : Finset I) (x : I → E) : fs.toHard.W Λ x = ∏ k ∈ fs.meets Λ, fs.φ k x := rfl

theorem toHard_range (Λ : Finset I) : fs.toHard.range Λ = (fs.meets Λ).biUnion fs.supp := rfl

/-- At a configuration where every weight is positive, every factor is positive. -/
theorem φ_pos_of_W_pos {x : I → E} (h : ∀ Λ : Finset I, 0 < fs.toHard.W Λ x) {k : K}
    {i : I} (hi : i ∈ fs.supp k) : 0 < fs.φ k x := by
  have hk : k ∈ fs.meets {i} := fs.mem_meets.2 ⟨i, Finset.mem_singleton_self i, hi⟩
  have hW := h {i}
  rw [toHard_W] at hW
  rcases (fs.nonneg k x).eq_or_lt with h0 | h0
  · rw [Finset.prod_eq_zero hk h0.symm] at hW
    exact absurd hW (lt_irrefl 0)
  · exact h0

/-- If every factor is positive at `x`, every weight is. -/
theorem W_pos_of_φ_pos {x : I → E} (h : ∀ k : K, 0 < fs.φ k x) (Λ : Finset I) :
    0 < fs.toHard.W Λ x :=
  Finset.prod_pos fun k _ => h k

end FactorSystem

end Gibbs

end UPD

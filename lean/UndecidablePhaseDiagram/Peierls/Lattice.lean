/-
# The square lattice as an Ising model on a graph (`set:sub-ising`)

`set:sub-ising` defines the Ising model on a countable graph `G` by the factors
`exp(J_{uv} σ_u σ_v)`, one per edge; "on `ℤ²` with all couplings equal to `J` we speak of the
Ising model with coupling `J`". `H2` and `set:peierls` (`Peierls/Limit.lean`) are stated with the
finite-volume measures of [FV] (`Ising.expect`, the bonds `ℰ^b_Λ` meeting `Λ`). This file checks
that the two agree: for the square lattice `squareLattice J` (neighbours `x ± e₁`, `x ± e₂`,
coupling `J` on every edge), the kernel of the weight system of `Gibbs/Dobrushin.lean` is
`Ising.expect J` (`expect_squareLattice`), so the Gibbs measures in the sense of `H2`(3) are exactly
those of the graph model (`isIsingGibbs_iff`), and the plus and minus states of `set:peierls` are
Gibbs measures of the Ising model on `ℤ²` with coupling `J` in the sense of `set:sub-ising`
(`peierls_squareLattice`).
-/
import UndecidablePhaseDiagram.Peierls.Limit
import UndecidablePhaseDiagram.Gibbs.Existence

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace UPD

namespace Peierls

open Ising Gibbs

/-- The four neighbours `x ± e₁`, `x ± e₂` of a site. -/
def nbrs (x : Plane) : Finset Plane := {x + e1, x - e1, x + e2, x - e2}

/-- `set:sub-ising`: the Ising model on `ℤ²` with all couplings equal to `J ≥ 0`. -/
def squareLattice (J : ℝ) (hJ : 0 ≤ J) : IsingGraph Plane where
  nbr := nbrs
  symm u v h := by
    simp only [nbrs, Finset.mem_insert, Finset.mem_singleton] at h ⊢
    rcases h with rfl | rfl | rfl | rfl <;> simp
  irrefl u h := by
    simp only [nbrs, Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff, e1, e2,
      Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] at h
    omega
  J _ := J
  J_nonneg _ := hJ

theorem card_nbrs_le (x : Plane) : (nbrs x).card ≤ 4 := Finset.card_le_four

/-- The edge `{x, x + e_k}` of a bond. -/
def bondEdge (b : Bond) : Sym2 Plane := s(b.1, b.1 + bondDir b.2)

theorem bondEdge_injective : Function.Injective bondEdge := by
  rintro ⟨x, k⟩ ⟨y, k'⟩ h
  simp only [bondEdge, Sym2.eq_iff] at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · subst h1
    cases k <;> cases k' <;>
      simp_all [bondDir, e1, e2, Prod.ext_iff]
  · exfalso
    cases k <;> cases k' <;>
      simp only [bondDir, e1, e2, Prod.ext_iff, Prod.fst_add, Prod.snd_add] at h1 h2 <;> omega

/-- The edges of the square lattice meeting `Λ` are the edges of the bonds `ℰ^b_Λ`. -/
theorem edgesMeeting_eq (J : ℝ) (hJ : 0 ≤ J) (Λ : Finset Plane) :
    (squareLattice J hJ).edgesMeeting Λ = (bonds Λ).image bondEdge := by
  ext e
  rw [IsingGraph.mem_edgesMeeting, Finset.mem_image]
  constructor
  · rintro ⟨u, hu, v, hv, rfl⟩
    simp only [squareLattice, nbrs, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact ⟨(u, false), (mem_bonds _ _ _).2 (Or.inl hu), rfl⟩
    · refine ⟨(u - e1, false), (mem_bonds _ _ _).2 (Or.inr (by simpa [bondDir] using hu)), ?_⟩
      simp only [bondEdge, bondDir, sub_add_cancel]
      exact Sym2.eq_swap
    · exact ⟨(u, true), (mem_bonds _ _ _).2 (Or.inl hu), rfl⟩
    · refine ⟨(u - e2, true), (mem_bonds _ _ _).2 (Or.inr (by simpa [bondDir] using hu)), ?_⟩
      simp only [bondEdge, bondDir, sub_add_cancel]
      exact Sym2.eq_swap
  · rintro ⟨⟨x, k⟩, hb, rfl⟩
    rcases (mem_bonds _ _ _).1 hb with h | h
    · refine ⟨x, h, x + bondDir k, ?_, rfl⟩
      cases k <;> simp [squareLattice, nbrs, bondDir]
    · refine ⟨x + bondDir k, h, x, ?_, Sym2.eq_swap⟩
      cases k <;> simp [squareLattice, nbrs, bondDir]

/-- **The weights agree**: `∏_{e meets Λ} exp(J σ_u σ_v) = exp(J ∑_{ℰ^b_Λ} σ_x σ_y)`. -/
theorem weight_squareLattice (J : ℝ) (hJ : 0 ≤ J) (Λ : Finset Plane) (σ : Config Spin) :
    (squareLattice J hJ).weight Λ σ = Ising.weight J Λ σ := by
  unfold IsingGraph.weight IsingGraph.energySum Ising.weight
  congr 1
  rw [edgesMeeting_eq, Finset.sum_image (fun b _ b' _ h => bondEdge_injective h), Finset.mul_sum]
  rfl

/-- **The kernels agree**: the kernel of the square lattice is `Ising.expect J`. -/
theorem expect_squareLattice (J : ℝ) (hJ : 0 ≤ J) (Λ : Finset Plane) (ω : Config Spin)
    (F : Config Spin → ℝ) :
    (squareLattice J hJ).toWeightSystem.expect Λ ω F = Ising.expect J Λ ω F := by
  simp only [WeightSystem.expect, WeightSystem.prob, WeightSystem.Z, IsingGraph.toWeightSystem_W,
    weight_squareLattice, Ising.expect, ← fill_eq_fillOn, div_mul_eq_mul_div, Finset.sum_div]

/-- The Gibbs measures of `H2`(3) are those of the graph model `squareLattice J`. -/
theorem isIsingGibbs_iff (J : ℝ) (hJ : 0 ≤ J) (ν : Measure (Config Spin)) :
    IsIsingGibbs J ν ↔ (squareLattice J hJ).toWeightSystem.IsDLR ν := by
  simp only [IsIsingGibbs, WeightSystem.IsDLR, expect_squareLattice]

/-- **`set:peierls`, in the vocabulary of `set:sub-ising`**: the plus and minus states are Gibbs
measures of the Ising model on `ℤ²` with coupling `J`, translation invariant, exchanged by the
flip; if `e^J ≥ 3` they differ, with `ν⁺(σ₀ = -1) ≤ 1/3` and `ν⁻(σ₀ = +1) ≤ 1/3`. -/
theorem peierls_squareLattice (h2 : H2) {J : ℝ} (hJ : 0 ≤ J) :
    ∃ νp νm : Measure (Config Spin),
      (squareLattice J hJ).toWeightSystem.IsDLR νp ∧
      (squareLattice J hJ).toWeightSystem.IsDLR νm ∧
      IsLimitState J plusConfig νp ∧ IsLimitState J minusConfig νm ∧
      IsTranslationInvariantMeasure νp ∧ IsTranslationInvariantMeasure νm ∧
      νm = νp.map flipConfig ∧ νp = νm.map flipConfig ∧
      (3 ≤ Real.exp J → νp.real {σ : Config Spin | σ 0 = .minus} ≤ 1 / 3 ∧
        νm.real {σ : Config Spin | σ 0 = .plus} ≤ 1 / 3 ∧ νp ≠ νm) := by
  obtain ⟨νp, νm, h1, h2', h3, h4, h5, h6, h7, h8, h9⟩ := peierls h2 hJ
  exact ⟨νp, νm, (isIsingGibbs_iff J hJ νp).1 h1, (isIsingGibbs_iff J hJ νm).1 h2', h3, h4, h5,
    h6, h7, h8, h9⟩

end Peierls

end UPD

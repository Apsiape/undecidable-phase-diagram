/-
# Sanity of the statement-level Gibbs definitions (`set:def-gibbs`)

Guards for the fidelity of `IsGibbs` (`Statements.lean`, decision D4), checked against the paper's
text of `set:def-gibbs`:
* `measurableSet_legal`: the set `X_Φ` of legal configurations is measurable, so `μ(X_Φ) = 1` is
  a genuine condition;
* `energy_lt_top_of_legal`, `partitionFunction_pos`: for a nearest-neighbour interaction and a
  legal `ω`, `H_Λ(ω) < ∞` and `Z_Λ(ω) ≥ e^{-βH_Λ(ω)} > 0` ("It is well defined, since
  `Z_Λ(ω) ≥ e^{-βH_Λ(ω)} > 0`");
* `kernelApply_eq_integral`, `isProbability_gibbsKernel`: `(γ_Λ F)(ω) = ∫ F dγ_Λ(· | ω)` for the
  measure `γ_Λ(· | ω) = ∑_ζ e^{-βH_Λ(ω^ζ)} / Z_Λ(ω) · δ_{ω^ζ}`, a probability measure when
  `Z_Λ(ω) > 0` (in particular at legal `ω`);
* `measurable_kernelApply`, `abs_kernelApply_le`: for bounded measurable `F`, `γ_Λ F` is
  measurable and bounded by the same bound, so the right side of the DLR identity is the integral
  of a bounded measurable function.
-/
import UndecidablePhaseDiagram.Gibbs.Weights

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace UPD

/-- The discrete σ-algebra on the site alphabet (it is `⊤`). -/
instance (U : Machine) : DiscreteMeasurableSpace (SiteVal U) := ⟨fun _ => trivial⟩

namespace Gibbs

variable {S : Type} [Fintype S] [MeasurableSpace S] [DiscreteMeasurableSpace S]

/-- `fill` is the general `fillOn` on the plane. -/
theorem fill_eq_fillOn (ω : Config S) (Λ : Finset Plane) (ζ : Λ → S) :
    fill ω Λ ζ = fillOn ω Λ ζ := rfl

/-- `Φ_A` is measurable (it depends on the finitely many coordinates in `A`). -/
theorem measurable_interaction {Φ : Interaction S} (hΦ : IsInteraction Φ) (A : Finset Plane) :
    Measurable (Φ A) :=
  measurable_of_dependsOn A (Φ A) (hΦ A)

/-- **`X_Φ` is measurable.** -/
theorem measurableSet_legal {Φ : Interaction S} (hΦ : IsInteraction Φ) :
    MeasurableSet {ω : Config S | IsLegal Φ ω} := by
  have : {ω : Config S | IsLegal Φ ω} = ⋂ A : Finset Plane, {ω | Φ A ω < ⊤} := by
    ext ω; simp [IsLegal]
  rw [this]
  exact MeasurableSet.iInter fun A =>
    measurableSet_lt (measurable_interaction hΦ A) measurable_const

/-- The energy is measurable. -/
theorem measurable_energy {Φ : Interaction S} (hΦ : IsInteraction Φ) (Λ : Finset Plane) :
    Measurable (energy Φ Λ) :=
  Measurable.ennreal_tsum fun A => measurable_interaction hΦ A.1

/-- The finitely many sets `A` that can carry a nonzero term of a nearest-neighbour interaction
and meet `Λ`. -/
def nnSets (Λ : Finset Plane) : Finset (Finset Plane) :=
  (Λ ∪ Λ.image (fun x => x - e1) ∪ Λ.image (fun x => x - e2)).biUnion
    fun ξ => {{ξ}, {ξ, ξ + e1}, {ξ, ξ + e2}}

theorem mem_nnSets {Φ : Interaction S} (hΦ : IsNearestNeighbour Φ) {Λ A : Finset Plane}
    (hA : (A ∩ Λ).Nonempty) {ω : Config S} (h0 : Φ A ω ≠ 0) : A ∈ nnSets Λ := by
  obtain ⟨y, hy⟩ := hA
  rw [Finset.mem_inter] at hy
  simp only [nnSets, Finset.mem_biUnion, Finset.mem_union, Finset.mem_image,
    Finset.mem_insert, Finset.mem_singleton]
  by_contra hcon
  apply h0
  refine hΦ A ?_ ?_ ?_ ω
  · rintro ⟨ξ, rfl⟩
    exact hcon ⟨ξ, Or.inl (Or.inl ((Finset.mem_singleton.1 hy.1) ▸ hy.2)), Or.inl rfl⟩
  · rintro ⟨ξ, rfl⟩
    rcases Finset.mem_insert.1 hy.1 with h | h
    · exact hcon ⟨ξ, Or.inl (Or.inl (h ▸ hy.2)), Or.inr (Or.inl rfl)⟩
    · rw [Finset.mem_singleton] at h
      exact hcon ⟨ξ, Or.inl (Or.inr ⟨y, hy.2, by rw [h]; abel⟩), Or.inr (Or.inl rfl)⟩
  · rintro ⟨ξ, rfl⟩
    rcases Finset.mem_insert.1 hy.1 with h | h
    · exact hcon ⟨ξ, Or.inl (Or.inl (h ▸ hy.2)), Or.inr (Or.inr rfl)⟩
    · rw [Finset.mem_singleton] at h
      exact hcon ⟨ξ, Or.inr ⟨y, hy.2, by rw [h]; abel⟩, Or.inr (Or.inr rfl)⟩

/-- For a nearest-neighbour interaction, `H_Λ(ω)` is a finite sum. -/
theorem energy_eq_sum {Φ : Interaction S} (hΦ : IsNearestNeighbour Φ) (Λ : Finset Plane)
    (ω : Config S) :
    energy Φ Λ ω = ∑ A ∈ nnSets Λ, {A : Finset Plane | (A ∩ Λ).Nonempty}.indicator
      (fun A => Φ A ω) A := by
  unfold energy
  refine (tsum_subtype {A : Finset Plane | (A ∩ Λ).Nonempty} (fun A => Φ A ω)).trans
    (tsum_eq_sum fun A hA => ?_)
  by_cases hm : (A ∩ Λ).Nonempty
  · rw [Set.indicator_of_mem (by exact hm)]
    by_contra h0
    exact hA (mem_nnSets hΦ hm h0)
  · exact Set.indicator_of_notMem (by exact hm) _

/-- **`H_Λ(ω) < ∞` at legal `ω`** (nearest-neighbour `Φ`; Section 2: "the sum defining `H_Λ` is
finite"). -/
theorem energy_lt_top_of_legal {Φ : Interaction S} (hΦ : IsNearestNeighbour Φ) (Λ : Finset Plane)
    {ω : Config S} (hω : IsLegal Φ ω) : energy Φ Λ ω < ⊤ := by
  rw [energy_eq_sum hΦ]
  refine ENNReal.sum_lt_top.2 fun A _ => ?_
  by_cases hm : (A ∩ Λ).Nonempty
  · rw [Set.indicator_of_mem (by exact hm)]; exact hω A
  · rw [Set.indicator_of_notMem (by exact hm)]; exact ENNReal.zero_lt_top

theorem boltzmann_nonneg (β : ℝ) (H : ℝ≥0∞) : 0 ≤ boltzmann β H := by
  unfold boltzmann; split_ifs <;> positivity

theorem boltzmann_pos {β : ℝ} {H : ℝ≥0∞} (h : H < ⊤) : 0 < boltzmann β H := by
  unfold boltzmann; rw [if_neg h.ne]; positivity

/-- **`Z_Λ(ω) > 0` at legal `ω`** (`set:def-gibbs`: `Z_Λ(ω) ≥ e^{-βH_Λ(ω)} > 0`). -/
theorem partitionFunction_pos {Φ : Interaction S} (hΦ : IsNearestNeighbour Φ) (β : ℝ)
    (Λ : Finset Plane) {ω : Config S} (hω : IsLegal Φ ω) : 0 < partitionFunction β Φ Λ ω := by
  unfold partitionFunction
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun ζ _ => boltzmann_nonneg β _)
    (Finset.mem_univ (fun x : Λ => ω x.1)))
  rw [fill_eq_fillOn, fillOn_self]
  exact boltzmann_pos (energy_lt_top_of_legal hΦ Λ hω)

/-- The Gibbs kernel `γ_Λ(· | ω) = ∑_ζ e^{-βH_Λ(ω^ζ)} / Z_Λ(ω) · δ_{ω^ζ}` as a measure (the zero
measure when `Z_Λ(ω) = 0`, which happens only at illegal `ω`). -/
def gibbsKernel (β : ℝ) (Φ : Interaction S) (Λ : Finset Plane) (ω : Config S) :
    Measure (Config S) :=
  ∑ ζ : Λ → S, ENNReal.ofReal (boltzmann β (energy Φ Λ (fill ω Λ ζ)) /
    partitionFunction β Φ Λ ω) • Measure.dirac (fill ω Λ ζ)

omit [MeasurableSpace S] [DiscreteMeasurableSpace S] in
theorem weight_div_nonneg (β : ℝ) (Φ : Interaction S) (Λ : Finset Plane) (ω : Config S)
    (ζ : Λ → S) :
    0 ≤ boltzmann β (energy Φ Λ (fill ω Λ ζ)) / partitionFunction β Φ Λ ω :=
  div_nonneg (boltzmann_nonneg _ _)
    (Finset.sum_nonneg fun _ _ => boltzmann_nonneg _ _)

/-- **`(γ_Λ F)(ω) = ∫ F dγ_Λ(· | ω)`**, for every `ω` and every `F`. -/
theorem kernelApply_eq_integral (β : ℝ) (Φ : Interaction S) (Λ : Finset Plane)
    (F : Config S → ℝ) (ω : Config S) :
    kernelApply β Φ Λ F ω = ∫ η, F η ∂(gibbsKernel β Φ Λ ω) := by
  unfold gibbsKernel
  rw [integral_finsetSum_measure (fun ζ _ => (integrable_dirac (by simp)).smul_measure
    ENNReal.ofReal_ne_top)]
  simp only [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal
    (weight_div_nonneg β Φ Λ ω _), smul_eq_mul]
  unfold kernelApply
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl fun ζ _ => by ring

/-- **`γ_Λ(· | ω)` is a probability measure** when `Z_Λ(ω) > 0`. -/
theorem isProbability_gibbsKernel (β : ℝ) (Φ : Interaction S) (Λ : Finset Plane) {ω : Config S}
    (hZ : 0 < partitionFunction β Φ Λ ω) : IsProbabilityMeasure (gibbsKernel β Φ Λ ω) := by
  constructor
  unfold gibbsKernel
  simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul,
    measure_univ, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun ζ _ => weight_div_nonneg β Φ Λ ω ζ), ← Finset.sum_div]
  unfold partitionFunction at hZ ⊢
  rw [div_self hZ.ne', ENNReal.ofReal_one]

/-- **`γ_Λ F` is measurable** for measurable `F`. -/
theorem measurable_kernelApply {Φ : Interaction S} (hΦ : IsInteraction Φ) (β : ℝ)
    (Λ : Finset Plane) {F : Config S → ℝ} (hF : Measurable F) :
    Measurable (kernelApply β Φ Λ F) := by
  have hb : Measurable (boltzmann β) := by
    unfold boltzmann
    exact Measurable.ite (measurableSet_singleton ⊤) measurable_const
      (Real.measurable_exp.comp (measurable_const.mul ENNReal.measurable_toReal).neg)
  have hw : Measurable (fun η : Config S => boltzmann β (energy Φ Λ η)) :=
    hb.comp (measurable_energy hΦ Λ)
  have hfill : ∀ ζ : Λ → S, Measurable (fun ω : Config S => fill ω Λ ζ) := fun ζ =>
    (measurable_fillOn Λ ζ).mono cylinderEvents_le_pi le_rfl
  unfold kernelApply partitionFunction
  exact (Finset.measurable_sum _ fun ζ _ => (hw.comp (hfill ζ)).mul (hF.comp (hfill ζ))).div
    (Finset.measurable_sum _ fun ζ _ => hw.comp (hfill ζ))

/-- **`γ_Λ F` is bounded** by any bound of `F`. -/
theorem abs_kernelApply_le (β : ℝ) (Φ : Interaction S) (Λ : Finset Plane) {F : Config S → ℝ}
    {C : ℝ} (hC : ∀ ω, |F ω| ≤ C) (ω : Config S) : |kernelApply β Φ Λ F ω| ≤ C := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC ω)
  unfold kernelApply
  set Z := partitionFunction β Φ Λ ω with hZdef
  have hZ0 : 0 ≤ Z := Finset.sum_nonneg fun _ _ => boltzmann_nonneg _ _
  rcases hZ0.eq_or_lt with h | h
  · rw [← h, div_zero, abs_zero]; exact hC0
  · rw [abs_div, abs_of_pos h, div_le_iff₀ h]
    calc |∑ ζ : Λ → S, boltzmann β (energy Φ Λ (fill ω Λ ζ)) * F (fill ω Λ ζ)|
        ≤ ∑ ζ : Λ → S, |boltzmann β (energy Φ Λ (fill ω Λ ζ)) * F (fill ω Λ ζ)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ ζ : Λ → S, boltzmann β (energy Φ Λ (fill ω Λ ζ)) * C := by
          refine Finset.sum_le_sum fun ζ _ => ?_
          rw [abs_mul, abs_of_nonneg (boltzmann_nonneg _ _)]
          exact mul_le_mul_of_nonneg_left (hC _) (boltzmann_nonneg _ _)
      _ = C * Z := by rw [← Finset.sum_mul, hZdef, partitionFunction, mul_comm]

end Gibbs

/-! ## Sanity of the `H2` vocabulary -/

namespace Ising

/-- `ℰ^b_Λ` ([FV, (3.2)]): the bond `(x, k)`, that is the edge `{x, x + e_k}`, is listed iff it
meets `Λ`. -/
theorem mem_bonds (Λ : Finset Plane) (x : Plane) (k : Bool) :
    (x, k) ∈ bonds Λ ↔ x ∈ Λ ∨ x + bondDir k ∈ Λ := by
  cases k <;>
    simp [bonds, bondDir, Finset.mem_product, sub_eq_iff_eq_add, eq_comm (a := x)]

end Ising

end UPD

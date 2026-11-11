/-
# Existence of Gibbs measures by compactness (`set:dobrushin`, existence; Step 4 of `thm:main`)

The paper (proof of `set:dobrushin`): "Existence holds because the spin space is compact and the
specification has finite range" ([gap] 4 of `STATUS.md`; not covered by `H1`, which is "at most
one"). Here, for a positive finite-range weight system on countably many coordinates with a finite
spin set:
* `integral_kernel`: `∫ F dγ_Λ(· | ω) = (γ_Λ F)(ω)` for bounded measurable `F`;
* `isDLR_of_isGibbsMeasure`: a measure compatible with the specification in the sense of `H1`
  ([FV, Definition 6.12]) satisfies the paper's DLR identity (the converse of
  `isGibbsMeasure_of_isDLR`), by integrating against the composition `γ_Λ ∘ μ = μ`;
* `exists_isDLR`: **a Gibbs measure exists**: a cluster point of the finite-volume measures
  `γ_Δ(· | ω₀)` as `Δ` grows (Mathlib's compactness of the probability measures on a compact space,
  `Prokhorov.lean`); the DLR identity holds along the net for local functions (`set:consistency`),
  passes to the limit because local functions are continuous, gives compatibility on cylinder
  events, hence on all events (π–λ), hence the DLR identity;
* `IsingGraph.exists_isDLR`, `IsingGraph.existsUnique_isDLR`: existence for every Ising model on a
  countable graph (Step 4 of `thm:main`), and **`set:dobrushin` in full** ("exactly one").
-/
import UndecidablePhaseDiagram.Gibbs.Dobrushin
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.Topology.ContinuousMap.Bounded.Basic

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BoundedContinuousFunction

namespace UPD

namespace Gibbs

namespace WeightSystem

variable {I E : Type} [DecidableEq I] [Fintype E] [DecidableEq E] [MeasurableSpace E]
  [DiscreteMeasurableSpace E] (ws : WeightSystem I E)

omit [DecidableEq E] [DiscreteMeasurableSpace E] in
/-- `∫ F dγ_Λ(· | ω) = (γ_Λ F)(ω)` for bounded measurable `F`. -/
theorem integral_kernel (Λ : Finset I) (ω : I → E) {F : (I → E) → ℝ} (hF : Measurable F)
    (hb : ∃ C : ℝ, ∀ η, |F η| ≤ C) : ∫ η, F η ∂(ws.kernel Λ ω) = ws.expect Λ ω F := by
  obtain ⟨C, hC⟩ := hb
  have hint : ∀ ζ : Λ → E, Integrable F
      (ENNReal.ofReal (ws.prob Λ ω ζ) • Measure.dirac (fillOn ω Λ ζ)) := fun ζ =>
    (Integrable.of_bound hF.aestronglyMeasurable C
      (ae_of_all _ fun η => by rw [Real.norm_eq_abs]; exact hC η)).smul_measure
      ENNReal.ofReal_ne_top
  unfold kernel expect
  rw [integral_finsetSum_measure fun ζ _ => hint ζ]
  refine Finset.sum_congr rfl fun ζ _ => ?_
  rw [integral_smul_measure, integral_dirac' F _ hF.stronglyMeasurable,
    ENNReal.toReal_ofReal (ws.prob_nonneg _ _ _), smul_eq_mul]

/-- The kernels `γ_Λ` as a Markov kernel. -/
def markovKernel (Λ : Finset I) : Kernel (I → E) (I → E) where
  toFun := ws.kernel Λ
  measurable' := Measure.measurable_of_measurable_coe _ fun A hA =>
    (ws.toSpecification.measurable Λ A hA).mono cylinderEvents_le_pi le_rfl

theorem markovKernel_apply (Λ : Finset I) (ω : I → E) : ws.markovKernel Λ ω = ws.kernel Λ ω :=
  rfl

instance (Λ : Finset I) : IsMarkovKernel (ws.markovKernel Λ) :=
  ⟨fun ω => ws.isProbability_kernel Λ ω⟩

/-- **Compatible measures satisfy the paper's DLR identity** (the converse of
`isGibbsMeasure_of_isDLR`). -/
theorem isDLR_of_isGibbsMeasure {μ : Measure (I → E)} (h : ws.toSpecification.IsGibbsMeasure μ) :
    ws.IsDLR μ := by
  obtain ⟨hμ, hc⟩ := h
  refine ⟨hμ, fun Λ F hF ⟨C, hC⟩ => ?_⟩
  have hbind : ws.markovKernel Λ ∘ₘ μ = μ := by
    ext A hA
    rw [Measure.bind_apply hA (ws.markovKernel Λ).aemeasurable]
    exact hc Λ A hA
  have hint : Integrable F (ws.markovKernel Λ ∘ₘ μ) := by
    rw [hbind]
    exact Integrable.of_bound hF.aestronglyMeasurable C
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hC ω)
  calc ∫ ω, F ω ∂μ = ∫ ω, F ω ∂(ws.markovKernel Λ ∘ₘ μ) := by rw [hbind]
    _ = ∫ ω, ∫ η, F η ∂(ws.markovKernel Λ ω) ∂μ := by
        rw [Measure.comp_eq_comp_const_apply] at hint ⊢
        rw [Kernel.integral_comp hint, Kernel.const_apply]
    _ = ∫ ω, ws.expect Λ ω F ∂μ := by
        refine integral_congr_ae (ae_of_all _ fun ω => ?_)
        exact ws.integral_kernel Λ ω hF ⟨C, hC⟩

omit [DecidableEq E] [MeasurableSpace E] [DiscreteMeasurableSpace E] in
/-- `γ_Λ F` depends only on the coordinates in `range Λ ∪ D` if `F` depends only on those in
`D`. -/
theorem expect_dependsOn (Λ : Finset I) {D : Finset I} {F : (I → E) → ℝ}
    (hF : ∀ ω ω' : I → E, (∀ i ∈ D, ω i = ω' i) → F ω = F ω') :
    ∀ ω ω' : I → E, (∀ i ∈ ws.range Λ ∪ D, ω i = ω' i) →
      ws.expect Λ ω F = ws.expect Λ ω' F := by
  intro ω ω' h
  have hfill : ∀ ζ : Λ → E, ∀ i ∈ ws.range Λ ∪ D, fillOn ω Λ ζ i = fillOn ω' Λ ζ i :=
    fun ζ => fillOn_agree_on h ζ
  have hW : ∀ ζ : Λ → E, ws.W Λ (fillOn ω Λ ζ) = ws.W Λ (fillOn ω' Λ ζ) := fun ζ =>
    ws.isLocal Λ _ _ (fun i hi => hfill ζ i (Finset.mem_union_left _ hi))
  have hFe : ∀ ζ : Λ → E, F (fillOn ω Λ ζ) = F (fillOn ω' Λ ζ) := fun ζ =>
    hF _ _ (fun i hi => hfill ζ i (Finset.mem_union_right _ hi))
  have hZ : ws.Z Λ ω = ws.Z Λ ω' := by simp only [Z, hW]
  simp only [expect, prob, hW, hZ, hFe]

omit [DecidableEq E] in
/-- From the DLR identity for the indicator of `A` to compatibility for `A` (as in
`isGibbsMeasure_of_isDLR`). -/
theorem lintegral_kernel_eq {μ : Measure (I → E)} [IsProbabilityMeasure μ] (Λ : Finset I)
    {A : Set (I → E)} (hA : MeasurableSet A)
    (h : ∫ ω, A.indicator 1 ω ∂μ = ∫ ω, ws.expect Λ ω (A.indicator 1) ∂μ) :
    ∫⁻ ω, ws.kernel Λ ω A ∂μ = μ A := by
  have hF : Measurable (A.indicator (1 : (I → E) → ℝ)) := measurable_const.indicator hA
  have hk : ∀ ω, ws.kernel Λ ω A = ENNReal.ofReal (ws.expect Λ ω (A.indicator 1)) := fun ω =>
    ws.kernel_apply Λ ω hA
  have hle : ∀ ω, ws.expect Λ ω (A.indicator 1) ≤ 1 := fun ω => by
    have := ws.isProbability_kernel Λ ω
    have h2 : ws.kernel Λ ω A ≤ 1 := prob_le_one
    rw [ws.kernel_apply Λ ω hA] at h2
    exact (ENNReal.ofReal_le_one).1 h2
  have hnn : ∀ ω, 0 ≤ ws.expect Λ ω (A.indicator 1) := fun ω =>
    ws.expect_nonneg _ _ (indicator_one_nonneg A)
  have hmeas := ws.measurable_expect' Λ hF
  have hL : (∫⁻ ω, ws.kernel Λ ω A ∂μ).toReal = ∫ ω, ws.expect Λ ω (A.indicator 1) ∂μ := by
    simp only [hk]
    rw [← integral_toReal hmeas.ennreal_ofReal.aemeasurable
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    simp only [ENNReal.toReal_ofReal (hnn _)]
  have hR : (μ A).toReal = ∫ ω, A.indicator (1 : (I → E) → ℝ) ω ∂μ := by
    rw [integral_indicator_one hA, measureReal_def]
  have hfin : ∫⁻ ω, ws.kernel Λ ω A ∂μ ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := ∫⁻ _, 1 ∂μ) (by simp) (lintegral_mono fun ω => ?_)
    rw [hk]; exact ENNReal.ofReal_le_one.2 (hle ω)
  rw [← ENNReal.toReal_eq_toReal_iff' hfin (measure_ne_top μ A), hL, hR, h]

section Existence

variable [TopologicalSpace E] [DiscreteTopology E] [BorelSpace E] [Countable I]

omit [Fintype E] [DecidableEq E] [MeasurableSpace E] [DiscreteMeasurableSpace E] [BorelSpace E]
  [Countable I] in
/-- A function of finitely many coordinates is continuous (finite discrete spin set). -/
theorem continuous_of_dependsOn (D : Finset I) (f : (I → E) → ℝ)
    (hf : ∀ ω ω' : I → E, (∀ i ∈ D, ω i = ω' i) → f ω = f ω') : Continuous f := by
  rcases isEmpty_or_nonempty (I → E) with h | ⟨⟨ω₀⟩⟩
  · exact ⟨fun s _ => by rw [Set.eq_empty_of_isEmpty (f ⁻¹' s)]; exact isOpen_empty⟩
  · have hfac : f = (fun ζ : D → E => f (fillOn ω₀ D ζ)) ∘ (fun ω (x : D) => ω x.1) := by
      funext ω
      exact hf _ _ fun i hi => (fillOn_of_mem ω₀ (fun x : D => ω x.1) hi).symm
    rw [hfac]
    exact continuous_of_discreteTopology.comp (continuous_pi fun x => continuous_apply x.1)

/-- The finite-volume Gibbs measure `γ_Δ(· | ω₀)` as a point of the space of probability
measures. -/
def fvMeasure (ω₀ : I → E) (Δ : Finset I) : ProbabilityMeasure (I → E) :=
  ⟨ws.kernel Δ ω₀, ws.isProbability_kernel Δ ω₀⟩

/-- **Existence of a Gibbs measure** for a positive finite-range weight system on countably many
coordinates with a finite spin set. -/
theorem exists_isDLR [Nonempty E] : ∃ μ : Measure (I → E), ws.IsDLR μ := by
  obtain ⟨e⟩ := (inferInstance : Nonempty E)
  let ω₀ : I → E := fun _ => e
  obtain ⟨ν, hν⟩ := exists_clusterPt_of_compactSpace (Filter.map (ws.fvMeasure ω₀) atTop)
  -- the DLR identity for local functions
  have hloc : ∀ (Λ D : Finset I) (F : (I → E) → ℝ),
      (∀ ω ω' : I → E, (∀ i ∈ D, ω i = ω' i) → F ω = F ω') →
      ∫ ω, F ω ∂(ν : Measure (I → E)) = ∫ ω, ws.expect Λ ω F ∂(ν : Measure (I → E)) := by
    intro Λ D F hF
    have hF₂ := ws.expect_dependsOn Λ hF
    let G₁ : (I → E) →ᵇ ℝ :=
      BoundedContinuousFunction.mkOfCompact ⟨F, continuous_of_dependsOn D F hF⟩
    let G₂ : (I → E) →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact
      ⟨fun ω => ws.expect Λ ω F, continuous_of_dependsOn _ _ hF₂⟩
    have hFm : Measurable F := measurable_of_dependsOn D F hF
    have hF₂m : Measurable (fun ω => ws.expect Λ ω F) := measurable_of_dependsOn _ _ hF₂
    have hFb : ∃ C : ℝ, ∀ η, |F η| ≤ C :=
      ⟨‖G₁‖, fun η => by rw [← Real.norm_eq_abs]; exact G₁.norm_coe_le_norm η⟩
    have hF₂b : ∃ C : ℝ, ∀ η, |ws.expect Λ η F| ≤ C :=
      ⟨‖G₂‖, fun η => by rw [← Real.norm_eq_abs]; exact G₂.norm_coe_le_norm η⟩
    set S : Set (ProbabilityMeasure (I → E)) :=
      {μ | ∫ ω, G₁ ω ∂(μ : Measure (I → E)) = ∫ ω, G₂ ω ∂(μ : Measure (I → E))} with hS
    have hclosed : IsClosed S :=
      isClosed_eq (ProbabilityMeasure.continuous_integral_boundedContinuousFunction G₁)
        (ProbabilityMeasure.continuous_integral_boundedContinuousFunction G₂)
    have hev : S ∈ Filter.map (ws.fvMeasure ω₀) atTop := by
      rw [Filter.mem_map]
      filter_upwards [Filter.eventually_ge_atTop Λ] with Δ hΔ
      show ∫ ω, F ω ∂(ws.kernel Δ ω₀) = ∫ ω, ws.expect Λ ω F ∂(ws.kernel Δ ω₀)
      rw [ws.integral_kernel Δ ω₀ hFm hFb, ws.integral_kernel Δ ω₀ hF₂m hF₂b]
      exact (ws.expect_expect hΔ ω₀ F).symm
    have hmem := clusterPt_iff_forall_mem_closure.1 hν S hev
    rw [hclosed.closure_eq] at hmem
    exact hmem
  -- compatibility on cylinder events, then on all events
  have hcomp : ∀ Λ : Finset I, ws.markovKernel Λ ∘ₘ (ν : Measure (I → E)) = ν := by
    intro Λ
    refine ext_of_generate_finite (measurableCylinders fun _ : I => E)
      generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders (fun A hA => ?_)
      (by simp [measure_univ])
    have hAm : MeasurableSet A := MeasurableSet.of_mem_measurableCylinders hA
    obtain ⟨s, S, -, hAeq⟩ := (mem_measurableCylinders _).1 hA
    rw [Measure.bind_apply hAm (ws.markovKernel Λ).aemeasurable]
    refine ws.lintegral_kernel_eq Λ hAm (hloc Λ s _ fun ω ω' h => ?_)
    have hr : s.restrict ω = s.restrict ω' := funext fun i => h i i.2
    subst hAeq
    have hiff : ω ∈ cylinder s S ↔ ω' ∈ cylinder s S := by
      rw [mem_cylinder, mem_cylinder, hr]
    by_cases hω : ω ∈ cylinder s S
    · simp [Set.indicator, hω, hiff.1 hω]
    · simp [Set.indicator, hω, mt hiff.2 hω]
  refine ⟨ν, ws.isDLR_of_isGibbsMeasure ⟨inferInstance, fun Λ A hA => ?_⟩⟩
  have h := congrArg (fun m : Measure (I → E) => m A) (hcomp Λ)
  rw [Measure.bind_apply hA (ws.markovKernel Λ).aemeasurable] at h
  exact h

end Existence

end WeightSystem

/-! ## Ising models: existence, and `set:dobrushin` in full -/

/-- The discrete topology on the two spin values. -/
instance : TopologicalSpace Spin := ⊥

instance : DiscreteTopology Spin := ⟨rfl⟩

instance : BorelSpace Spin := ⟨borel_eq_top_of_discrete.symm⟩

instance : Nonempty Spin := ⟨.plus⟩

namespace IsingGraph

variable {V : Type} [DecidableEq V] [Countable V] (G : IsingGraph V)

/-- **Existence of a Gibbs measure** for every Ising model on a countable graph (Step 4 of
`thm:main`; the existence half of `set:dobrushin`). -/
theorem exists_isDLR : ∃ μ : Measure (V → Spin), G.toWeightSystem.IsDLR μ :=
  G.toWeightSystem.exists_isDLR

/-- **`set:dobrushin`** ("exactly one Gibbs measure"), from `H1` and compactness. -/
theorem existsUnique_isDLR (h1 : H1) (Jbar : ℝ) (hJ : ∀ e, G.J e ≤ Jbar)
    (hdeg : ∀ i, (G.nbr i).card ≤ 4) (htanh : 4 * Real.tanh Jbar < 1) :
    ∃! μ : Measure (V → Spin), G.toWeightSystem.IsDLR μ := by
  obtain ⟨μ, hμ⟩ := G.exists_isDLR
  exact ⟨μ, hμ, fun ν hν => G.dobrushin_unique h1 Jbar hJ hdeg htanh hν hμ⟩

end IsingGraph

end Gibbs

end UPD

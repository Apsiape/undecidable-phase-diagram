/-
# The plus and minus states (`set:peierls`)

Printed statement (`set:peierls`): "For every `J ≥ 0`, the Ising model on `ℤ²` with coupling `J`
has Gibbs measures `ν⁺` and `ν⁻`, the plus and minus states (the weak limits of the finite-volume
measures with plus and minus boundary conditions), invariant under all translations of `ℤ²` and
exchanged by the global spin flip. If `e^J ≥ 3`, then `ν⁺(σ₀ = -1) ≤ 1/3` and
`ν⁻(σ₀ = +1) ≤ 1/3`; in particular `ν⁺ ≠ ν⁻`."

Proof here: the plus state is `H2`'s measure (existence of the limit, independence of the
sequence, translation invariance and the Gibbs property are `H2`, quoting [FV, Theorem 3.17,
Theorem 6.5, Example 6.51, Lemma 6.65]); the minus state is its image under the global spin flip,
and its properties follow from the flip invariance of the finite-volume measures
(`expect_flip`: `⟨F ∘ flip⟩^η_Λ = ⟨F⟩^{flip η}_Λ`; [gap] 5 of `STATUS.md`). The bound passes to the
limit along the boxes `B(n)` from `plus_prob_minus_le`.
-/
import UndecidablePhaseDiagram.Peierls.Contour
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology

namespace UPD

namespace Peierls

open Ising

/-! ## The global spin flip -/

/-- [FV, Section 3.1]: the `-` boundary condition, `η⁻_i = -1` for all `i`. -/
def minusConfig : Config Spin := fun _ => .minus

/-- The global spin flip `σ ↦ -σ`. -/
def flipConfig (σ : Config Spin) : Config Spin := fun x => flipSpin (σ x)

theorem flipSpin_flipSpin (s : Spin) : flipSpin (flipSpin s) = s := by cases s <;> rfl

theorem flipConfig_flipConfig (σ : Config Spin) : flipConfig (flipConfig σ) = σ :=
  funext fun x => flipSpin_flipSpin (σ x)

theorem flipConfig_plusConfig : flipConfig plusConfig = minusConfig := rfl

theorem flipConfig_minusConfig : flipConfig minusConfig = plusConfig := rfl

theorem measurable_flipConfig : Measurable flipConfig :=
  Measurable.of_eval fun x => (Measurable.of_discrete (f := flipSpin)).comp
    (measurable_pi_apply x)

/-- The global spin flip as a measurable involution. -/
def flipEquiv : Config Spin ≃ᵐ Config Spin where
  toFun := flipConfig
  invFun := flipConfig
  left_inv := flipConfig_flipConfig
  right_inv := flipConfig_flipConfig
  measurable_toFun := measurable_flipConfig
  measurable_invFun := measurable_flipConfig

theorem coe_flipEquiv : (flipEquiv : Config Spin → Config Spin) = flipConfig := rfl

theorem measurable_shift (a : Plane) : Measurable (shift (S := Spin) a) :=
  Measurable.of_eval fun x => measurable_pi_apply (x - a)

theorem val_flipSpin (s : Spin) : val (flipSpin s) = -val s := by
  cases s <;> simp [val, flipSpin]

/-- The Boltzmann weight is invariant under the global flip. -/
theorem weight_flipConfig (J : ℝ) (Λ : Finset Plane) (σ : Config Spin) :
    weight J Λ (flipConfig σ) = weight J Λ σ := by
  unfold weight
  congr 2
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [flipConfig, val_flipSpin, neg_mul_neg]

theorem flipConfig_fill (η : Config Spin) (Λ : Finset Plane) (ζ : Λ → Spin) :
    flipConfig (fill η Λ ζ) = fill (flipConfig η) Λ (fun x => flipSpin (ζ x)) := by
  funext x
  simp only [flipConfig, fill]
  split_ifs <;> rfl

/-- **Flip invariance of the finite-volume measures** ([gap] 5): `⟨F ∘ flip⟩^η_Λ = ⟨F⟩^{flip η}_Λ`. -/
theorem expect_flip (J : ℝ) (Λ : Finset Plane) (η : Config Spin) (F : Config Spin → ℝ) :
    expect J Λ η (fun σ => F (flipConfig σ)) = expect J Λ (flipConfig η) F := by
  let e : (Λ → Spin) ≃ (Λ → Spin) :=
    ⟨fun ζ x => flipSpin (ζ x), fun ζ x => flipSpin (ζ x),
      fun ζ => funext fun x => flipSpin_flipSpin _, fun ζ => funext fun x => flipSpin_flipSpin _⟩
  have h : ∀ ζ, fill (flipConfig η) Λ (e ζ) = flipConfig (fill η Λ ζ) := fun ζ =>
    (flipConfig_fill η Λ ζ).symm
  unfold expect
  congr 1
  · exact Fintype.sum_equiv e _ _ fun ζ => by rw [h, weight_flipConfig]
  · exact Fintype.sum_equiv e _ _ fun ζ => by rw [h, weight_flipConfig]

/-! ## States of the Ising model on `ℤ²` -/

/-- `ν` is a Gibbs measure of the Ising model on `ℤ²` with coupling `J`: a probability measure
satisfying the DLR identity of the Ising specification for every finite `Λ` and every bounded
measurable `F` (the form of `H2`(3)). -/
def IsIsingGibbs (J : ℝ) (ν : Measure (Config Spin)) : Prop :=
  IsProbabilityMeasure ν ∧ ∀ (Λ : Finset Plane) (F : Config Spin → ℝ), Measurable F →
    (∃ C : ℝ, ∀ ω, |F ω| ≤ C) → ∫ ω, F ω ∂ν = ∫ ω, expect J Λ ω F ∂ν

/-- `ν` is the weak limit of the finite-volume measures with boundary condition `η`, along every
increasing sequence of finite sets invading `ℤ²` (the form of `H2`(1)). -/
def IsLimitState (J : ℝ) (η : Config Spin) (ν : Measure (Config Spin)) : Prop :=
  ∀ Λs : ℕ → Finset Plane, Monotone Λs → (∀ x : Plane, ∃ n, x ∈ Λs n) →
    ∀ f : Config Spin → ℝ, IsLocal f →
      Tendsto (fun n => expect J (Λs n) η f) atTop (𝓝 (∫ ω, f ω ∂ν))

/-- The plus state, from `H2`. -/
theorem exists_plus_state (h2 : H2) {J : ℝ} (hJ : 0 ≤ J) :
    ∃ ν : Measure (Config Spin), IsIsingGibbs J ν ∧ IsLimitState J plusConfig ν ∧
      IsTranslationInvariantMeasure ν := by
  obtain ⟨ν, hP, hlim, hTI, hDLR⟩ := h2 J hJ
  exact ⟨ν, ⟨hP, hDLR⟩, hlim, hTI⟩

theorem isProbabilityMeasure_map_flip {ν : Measure (Config Spin)} [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (ν.map flipConfig) :=
  (Measure.isProbabilityMeasure_map_iff measurable_flipConfig.aemeasurable).2 inferInstance

/-- The flip image of a Gibbs measure is a Gibbs measure. -/
theorem IsIsingGibbs.map_flip {J : ℝ} {ν : Measure (Config Spin)} (h : IsIsingGibbs J ν) :
    IsIsingGibbs J (ν.map flipConfig) := by
  haveI := h.1
  refine ⟨isProbabilityMeasure_map_flip, fun Λ F hF ⟨C, hC⟩ => ?_⟩
  rw [← coe_flipEquiv, integral_map_equiv, integral_map_equiv, coe_flipEquiv]
  rw [h.2 Λ (fun σ => F (flipConfig σ)) (hF.comp measurable_flipConfig) ⟨C, fun ω => hC _⟩]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  simp only
  rw [expect_flip]

/-- The flip image of a limit state with boundary condition `η` is the limit state with boundary
condition `flip η`. -/
theorem IsLimitState.map_flip {J : ℝ} {η : Config Spin} {ν : Measure (Config Spin)}
    (h : IsLimitState J η ν) : IsLimitState J (flipConfig η) (ν.map flipConfig) := by
  intro Λs hmono hinv f ⟨Δ, hΔ⟩
  have hloc : IsLocal (fun σ => f (flipConfig σ)) :=
    ⟨Δ, fun ω ω' hω => hΔ _ _ fun i hi => by simp only [flipConfig, hω i hi]⟩
  have := h Λs hmono hinv _ hloc
  rw [← coe_flipEquiv, integral_map_equiv, coe_flipEquiv]
  simp only [← expect_flip]
  exact this

/-- The flip image of a translation-invariant measure is translation invariant. -/
theorem isTranslationInvariant_map_flip {ν : Measure (Config Spin)}
    (h : IsTranslationInvariantMeasure ν) : IsTranslationInvariantMeasure (ν.map flipConfig) := by
  intro a
  rw [Measure.map_map (measurable_shift a) measurable_flipConfig]
  have hc : shift a ∘ flipConfig = flipConfig ∘ shift a := rfl
  rw [hc, ← Measure.map_map measurable_flipConfig (measurable_shift a), h a]

/-! ## The bound in the limit -/

theorem box_mono : Monotone box := by
  intro n m hnm x hx
  rw [mem_box] at hx ⊢
  have : (n : ℤ) ≤ m := by exact_mod_cast hnm
  exact ⟨hx.1.trans this, hx.2.trans this⟩

theorem exists_mem_box (x : Plane) : ∃ n, x ∈ box n := by
  refine ⟨(|x.1| + |x.2|).toNat, ?_⟩
  rw [mem_box]
  have h1 := abs_nonneg x.1
  have h2 := abs_nonneg x.2
  constructor <;> omega

theorem measurableSet_spin_eq (s : Spin) : MeasurableSet {σ : Config Spin | σ 0 = s} := by
  have hs : MeasurableSet ({s} : Set Spin) := MeasurableSet.of_discrete
  have hm : Measurable (fun σ : Config Spin => σ 0) := measurable_pi_apply _
  exact hm hs

theorem isLocal_indicator_spin (s : Spin) :
    IsLocal ({σ : Config Spin | σ 0 = s}.indicator 1) :=
  ⟨{0}, fun ω ω' h => by
    have h0 : ω 0 = ω' 0 := h 0 (Finset.mem_singleton_self _)
    simp only [Set.indicator, Set.mem_setOf_eq, h0, Pi.one_apply]⟩

/-- **Peierls' bound for the plus state**: `ν⁺(σ₀ = -1) ≤ 1296/4225` if `e^J ≥ 3`. -/
theorem plus_state_bound {J : ℝ} (hJ : 3 ≤ Real.exp J) {ν : Measure (Config Spin)}
    (h : IsLimitState J plusConfig ν) : ν.real {σ : Config Spin | σ 0 = .minus} ≤ 1296 / 4225 := by
  have ht := h box box_mono exists_mem_box _ (isLocal_indicator_spin .minus)
  rw [integral_indicator_one (measurableSet_spin_eq .minus)] at ht
  exact le_of_tendsto' ht fun n => plus_prob_minus_le hJ n

theorem preimage_flip_spin (s : Spin) :
    flipConfig ⁻¹' {σ : Config Spin | σ 0 = s} = {σ : Config Spin | σ 0 = flipSpin s} := by
  ext σ
  simp only [Set.mem_preimage, Set.mem_setOf_eq, flipConfig]
  constructor
  · intro h; rw [← h, flipSpin_flipSpin]
  · intro h; rw [h, flipSpin_flipSpin]

/-- **`set:peierls`.** For every `J ≥ 0` there are Gibbs measures `ν⁺`, `ν⁻` of the Ising model on
`ℤ²` with coupling `J`, the limits of the finite-volume measures with plus and minus boundary
condition along every increasing sequence of finite sets invading `ℤ²`, invariant under all
translations, exchanged by the global spin flip; if `e^J ≥ 3`, then `ν⁺(σ₀ = -1) ≤ 1/3`,
`ν⁻(σ₀ = +1) ≤ 1/3` and `ν⁺ ≠ ν⁻`. -/
theorem peierls (h2 : H2) {J : ℝ} (hJ : 0 ≤ J) :
    ∃ νp νm : Measure (Config Spin),
      IsIsingGibbs J νp ∧ IsIsingGibbs J νm ∧
      IsLimitState J plusConfig νp ∧ IsLimitState J minusConfig νm ∧
      IsTranslationInvariantMeasure νp ∧ IsTranslationInvariantMeasure νm ∧
      νm = νp.map flipConfig ∧ νp = νm.map flipConfig ∧
      (3 ≤ Real.exp J → νp.real {σ : Config Spin | σ 0 = .minus} ≤ 1 / 3 ∧
        νm.real {σ : Config Spin | σ 0 = .plus} ≤ 1 / 3 ∧ νp ≠ νm) := by
  obtain ⟨ν, hG, hlim, hTI⟩ := exists_plus_state h2 hJ
  haveI := hG.1
  have hback : (ν.map flipConfig).map flipConfig = ν := by
    rw [Measure.map_map measurable_flipConfig measurable_flipConfig]
    have : flipConfig ∘ flipConfig = id := funext flipConfig_flipConfig
    rw [this, Measure.map_id]
  refine ⟨ν, ν.map flipConfig, hG, hG.map_flip, hlim, ?_, hTI, isTranslationInvariant_map_flip hTI,
    rfl, hback.symm, fun h3 => ?_⟩
  · have := hlim.map_flip
    rwa [flipConfig_plusConfig] at this
  have hp := plus_state_bound h3 hlim
  have hm : (ν.map flipConfig).real {σ : Config Spin | σ 0 = .plus} =
      ν.real {σ : Config Spin | σ 0 = .minus} := by
    rw [measureReal_def, Measure.map_apply measurable_flipConfig (measurableSet_spin_eq _),
      preimage_flip_spin]
    rfl
  have hb : (1296 : ℝ) / 4225 ≤ 1 / 3 := by norm_num
  refine ⟨hp.trans hb, hm ▸ hp.trans hb, fun heq => ?_⟩
  -- `ν⁺(σ₀ = +1) = 1 - ν⁺(σ₀ = -1) ≥ 2/3`, while `ν⁻(σ₀ = +1) ≤ 1/3`
  have hcompl : {σ : Config Spin | σ 0 = .plus} = {σ : Config Spin | σ 0 = .minus}ᶜ := by
    ext σ
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff]
    cases σ 0 <;> simp
  have h1 : ν.real {σ : Config Spin | σ 0 = .plus} = 1 - ν.real {σ : Config Spin | σ 0 = .minus} := by
    rw [hcompl, probReal_compl_eq_one_sub (measurableSet_spin_eq _)]
  have h2' : ν.real {σ : Config Spin | σ 0 = .plus} ≤ 1296 / 4225 := by
    rw [heq, hm]; exact hp
  linarith

end Peierls

end UPD

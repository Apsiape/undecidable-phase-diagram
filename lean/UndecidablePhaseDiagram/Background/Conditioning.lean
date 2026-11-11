/-
# Section 5.4: conditioning on the background (`lem:freeze`(b), (c))

New in this project. QB's ruling on G.5 (1): `Config (SiteVal U)` is the only configuration
space; "`μ^𝔟` is Gibbs for `γ^𝔟`" is read as "`μ^𝔟`, concentrated on the background `𝔟`, is Gibbs
for `βΦ`"; `lem:freeze`(c) is proved by disintegrating over the phase `τ(ω)` (`phaseMap`) with
`Measure.condKernel`, the background being the measurable function `τ ↦ 𝔟_τ` of the phase.

* `gibbsK β Λ`: the Gibbs kernels `γ_Λ(· | ω)` as a kernel; `lintegral_gibbsK`: a Gibbs measure
  is compatible (`∫ γ_Λ(B | ω) dμ = μ(B)`).
* **`freeze_a_product`** (`lem:freeze`(a), product form): at `ω = (𝔟, p) ∈ X_typ`,
  `γ_Λ(· | ω) = δ_𝔟 ⊗ γ^𝔟_Λ(· | p)`, with the frozen kernel `frozenApply` on payload
  configurations (sums over the payload fillings `compatFill` compatible with `𝔟`; `assemble` is
  `(𝔟, p) ↦ ω`); `sum_fill_eq` reindexes the fillings of `Λ`.
* **`freeze_b`** (`lem:freeze`(b)): at `ω ∈ X_typ` the kernel charges only configurations with the
  same quarters, hence the same phase and background (`quarters_fill`, `gibbsK_inter`); two
  configurations of `X_typ` that agree off `Λ` have the same phase and background.
* `condLaw μ`: the conditional laws `μ^τ` of `μ` given the phase (`Measure.condKernel` of the
  joint law of `(τ(ω), ω)`); `disintegration`: `μ = ∫ μ^τ (μ ∘ τ⁻¹)(dτ)`.
* **`freeze_c`** (`lem:freeze`(c)): if `μ` is Gibbs for `βΦ` and concentrated on `X_typ`, then for
  almost every `τ` the conditional law `μ^τ` is Gibbs for `βΦ`, concentrated on `{τ(ω) = τ}`, so
  (`τ` being typical) on the legal configurations with background `𝔟_τ`; conversely
  (`isGibbs_comp`) every mixture of Gibbs measures is Gibbs.
-/
import UndecidablePhaseDiagram.Background.BgMap
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.Disintegration.Unique
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace UPD.BG

open UPD.Scaffold

variable {U : Machine}

/-! ## The Gibbs kernels as a kernel -/

section Kernel

variable (β : ℝ)

theorem gibbsKernel_apply (Λ : Finset Plane) (ω : Config (SiteVal U)) (B : Set (Config (SiteVal U))) :
    Gibbs.gibbsKernel β (Phi U) Λ ω B = ∑ ζ : Λ → SiteVal U,
      ENNReal.ofReal (boltzmann β (energy (Phi U) Λ (fill ω Λ ζ)) /
        partitionFunction β (Phi U) Λ ω) * B.indicator 1 (fill ω Λ ζ) := by
  simp only [Gibbs.gibbsKernel, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    Measure.dirac_apply, smul_eq_mul]

theorem gibbsKernel_univ_le (Λ : Finset Plane) (ω : Config (SiteVal U)) :
    Gibbs.gibbsKernel β (Phi U) Λ ω Set.univ ≤ 1 := by
  rw [gibbsKernel_apply]
  simp only [Set.indicator_univ, Pi.one_apply, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun ζ _ => Gibbs.weight_div_nonneg β (Phi U) Λ ω ζ),
    ← Finset.sum_div]
  refine ENNReal.ofReal_le_one.2 ?_
  unfold partitionFunction
  rcases (Finset.sum_nonneg fun ζ _ => Gibbs.boltzmann_nonneg β
    (energy (Phi U) Λ (fill ω Λ ζ)) : 0 ≤ ∑ ζ : Λ → SiteVal U,
      boltzmann β (energy (Phi U) Λ (fill ω Λ ζ))).eq_or_lt with h | h
  · rw [← h, div_zero]; norm_num
  · rw [div_self h.ne']

theorem gibbsKernel_le_one (Λ : Finset Plane) (ω : Config (SiteVal U)) (B : Set (Config (SiteVal U))) :
    Gibbs.gibbsKernel β (Phi U) Λ ω B ≤ 1 :=
  (measure_mono (Set.subset_univ B)).trans (gibbsKernel_univ_le β Λ ω)

theorem measurable_gibbsKernel_apply (Λ : Finset Plane) {B : Set (Config (SiteVal U))}
    (hB : MeasurableSet B) : Measurable fun ω => Gibbs.gibbsKernel β (Phi U) Λ ω B := by
  have hb : Measurable (boltzmann β) := by
    unfold boltzmann
    exact Measurable.ite (measurableSet_singleton ⊤) measurable_const
      (Real.measurable_exp.comp (measurable_const.mul ENNReal.measurable_toReal).neg)
  have hw : Measurable (fun η : Config (SiteVal U) => boltzmann β (energy (Phi U) Λ η)) :=
    hb.comp (Gibbs.measurable_energy phi_isInteraction Λ)
  have hfill : ∀ ζ : Λ → SiteVal U, Measurable (fun ω : Config (SiteVal U) => fill ω Λ ζ) :=
    fun ζ => (Gibbs.measurable_fillOn Λ ζ).mono cylinderEvents_le_pi le_rfl
  have hZ : Measurable (fun ω : Config (SiteVal U) => partitionFunction β (Phi U) Λ ω) := by
    unfold partitionFunction
    exact Finset.measurable_sum _ fun ζ _ => hw.comp (hfill ζ)
  simp only [gibbsKernel_apply]
  exact Finset.measurable_sum _ fun ζ _ =>
    (ENNReal.measurable_ofReal.comp ((hw.comp (hfill ζ)).div hZ)).mul
      ((measurable_one.indicator hB).comp (hfill ζ))

/-- The Gibbs kernels `γ_Λ(· | ω)` of `βΦ` as a kernel. -/
def gibbsK (Λ : Finset Plane) : Kernel (Config (SiteVal U)) (Config (SiteVal U)) where
  toFun := Gibbs.gibbsKernel β (Phi U) Λ
  measurable' := Measure.measurable_of_measurable_coe _ fun _ hB =>
    measurable_gibbsKernel_apply β Λ hB

theorem gibbsK_apply (Λ : Finset Plane) (ω : Config (SiteVal U)) :
    gibbsK (U := U) β Λ ω = Gibbs.gibbsKernel β (Phi U) Λ ω := rfl

instance (Λ : Finset Plane) : IsFiniteKernel (gibbsK (U := U) β Λ) :=
  ⟨⟨1, ENNReal.one_lt_top, fun ω => gibbsKernel_univ_le β Λ ω⟩⟩

/-- A Gibbs measure is compatible: `∫ γ_Λ(B | ω) dμ(ω) = μ(B)`. -/
theorem lintegral_gibbsK {μ : Measure (Config (SiteVal U))} (hμ : IsGibbs β (Phi U) μ)
    (Λ : Finset Plane) {B : Set (Config (SiteVal U))} (hB : MeasurableSet B) :
    ∫⁻ ω, gibbsK β Λ ω B ∂μ = μ B := by
  haveI := hμ.1
  have hF : Measurable (B.indicator (1 : Config (SiteVal U) → ℝ)) := measurable_const.indicator hB
  have hdlr := hμ.2.2 Λ _ hF ⟨1, fun ω => by
    by_cases h : ω ∈ B <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]⟩
  have hk : ∀ ω, kernelApply β (Phi U) Λ (B.indicator 1) ω = (gibbsK β Λ ω B).toReal := by
    intro ω
    rw [Gibbs.kernelApply_eq_integral, integral_indicator_one hB, measureReal_def]; rfl
  simp only [hk, integral_indicator_one hB, measureReal_def] at hdlr
  have hmeas : Measurable fun ω => gibbsK β Λ ω B := Kernel.measurable_coe _ hB
  have hfin : ∫⁻ ω, gibbsK β Λ ω B ∂μ ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := ∫⁻ _, 1 ∂μ) (by simp) (lintegral_mono fun ω => ?_)
    exact gibbsKernel_le_one β Λ ω B
  rw [← ENNReal.toReal_eq_toReal_iff' hfin (measure_ne_top μ B), hdlr,
    integral_toReal hmeas.aemeasurable (Filter.Eventually.of_forall fun ω =>
      (gibbsKernel_le_one β Λ ω B).trans_lt ENNReal.one_lt_top)]

end Kernel

/-! ## `lem:freeze`(b): the kernel keeps the quarters, the phase and the background -/

section Freeze

variable (β : ℝ)

/-- At `ω ∈ X_typ`, every configuration charged by `γ_Λ(· | ω)` has the quarters of `ω`. -/
theorem quarters_fill {ω : Config (SiteVal U)} {τ : ℕ → Bool × Bool} (hs : Setting ω τ)
    (Λ : Finset Plane) (ζ : Λ → SiteVal U)
    (hpos : boltzmann β (energy (Phi U) Λ (fill ω Λ ζ)) ≠ 0) :
    quartersOf (fill ω Λ ζ) = quartersOf ω := by
  have hagree : ∀ ξ, ξ ∉ Λ → fill ω Λ ζ ξ = ω ξ := fun ξ h => by simp [fill, h]
  have hE : energy (Phi U) Λ (fill ω Λ ζ) ≠ ⊤ := fun h => hpos (by simp [boltzmann, h])
  exact quarter_rigid (isQTiling_of_legal (legal_fill hs.legal hagree hE)) hs.phase
    hs.typical.1 Λ (fun ξ hξ => by simp only [quartersOf, hagree ξ hξ])

/-- At `ω ∈ X_typ`, `γ_Λ(· | ω)` is concentrated on the configurations with the quarters of `ω`. -/
theorem gibbsK_inter {ω : Config (SiteVal U)} {τ : ℕ → Bool × Bool} (hs : Setting ω τ)
    (Λ : Finset Plane) (B : Set (Config (SiteVal U))) :
    gibbsK β Λ ω B = gibbsK β Λ ω (B ∩ {η | quartersOf η = quartersOf ω}) := by
  simp only [gibbsK_apply, gibbsKernel_apply]
  refine Finset.sum_congr rfl fun ζ _ => ?_
  by_cases hw : boltzmann β (energy (Phi U) Λ (fill ω Λ ζ)) = 0
  · simp [hw]
  · have hq := quarters_fill β hs Λ ζ hw
    congr 1
    by_cases hB : fill ω Λ ζ ∈ B
    · rw [Set.indicator_of_mem hB, Set.indicator_of_mem
        (show fill ω Λ ζ ∈ B ∩ {η | quartersOf η = quartersOf ω} from ⟨hB, hq⟩)]
    · rw [Set.indicator_of_notMem hB, Set.indicator_of_notMem fun h => hB h.1]

/-- **`lem:freeze`(b)**: two configurations of `X_typ` that agree off a finite set `Λ` have the same
quarters, phase and background; so on `X_typ` the background on `Λ` is a function of `ω_{Λᶜ}`. -/
theorem freeze_b {ω ω' : Config (SiteVal U)} {τ : ℕ → Bool × Bool} (hs : Setting ω τ)
    (h' : IsLegal (Phi U) ω') (Λ : Finset Plane) (hΛ : ∀ ξ, ξ ∉ Λ → ω' ξ = ω ξ) :
    quartersOf ω' = quartersOf ω ∧ phaseMap ω' = phaseMap ω ∧ bgOf ω' = bgOf ω := by
  have hq : quartersOf ω' = quartersOf ω := quarter_rigid (isQTiling_of_legal h') hs.phase
    hs.typical.1 Λ (fun ξ hξ => by simp only [quartersOf, hΛ ξ hξ])
  exact ⟨hq, by simp only [phaseMap, hq], background_rigid hs h' Λ hΛ⟩

end Freeze

/-! ## `lem:freeze`(a), product form -/

section Product

/-- `PayVal` is the product of its fields (used only to transfer finiteness). -/
def PayVal.equivProd : PayVal ≃ Spin × Option Spin × Option Spin × Option Spin × Option Spin ×
    (Fin 4 → Bool) × (Fin 4 → Bool) × (Fin 4 → Bool) × (Fin 4 → Bool) where
  toFun p := (p.spin, p.wW, p.wE, p.wS, p.wN, p.kx, p.ky, p.lSx, p.lNx)
  invFun := fun ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ => ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩
  left_inv _ := rfl
  right_inv := fun ⟨_, _, _, _, _, _, _, _, _⟩ => rfl

instance : Fintype PayVal := Fintype.ofEquiv _ PayVal.equivProd.symm

/-- `ω = (𝔟, p)`: the configuration with background `𝔟` and payload `p`. -/
def assemble (b : Plane → BgVal U) (p : Plane → PayVal) : Config (SiteVal U) :=
  fun ξ => merge (b ξ) (p ξ)

theorem assemble_split (ω : Config (SiteVal U)) : assemble (bgOf ω) (payOf ω) = ω :=
  merge_bgOf_payOf ω

open Classical in
/-- The payload fillings of `Λ` compatible with the background `𝔟` (the payload components that
`𝔟` leaves absent are `0`): the fillings `p'_Λ` of payloads `p'` with `(𝔟, p')` a configuration. -/
noncomputable def compatFill (b : Plane → BgVal U) (Λ : Finset Plane) : Finset (Λ → PayVal) :=
  Finset.univ.filter fun π => ∀ x : Λ, Compatible (b x) (π x)

/-- The frozen kernel `γ^𝔟_Λ(· | p)` of `lem:freeze`, applied to a function `F` of the payload:
`∑_{p' = p off Λ} e^{-βH_Λ(𝔟, p')} F(p') / ∑_{p' = p off Λ} e^{-βH_Λ(𝔟, p')}`, the sums over the
payload fillings of `Λ` compatible with `𝔟`. -/
noncomputable def frozenApply (β : ℝ) (b : Plane → BgVal U) (Λ : Finset Plane)
    (F : (Plane → PayVal) → ℝ) (p : Plane → PayVal) : ℝ :=
  (∑ π ∈ compatFill b Λ, boltzmann β (energy (Phi U) Λ (assemble b (fill p Λ π))) *
      F (fill p Λ π)) /
    ∑ π ∈ compatFill b Λ, boltzmann β (energy (Phi U) Λ (assemble b (fill p Λ π)))

variable {ω : Config (SiteVal U)} {τ : ℕ → Bool × Bool} (hs : Setting ω τ) (β : ℝ)
  (Λ : Finset Plane)
include hs

/-- The sum over the fillings of `Λ` is the sum over the payload fillings compatible with the
background of `ω` (the other fillings have weight `0`, by `freeze_a`). -/
theorem sum_fill_eq (g : Config (SiteVal U) → ℝ) :
    ∑ ζ : Λ → SiteVal U, boltzmann β (energy (Phi U) Λ (fill ω Λ ζ)) * g (fill ω Λ ζ) =
      ∑ π ∈ compatFill (bgOf ω) Λ,
        boltzmann β (energy (Phi U) Λ (assemble (bgOf ω) (fill (payOf ω) Λ π))) *
          g (assemble (bgOf ω) (fill (payOf ω) Λ π)) := by
  classical
  have hfill : ∀ ζ : Λ → SiteVal U, (∀ x : Λ, bgPart (ζ x) = bgOf ω x) →
      fill ω Λ ζ = assemble (bgOf ω) (fill (payOf ω) Λ fun x => payPart (ζ x)) := by
    intro ζ hζ
    funext ξ
    by_cases hξ : ξ ∈ Λ
    · simp only [fill, assemble, dif_pos hξ]
      have h := hζ ⟨ξ, hξ⟩
      simp only at h
      rw [← h, merge_split]
    · simp only [fill, assemble, dif_neg hξ, bgOf, payOf, merge_split]
  rw [← Finset.sum_filter_of_ne (p := fun ζ : Λ → SiteVal U => ∀ x : Λ, bgPart (ζ x) = bgOf ω x)]
  · refine Finset.sum_nbij' (fun ζ x => payPart (ζ x)) (fun π x => merge (bgOf ω x) (π x))
      ?_ ?_ ?_ ?_ ?_
    · intro ζ hζ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hζ
      simp only [compatFill, Finset.mem_filter, Finset.mem_univ, true_and]
      intro x
      rw [← hζ x]
      exact compatible_split _
    · intro π hπ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro x
      exact bgPart_merge _ _
    · intro ζ hζ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hζ
      funext x
      simp only
      rw [← hζ x, merge_split]
    · intro π hπ
      simp only [compatFill, Finset.mem_filter, Finset.mem_univ, true_and] at hπ
      funext x
      exact payPart_merge (hπ x)
    · intro ζ hζ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hζ
      rw [hfill ζ hζ]
  · intro ζ _ hne
    have hw : boltzmann β (energy (Phi U) Λ (fill ω Λ ζ)) ≠ 0 := left_ne_zero_of_mul hne
    have hb := freeze_a hs β Λ ζ hw
    intro x
    have := congrFun hb x
    simpa [bgOf, fill, x.2] using this

/-- **`lem:freeze`(a)**, product form: at `ω = (𝔟, p) ∈ X_typ`,
`γ_Λ(· | ω) = δ_𝔟 ⊗ γ^𝔟_Λ(· | p)`: for every `F`, `(γ_Λ F)(ω) = (γ^𝔟_Λ F(𝔟, ·))(p)`. -/
theorem freeze_a_product (F : Config (SiteVal U) → ℝ) :
    kernelApply β (Phi U) Λ F ω =
      frozenApply β (bgOf ω) Λ (fun p' => F (assemble (bgOf ω) p')) (payOf ω) := by
  unfold kernelApply partitionFunction frozenApply
  rw [sum_fill_eq hs β Λ F]
  have h1 := sum_fill_eq hs β Λ (fun _ => 1)
  simp only [mul_one] at h1
  rw [h1]

end Product

/-! ## Mixtures of Gibbs measures (`lem:freeze`(c), converse) -/

section Mixture

variable (β : ℝ) {α : Type} [MeasurableSpace α]

theorem integral_comp_bounded {P : Measure α} [IsFiniteMeasure P]
    {κ : Kernel α (Config (SiteVal U))} [IsFiniteKernel κ] {F : Config (SiteVal U) → ℝ}
    (hF : Measurable F) (hb : ∃ C : ℝ, ∀ ω, |F ω| ≤ C) :
    ∫ ω, F ω ∂(κ ∘ₘ P) = ∫ τ, ∫ ω, F ω ∂(κ τ) ∂P := by
  obtain ⟨C, hC⟩ := hb
  have hint : Integrable F (κ ∘ₘ P) := Integrable.of_bound hF.aestronglyMeasurable C
    (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hC ω)
  rw [Measure.comp_eq_comp_const_apply] at hint ⊢
  rw [Kernel.integral_comp hint, Kernel.const_apply]

/-- **`lem:freeze`(c)**, converse direction: a mixture of Gibbs measures is a Gibbs measure. -/
theorem isGibbs_comp {P : Measure α} [IsProbabilityMeasure P]
    {κ : Kernel α (Config (SiteVal U))} [IsMarkovKernel κ]
    (h : ∀ᵐ τ ∂P, IsGibbs β (Phi U) (κ τ)) : IsGibbs β (Phi U) (κ ∘ₘ P) := by
  have hL := Gibbs.measurableSet_legal (S := SiteVal U) phi_isInteraction
  refine ⟨inferInstance, ?_, fun Λ F hF hb => ?_⟩
  · rw [Measure.bind_apply hL κ.aemeasurable]
    rw [lintegral_congr_ae (h.mono fun τ hτ => hτ.2.1)]
    simp
  · obtain ⟨C, hC⟩ := hb
    rw [integral_comp_bounded hF ⟨C, hC⟩,
      integral_comp_bounded (Gibbs.measurable_kernelApply phi_isInteraction β Λ hF)
        ⟨C, Gibbs.abs_kernelApply_le β (Phi U) Λ hC⟩]
    exact integral_congr_ae (h.mono fun τ hτ => hτ.2.2 Λ F hF ⟨C, hC⟩)

end Mixture

/-! ## Disintegration over the phase (`lem:freeze`(c)) -/

section Disintegration

variable (μ : Measure (Config (SiteVal U))) [IsProbabilityMeasure μ]

instance : Nonempty (Config (SiteVal U)) := ⟨cfg U (fun _ => (false, false)) fun _ => .plus⟩

/-- The joint law of the phase and the configuration. -/
def jointLaw : Measure ((ℕ → Bool × Bool) × Config (SiteVal U)) :=
  μ.map fun ω => (phaseMap ω, ω)

theorem measurable_phase_id :
    Measurable (fun ω : Config (SiteVal U) => (phaseMap ω, ω)) :=
  measurable_phaseMap.prodMk measurable_id

instance : IsProbabilityMeasure (jointLaw μ) :=
  (Measure.isProbabilityMeasure_map_iff measurable_phase_id.aemeasurable).2 inferInstance

omit [IsProbabilityMeasure μ] in
theorem jointLaw_fst : (jointLaw μ).fst = μ.map phaseMap :=
  Measure.fst_map_prodMk measurable_phaseMap measurable_id

omit [IsProbabilityMeasure μ] in
theorem jointLaw_snd : (jointLaw μ).snd = μ := by
  rw [jointLaw, Measure.snd_map_prodMk measurable_phaseMap measurable_id', Measure.map_id']

/-- The conditional laws `μ^τ` of `μ` given the phase `τ(ω)`. -/
def condLaw : Kernel (ℕ → Bool × Bool) (Config (SiteVal U)) := (jointLaw μ).condKernel

instance : IsMarkovKernel (condLaw μ) := by unfold condLaw; infer_instance

instance : IsProbabilityMeasure (μ.map phaseMap) :=
  (Measure.isProbabilityMeasure_map_iff measurable_phaseMap.aemeasurable).2 inferInstance

theorem jointLaw_eq : jointLaw μ = (μ.map phaseMap) ⊗ₘ condLaw μ := by
  rw [← jointLaw_fst]; exact (Measure.disintegrate (jointLaw μ) (jointLaw μ).condKernel).symm

/-- `μ = ∫ μ^τ (μ ∘ τ⁻¹)(dτ)`. -/
theorem disintegration : μ = condLaw μ ∘ₘ (μ.map phaseMap) := by
  have h := congrArg Measure.snd (jointLaw_eq μ)
  rw [jointLaw_snd, Measure.snd_compProd] at h
  exact h

omit [IsProbabilityMeasure μ] in
theorem jointLaw_prod {S : Set (ℕ → Bool × Bool)} {A : Set (Config (SiteVal U))}
    (hS : MeasurableSet S) (hA : MeasurableSet A) :
    jointLaw μ (S ×ˢ A) = μ (phaseMap ⁻¹' S ∩ A) := by
  rw [jointLaw, Measure.map_apply measurable_phase_id (hS.prod hA)]; rfl

variable {μ}

theorem measurableSet_graph :
    MeasurableSet {p : (ℕ → Bool × Bool) × Config (SiteVal U) | phaseMap p.2 = p.1} :=
  measurableSet_eq_fun (measurable_phaseMap.comp measurable_snd) measurable_fst

/-- `μ^τ` is concentrated on `{τ(ω) = τ}` for almost every `τ`. -/
theorem ae_condLaw_graph : ∀ᵐ τ ∂(μ.map phaseMap), condLaw μ τ {ω | phaseMap ω = τ} = 1 := by
  have hG := measurableSet_graph (U := U)
  have h1 : jointLaw μ {p | phaseMap p.2 = p.1} = 1 := by
    rw [jointLaw, Measure.map_apply measurable_phase_id hG]
    simp
  rw [jointLaw_eq, Measure.compProd_apply hG] at h1
  have hm : Measurable fun τ => condLaw μ τ (Prod.mk τ ⁻¹' {p | phaseMap p.2 = p.1}) :=
    Kernel.measurable_kernel_prodMk_left hG
  have hle : ∀ τ, condLaw μ τ (Prod.mk τ ⁻¹' {p | phaseMap p.2 = p.1}) ≤ 1 := fun τ => prob_le_one
  have hae := ae_eq_of_ae_le_of_lintegral_le (μ := μ.map phaseMap)
    (f := fun τ => condLaw μ τ (Prod.mk τ ⁻¹' {p | phaseMap p.2 = p.1})) (g := fun _ => 1)
    (ae_of_all _ hle) (by rw [h1]; simp) aemeasurable_const (by rw [h1]; simp)
  filter_upwards [hae] with τ hτ
  exact hτ

/-- `μ^τ(B) = μ(B)`-weighted: `μ^τ` charges the legal configurations for almost every `τ` if `μ`
does. -/
theorem ae_condLaw_full {B : Set (Config (SiteVal U))} (hB : MeasurableSet B) (h : μ B = 1) :
    ∀ᵐ τ ∂(μ.map phaseMap), condLaw μ τ B = 1 := by
  have h1 : jointLaw μ (Set.univ ×ˢ B) = 1 := by
    rw [jointLaw_prod μ MeasurableSet.univ hB, Set.preimage_univ, Set.univ_inter, h]
  rw [jointLaw_eq, Measure.compProd_apply_prod MeasurableSet.univ hB, Measure.restrict_univ] at h1
  have hle : ∀ τ, condLaw μ τ B ≤ 1 := fun τ => prob_le_one
  have hae := ae_eq_of_ae_le_of_lintegral_le (μ := μ.map phaseMap)
    (f := fun τ => condLaw μ τ B) (g := fun _ => 1)
    (ae_of_all _ hle) (by rw [h1]; simp) aemeasurable_const (by rw [h1]; simp)
  filter_upwards [hae] with τ hτ
  exact hτ

variable (β : ℝ)

/-- The joint law of `(τ(ω), η)`, `η` drawn from `γ_Λ(· | ω)`, is the joint law of `(τ(ω), ω)`. -/
theorem jointLaw_gibbsK (hμ : IsGibbs β (Phi U) μ) (htyp : ∀ᵐ ω ∂μ, Typical (phaseMap ω))
    (Λ : Finset Plane) :
    jointLaw μ = (jointLaw μ).fst ⊗ₘ (gibbsK β Λ ∘ₖ condLaw μ) := by
  have hlegal : ∀ᵐ ω ∂μ, IsLegal (Phi U) ω :=
    (ae_iff_measure_eq (Gibbs.measurableSet_legal phi_isInteraction).nullMeasurableSet).2
      (by rw [hμ.2.1, measure_univ])
  have hrect : ∀ S A, MeasurableSet S → MeasurableSet A → jointLaw μ (S ×ˢ A) =
      ((jointLaw μ).fst ⊗ₘ (gibbsK β Λ ∘ₖ condLaw μ)) (S ×ˢ A) := by
    intro S A hS hA
    rw [Measure.compProd_apply_prod hS hA, jointLaw_prod μ hS hA, jointLaw_fst]
    simp_rw [Kernel.comp_apply' _ _ _ hA]
    -- `∫_S ∫ γ_Λ(A | ω) dμ^τ = ∫ 1_S(τ(ω)) γ_Λ(A | ω) dμ`
    have hg : Measurable fun ω => gibbsK β Λ ω A := Kernel.measurable_coe _ hA
    have e1 : ∫⁻ τ in S, ∫⁻ ω, gibbsK β Λ ω A ∂(condLaw μ τ) ∂(μ.map phaseMap) =
        ∫⁻ ω, (phaseMap ⁻¹' S).indicator (fun ω => gibbsK β Λ ω A) ω ∂μ := by
      have hf : Measurable fun p : (ℕ → Bool × Bool) × Config (SiteVal U) =>
          S.indicator 1 p.1 * gibbsK β Λ p.2 A :=
        ((measurable_one.indicator hS).comp measurable_fst).mul (hg.comp measurable_snd)
      have h2 := Measure.lintegral_compProd (μ := μ.map phaseMap) (κ := condLaw μ) hf
      rw [← jointLaw_eq, jointLaw, lintegral_map hf measurable_phase_id] at h2
      rw [← lintegral_indicator hS]
      convert h2.symm using 1
      · refine lintegral_congr fun τ => ?_
        by_cases hτ : τ ∈ S
        · simp [Set.indicator_of_mem hτ]
        · simp [Set.indicator_of_notMem hτ]
      · refine lintegral_congr fun ω => ?_
        by_cases hω : phaseMap ω ∈ S
        · simp [Set.indicator_of_mem (show ω ∈ phaseMap ⁻¹' S from hω),
            Set.indicator_of_mem hω]
        · simp [Set.indicator_of_notMem (show ω ∉ phaseMap ⁻¹' S from hω),
            Set.indicator_of_notMem hω]
    rw [e1]
    -- at `ω ∈ X_typ` the kernel keeps the phase
    have e2 : ∫⁻ ω, (phaseMap ⁻¹' S).indicator (fun ω => gibbsK β Λ ω A) ω ∂μ =
        ∫⁻ ω, gibbsK β Λ ω (phaseMap ⁻¹' S ∩ A) ∂μ := by
      refine lintegral_congr_ae ?_
      filter_upwards [hlegal, htyp] with ω h1 h2
      have hs := setting_phaseMap h1 h2
      rw [gibbsK_inter β hs Λ (phaseMap ⁻¹' S ∩ A)]
      by_cases hω : phaseMap ω ∈ S
      · rw [Set.indicator_of_mem (show ω ∈ phaseMap ⁻¹' S from hω), gibbsK_inter β hs Λ A]
        congr 1
        ext η
        simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq]
        constructor
        · rintro ⟨hA, hq⟩; exact ⟨⟨by rw [phaseMap, hq]; exact hω, hA⟩, hq⟩
        · rintro ⟨⟨-, hA⟩, hq⟩; exact ⟨hA, hq⟩
      · rw [Set.indicator_of_notMem (show ω ∉ phaseMap ⁻¹' S from hω)]
        symm
        refine measure_mono_null (fun η hη => ?_) (measure_empty (μ := gibbsK β Λ ω))
        obtain ⟨⟨hS', -⟩, hq⟩ := hη
        have hq' : quartersOf η = quartersOf ω := hq
        simp only [Set.mem_preimage, phaseMap] at hS'
        exact hω (show qphaseOf (quartersOf ω) ∈ S by rw [← hq']; exact hS')
    rw [e2, lintegral_gibbsK β hμ Λ ((measurable_phaseMap hS).inter hA)]
  refine ext_of_generate_finite _ generateFrom_prod.symm isPiSystem_prod ?_ ?_
  · rintro _ ⟨S, hS, A, hA, rfl⟩
    exact hrect S A hS hA
  · rw [← Set.univ_prod_univ]
    exact hrect _ _ MeasurableSet.univ MeasurableSet.univ

/-- **`lem:freeze`(c)**: let `μ` be a Gibbs measure for `βΦ` concentrated on `X_typ`. Then
`μ = ∫ μ^τ (μ ∘ τ⁻¹)(dτ)`, and for almost every `τ` the phase `τ` is typical, the conditional law
`μ^τ` is a Gibbs measure for `βΦ` concentrated on the configurations of phase `τ`, and `μ^τ`-almost
every configuration is legal with quarter phase `τ` and background `𝔟_τ`. (The converse is
`isGibbs_comp`.) -/
theorem freeze_c (hμ : IsGibbs β (Phi U) μ) (htyp : ∀ᵐ ω ∂μ, Typical (phaseMap ω)) :
    μ = condLaw μ ∘ₘ (μ.map phaseMap) ∧
    ∀ᵐ τ ∂(μ.map phaseMap), Typical τ ∧ IsGibbs β (Phi U) (condLaw μ τ) ∧
      condLaw μ τ {ω | phaseMap ω = τ} = 1 ∧
      ∀ᵐ ω ∂(condLaw μ τ), Setting ω τ ∧ bgOf ω = bgMap U τ := by
  have hL := Gibbs.measurableSet_legal (S := SiteVal U) phi_isInteraction
  refine ⟨disintegration μ, ?_⟩
  -- the kernels fix `μ^τ`
  have hK : ∀ Λ : Finset Plane, ∀ᵐ τ ∂(μ.map phaseMap),
      (gibbsK β Λ ∘ₖ condLaw μ) τ = condLaw μ τ := by
    intro Λ
    have h := eq_condKernel_of_measure_eq_compProd (gibbsK β Λ ∘ₖ condLaw μ)
      (jointLaw_gibbsK β hμ htyp Λ)
    rw [jointLaw_fst] at h
    exact h
  have hKall := ae_all_iff.2 hK
  have hleg := ae_condLaw_full hL hμ.2.1
  have hgraph := ae_condLaw_graph (μ := μ)
  -- `μ^τ`-almost every configuration is legal and has a typical phase
  have hae : ∀ᵐ τ ∂(μ.map phaseMap), ∀ᵐ ω ∂(condLaw μ τ),
      IsLegal (Phi U) ω ∧ Typical (phaseMap ω) := by
    have h : ∀ᵐ ω ∂μ, IsLegal (Phi U) ω ∧ Typical (phaseMap ω) := by
      have hlegal : ∀ᵐ ω ∂μ, IsLegal (Phi U) ω :=
        (ae_iff_measure_eq hL.nullMeasurableSet).2 (by rw [hμ.2.1, measure_univ])
      filter_upwards [hlegal, htyp] with ω h1 h2 using ⟨h1, h2⟩
    rw [disintegration μ, Measure.comp_eq_comp_const_apply] at h
    have := Kernel.ae_ae_of_ae_comp h
    rwa [Kernel.const_apply] at this
  filter_upwards [hKall, hleg, hgraph, hae] with τ hτK hτL hτG hτA
  have hfull : ∀ᵐ ω ∂(condLaw μ τ), phaseMap ω = τ := by
    have hs : MeasurableSet {ω : Config (SiteVal U) | phaseMap ω = τ} :=
      measurable_phaseMap (measurableSet_singleton τ)
    rw [ae_iff, show {a : Config (SiteVal U) | ¬phaseMap a = τ} = {ω | phaseMap ω = τ}ᶜ from rfl,
      prob_compl_eq_zero_iff hs]
    exact hτG
  have hset : ∀ᵐ ω ∂(condLaw μ τ), Setting ω τ := by
    filter_upwards [hfull, hτA] with ω h1 h2
    rw [← h1]
    exact setting_phaseMap h2.1 h2.2
  have htypτ : Typical τ := by
    obtain ⟨ω, hω⟩ := (hset.and (ae_of_all _ fun _ => trivial)).exists
    exact hω.1.typical
  refine ⟨htypτ, ⟨inferInstance, hτL, fun Λ F hF hb => ?_⟩, hτG,
    hset.mono fun ω hω => ⟨hω, background_eq hω⟩⟩
  -- the DLR identity from `γ_Λ ∘ μ^τ = μ^τ`
  obtain ⟨C, hC⟩ := hb
  have e := hτK Λ
  rw [Kernel.comp_apply] at e
  calc ∫ ω, F ω ∂(condLaw μ τ) = ∫ ω, F ω ∂(gibbsK β Λ ∘ₘ condLaw μ τ) := by rw [e]
    _ = ∫ ω, ∫ η, F η ∂(gibbsK β Λ ω) ∂(condLaw μ τ) := integral_comp_bounded hF ⟨C, hC⟩
    _ = ∫ ω, kernelApply β (Phi U) Λ F ω ∂(condLaw μ τ) := by
        refine integral_congr_ae (ae_of_all _ fun ω => ?_)
        rw [Gibbs.kernelApply_eq_integral]; rfl

end Disintegration

end UPD.BG

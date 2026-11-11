/-
# Specifications with hard constraints (`set:def-gibbs`, the factor paragraph, `set:consistency`)

The paper's interaction has hard constraints (`Φ_A ∈ {0, 1, +∞}`), and the factor specifications
after `set:def-gibbs` have nonnegative factors ("the kernel ... proportional to the product of the
factors that involve a coordinate of `S`, whenever the normalization is positive"). This file
treats weight systems with **nonnegative** weights:
* `HardWeightSystem`: weights `W_Λ ≥ 0` of finite range with the ratio property and the support
  property (`W_Λ(ω) = 0 ⇒ W_Δ(ω) = 0` for `Λ ⊆ Δ`), which hold for every product of nonnegative
  factors (`W_Δ = W_Λ · R` with `R` the factors meeting `Δ` but not `Λ`);
* `expect_expect`: **`set:consistency`** `γ_Δ γ_Λ = γ_Δ` pointwise, at every boundary condition
  (with the convention `x / 0 = 0`, a kernel with `Z = 0` is the zero functional, and the identity
  still holds); `dlr_of_superset`: the paper's form ("if `μ` satisfies the Gibbs identity for `S'`,
  it satisfies it for `S ⊆ S'`");
* `siteSystem`: the Gibbs kernels of `set:def-gibbs` for a nearest-neighbour interaction with
  values in `[0, ∞]` form such a system (`W_Λ = e^{-βH_Λ}`, `e^{-∞} = 0`); `kernelApply_eq` and
  `isGibbs_iff`: the statement-level `IsGibbs β Φ` is exactly "Gibbs for the site system" (legal
  configurations = those at which every weight is positive).
The finer coordinates of the paper (the fields at the sites, `int:sub-split`) are a relabelling of
the same weights; that bridge is made with Section 4 (`int:sub-split`).
-/
import UndecidablePhaseDiagram.Gibbs.Site

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace UPD

namespace Gibbs

/-- Nonnegative weights `W_Λ` of finite range with the ratio and support properties. -/
structure HardWeightSystem (I E : Type) [DecidableEq I] where
  /-- The weight `W_Λ(ω)`. -/
  W : Finset I → (I → E) → ℝ
  nonneg : ∀ (Λ : Finset I) (ω : I → E), 0 ≤ W Λ ω
  /-- A finite set of coordinates on which `W_Λ` depends. -/
  range : Finset I → Finset I
  isLocal : ∀ (Λ : Finset I) (ω ω' : I → E), (∀ i ∈ range Λ, ω i = ω' i) → W Λ ω = W Λ ω'
  ratio : ∀ (Λ Δ : Finset I), Λ ⊆ Δ → ∀ ω ω' : I → E, (∀ i, i ∉ Λ → ω i = ω' i) →
    W Δ ω * W Λ ω' = W Δ ω' * W Λ ω
  support : ∀ (Λ Δ : Finset I), Λ ⊆ Δ → ∀ ω : I → E, W Λ ω = 0 → W Δ ω = 0

namespace HardWeightSystem

variable {I E : Type} [DecidableEq I] [Fintype E] (ws : HardWeightSystem I E)

/-- The partition function `Z_Λ(ω) = ∑_ζ W_Λ(ω^ζ)`. -/
def Z (Λ : Finset I) (ω : I → E) : ℝ := ∑ ζ : Λ → E, ws.W Λ (fillOn ω Λ ζ)

/-- The probability `W_Λ(ω^ζ) / Z_Λ(ω)` of the filling `ζ` (`0` if `Z_Λ(ω) = 0`). -/
def prob (Λ : Finset I) (ω : I → E) (ζ : Λ → E) : ℝ := ws.W Λ (fillOn ω Λ ζ) / ws.Z Λ ω

/-- The kernel applied to a function: `(γ_Λ F)(ω) = ∑_ζ prob ζ · F(ω^ζ)`. -/
def expect (Λ : Finset I) (ω : I → E) (F : (I → E) → ℝ) : ℝ :=
  ∑ ζ : Λ → E, ws.prob Λ ω ζ * F (fillOn ω Λ ζ)

theorem Z_nonneg (Λ : Finset I) (ω : I → E) : 0 ≤ ws.Z Λ ω :=
  Finset.sum_nonneg fun _ _ => ws.nonneg _ _

theorem prob_nonneg (Λ : Finset I) (ω : I → E) (ζ : Λ → E) : 0 ≤ ws.prob Λ ω ζ :=
  div_nonneg (ws.nonneg _ _) (ws.Z_nonneg _ _)

theorem sum_prob_le_one (Λ : Finset I) (ω : I → E) : ∑ ζ : Λ → E, ws.prob Λ ω ζ ≤ 1 := by
  simp only [prob, ← Finset.sum_div]
  exact div_self_le_one _

theorem Z_congr {Λ : Finset I} {ω ω' : I → E} (h : ∀ i, i ∉ Λ → ω i = ω' i) :
    ws.Z Λ ω = ws.Z Λ ω' := by
  simp only [Z, fillOn_congr h]

/-- `|γ_Λ F| ≤ C` if `|F| ≤ C`. -/
theorem abs_expect_le (Λ : Finset I) (ω : I → E) {F : (I → E) → ℝ} {C : ℝ}
    (hC : ∀ η, |F η| ≤ C) : |ws.expect Λ ω F| ≤ C := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC ω)
  calc |ws.expect Λ ω F| ≤ ∑ ζ : Λ → E, |ws.prob Λ ω ζ * F (fillOn ω Λ ζ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ ζ : Λ → E, ws.prob Λ ω ζ * C := by
        refine Finset.sum_le_sum fun ζ _ => ?_
        rw [abs_mul, abs_of_nonneg (ws.prob_nonneg _ _ _)]
        exact mul_le_mul_of_nonneg_left (hC _) (ws.prob_nonneg _ _ _)
    _ = (∑ ζ : Λ → E, ws.prob Λ ω ζ) * C := by rw [Finset.sum_mul]
    _ ≤ 1 * C := mul_le_mul_of_nonneg_right (ws.sum_prob_le_one Λ ω) hC0
    _ = C := one_mul C

/-- **`set:consistency`** (`γ_Δ γ_Λ = γ_Δ` for `Λ ⊆ Δ`), pointwise at every boundary condition. -/
theorem expect_expect [DecidableEq E] {Λ Δ : Finset I} (hΛΔ : Λ ⊆ Δ) (ω : I → E)
    (g : (I → E) → ℝ) :
    ∑ ζ' : Δ → E, ws.prob Δ ω ζ' * ws.expect Λ (fillOn ω Δ ζ') g = ws.expect Δ ω g := by
  set f : (Δ → E) → (I → E) := fillOn ω Δ with hf
  have hZ : ∀ ζ' : Δ → E, ws.Z Λ (f ζ') =
      ∑ ζ'' : Δ → E, if AgreeOff Λ ζ'' ζ' then ws.W Λ (f ζ'') else 0 := fun ζ' =>
    sum_fillOn_fillOn hΛΔ ω ζ' (ws.W Λ)
  have hE : ∀ ζ' : Δ → E, ws.expect Λ (f ζ') g =
      ∑ ζ'' : Δ → E, if AgreeOff Λ ζ'' ζ' then
        ws.W Λ (f ζ'') / ws.Z Λ (f ζ') * g (f ζ'') else 0 := fun ζ' =>
    sum_fillOn_fillOn hΛΔ ω ζ' (fun η => ws.W Λ η / ws.Z Λ (f ζ') * g η)
  have hdb : ∀ ζ' ζ'' : Δ → E, AgreeOff Λ ζ'' ζ' →
      ws.prob Δ ω ζ' * (ws.W Λ (f ζ'') / ws.Z Λ (f ζ')) =
        ws.prob Δ ω ζ'' * (ws.W Λ (f ζ') / ws.Z Λ (f ζ'')) := by
    intro ζ' ζ'' h
    have hag : ∀ i, i ∉ Λ → f ζ' i = f ζ'' i := (h.symm).fillOn ω
    have hZeq : ws.Z Λ (f ζ') = ws.Z Λ (f ζ'') := ws.Z_congr hag
    have hr := ws.ratio Λ Δ hΛΔ (f ζ') (f ζ'') hag
    simp only [prob, hZeq, ← hf]
    rw [div_mul_div_comm, div_mul_div_comm, hr]
  -- the inner sums of probabilities are one, or the outer weight vanishes
  have hone : ∀ ζ'' : Δ → E, ws.prob Δ ω ζ'' *
      ∑ ζ' : Δ → E, (if AgreeOff Λ ζ'' ζ' then ws.W Λ (f ζ') / ws.Z Λ (f ζ'') else 0) =
      ws.prob Δ ω ζ'' := by
    intro ζ''
    have hsum : ∑ ζ' : Δ → E, (if AgreeOff Λ ζ'' ζ' then ws.W Λ (f ζ') / ws.Z Λ (f ζ'') else 0) =
        (∑ ζ' : Δ → E, if AgreeOff Λ ζ' ζ'' then ws.W Λ (f ζ') else 0) / ws.Z Λ (f ζ'') := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun ζ' _ => ?_
      by_cases h : AgreeOff Λ ζ'' ζ'
      · simp [h, h.symm]
      · have h' : ¬ AgreeOff Λ ζ' ζ'' := fun h' => h h'.symm
        simp [h, h']
    rw [hsum, ← hZ]
    by_cases hz : ws.Z Λ (f ζ'') = 0
    · have hle : ws.W Λ (f ζ'') ≤ ws.Z Λ (f ζ'') := by
        rw [hZ]
        have hself : AgreeOff Λ ζ'' ζ'' := fun _ _ => rfl
        calc ws.W Λ (f ζ'') = if AgreeOff Λ ζ'' ζ'' then ws.W Λ (f ζ'') else 0 := by
              rw [if_pos hself]
          _ ≤ ∑ ζ' : Δ → E, if AgreeOff Λ ζ' ζ'' then ws.W Λ (f ζ') else 0 :=
              Finset.single_le_sum (f := fun ζ' => if AgreeOff Λ ζ' ζ'' then ws.W Λ (f ζ') else 0)
                (fun ζ' _ => by split_ifs; exacts [ws.nonneg _ _, le_rfl])
                (Finset.mem_univ ζ'')
      have hW : ws.W Λ (f ζ'') = 0 := le_antisymm (hz ▸ hle) (ws.nonneg _ _)
      have hWΔ : ws.W Δ (f ζ'') = 0 := ws.support Λ Δ hΛΔ _ hW
      have hp : ws.prob Δ ω ζ'' = 0 := by
        simp only [prob]; rw [← hf, hWΔ, zero_div]
      rw [hp, zero_mul]
    · rw [div_self hz, mul_one]
  calc ∑ ζ' : Δ → E, ws.prob Δ ω ζ' * ws.expect Λ (f ζ') g
      = ∑ ζ' : Δ → E, ∑ ζ'' : Δ → E, if AgreeOff Λ ζ'' ζ' then
          ws.prob Δ ω ζ'' * (ws.W Λ (f ζ') / ws.Z Λ (f ζ'')) * g (f ζ'') else 0 := by
        refine Finset.sum_congr rfl fun ζ' _ => ?_
        rw [hE, Finset.mul_sum]
        refine Finset.sum_congr rfl fun ζ'' _ => ?_
        by_cases h : AgreeOff Λ ζ'' ζ'
        · simp only [h, if_true]
          rw [← mul_assoc, hdb ζ' ζ'' h]
        · simp [h]
    _ = ∑ ζ'' : Δ → E, ∑ ζ' : Δ → E, if AgreeOff Λ ζ'' ζ' then
          ws.prob Δ ω ζ'' * (ws.W Λ (f ζ') / ws.Z Λ (f ζ'')) * g (f ζ'') else 0 :=
        Finset.sum_comm
    _ = ∑ ζ'' : Δ → E, ws.prob Δ ω ζ'' *
          (∑ ζ' : Δ → E, (if AgreeOff Λ ζ'' ζ' then ws.W Λ (f ζ') / ws.Z Λ (f ζ'') else 0)) *
            g (f ζ'') := by
        refine Finset.sum_congr rfl fun ζ'' _ => ?_
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun ζ' _ => ?_
        by_cases h : AgreeOff Λ ζ'' ζ'
        · simp only [h, if_true]
        · simp [h]
    _ = ws.expect Δ ω g := by
        rw [Finset.sum_congr rfl fun ζ'' _ => by rw [hone ζ'']]
        rfl

section Measure

variable [MeasurableSpace E]

/-- For measurable `F`, `ω ↦ (γ_Λ F)(ω)` is measurable. -/
theorem measurable_expect [Finite E] [DiscreteMeasurableSpace E] (Λ : Finset I)
    {F : (I → E) → ℝ} (hF : Measurable F) : Measurable (fun ω => ws.expect Λ ω F) := by
  have hW : Measurable (ws.W Λ) := measurable_of_dependsOn (ws.range Λ) _ (ws.isLocal Λ)
  let Ψ : ((Λ → E) → (I → E)) → ℝ := fun φ =>
    ∑ ζ : Λ → E, ws.W Λ (φ ζ) / (∑ ζ'' : Λ → E, ws.W Λ (φ ζ'')) * F (φ ζ)
  have hΨ : Measurable Ψ := by
    refine Finset.measurable_sum _ fun ζ _ => ?_
    refine Measurable.mul ?_ (hF.comp (measurable_pi_apply ζ))
    exact (hW.comp (measurable_pi_apply ζ)).div
      (Finset.measurable_sum _ fun ζ'' _ => hW.comp (measurable_pi_apply ζ''))
  exact (hΨ.comp (measurable_fillings Λ)).mono cylinderEvents_le_pi le_rfl

/-- Gibbs for a hard-constraint system (the paragraph after `set:def-gibbs`): a probability
measure concentrated on the configurations at which every weight is positive, with
`∫ F dμ = ∫ γ_Λ F dμ` for every finite `Λ` and every bounded measurable `F`. -/
def IsGibbs (μ : Measure (I → E)) : Prop :=
  IsProbabilityMeasure μ ∧ (∀ᵐ ω ∂μ, ∀ Λ : Finset I, 0 < ws.W Λ ω) ∧
    ∀ (Λ : Finset I) (F : (I → E) → ℝ), Measurable F → (∃ C : ℝ, ∀ ω, |F ω| ≤ C) →
      ∫ ω, F ω ∂μ = ∫ ω, ws.expect Λ ω F ∂μ

/-- **`set:consistency`**, the paper's form: the Gibbs identity for `Δ` implies it for `Λ ⊆ Δ`. -/
theorem dlr_of_superset [Finite E] [DiscreteMeasurableSpace E] [DecidableEq E]
    {μ : Measure (I → E)} {Λ Δ : Finset I} (hΛΔ : Λ ⊆ Δ)
    (h : ∀ F : (I → E) → ℝ, Measurable F → (∃ C : ℝ, ∀ ω, |F ω| ≤ C) →
      ∫ ω, F ω ∂μ = ∫ ω, ws.expect Δ ω F ∂μ)
    (F : (I → E) → ℝ) (hF : Measurable F) (hb : ∃ C : ℝ, ∀ ω, |F ω| ≤ C) :
    ∫ ω, F ω ∂μ = ∫ ω, ws.expect Λ ω F ∂μ := by
  obtain ⟨C, hC⟩ := hb
  have hG := h (fun ω => ws.expect Λ ω F) (ws.measurable_expect Λ hF)
    ⟨C, fun ω => ws.abs_expect_le Λ ω hC⟩
  rw [hG, h F hF ⟨C, hC⟩]
  congr 1
  funext ω
  exact (ws.expect_expect hΛΔ ω F).symm

end Measure

end HardWeightSystem

/-! ## The site specification of `set:def-gibbs` -/

section Site

variable {S : Type} [Fintype S]

/-- `e^{-β(a + b)} = e^{-βa} e^{-βb}` in `[0, ∞]` with `e^{-∞} = 0`. -/
theorem boltzmann_add (β : ℝ) (a b : ℝ≥0∞) :
    boltzmann β (a + b) = boltzmann β a * boltzmann β b := by
  unfold boltzmann
  by_cases ha : a = ⊤
  · simp [ha]
  by_cases hb : b = ⊤
  · simp [hb]
  rw [if_neg (ENNReal.add_ne_top.2 ⟨ha, hb⟩), if_neg ha, if_neg hb, ENNReal.toReal_add ha hb,
    ← Real.exp_add]
  ring_nf

/-- The sets meeting `Δ` but not `Λ`. -/
def RestSets (Λ Δ : Finset Plane) : Set (Finset Plane) :=
  {A | (A ∩ Δ).Nonempty ∧ ¬ (A ∩ Λ).Nonempty}

omit [Fintype S] in
/-- `H_Δ = H_Λ + R`, `R` the terms of the sets meeting `Δ` but not `Λ`. -/
theorem energy_add (Φ : Interaction S) {Λ Δ : Finset Plane} (h : Λ ⊆ Δ) (ω : Config S) :
    energy Φ Δ ω = energy Φ Λ ω + ∑' A : RestSets Λ Δ, Φ A.1 ω := by
  have e1 : energy Φ Δ ω =
      ∑' A, {A : Finset Plane | (A ∩ Δ).Nonempty}.indicator (fun A => Φ A ω) A :=
    tsum_subtype {A : Finset Plane | (A ∩ Δ).Nonempty} (fun A => Φ A ω)
  have e2 : energy Φ Λ ω =
      ∑' A, {A : Finset Plane | (A ∩ Λ).Nonempty}.indicator (fun A => Φ A ω) A :=
    tsum_subtype {A : Finset Plane | (A ∩ Λ).Nonempty} (fun A => Φ A ω)
  rw [e1, e2, tsum_subtype (RestSets Λ Δ) (fun A => Φ A ω), ← ENNReal.tsum_add]
  refine tsum_congr fun A => ?_
  by_cases hΛ : (A ∩ Λ).Nonempty
  · have hΔ : (A ∩ Δ).Nonempty := hΛ.mono (Finset.inter_subset_inter_left h)
    have hR : A ∉ RestSets Λ Δ := fun hA => hA.2 hΛ
    simp only [Set.indicator, Set.mem_setOf_eq, hΔ, hΛ, if_true, hR, if_false, add_zero]
  · by_cases hΔ : (A ∩ Δ).Nonempty
    · have hR : A ∈ RestSets Λ Δ := ⟨hΔ, hΛ⟩
      simp only [Set.indicator, Set.mem_setOf_eq, hΔ, hΛ, if_true, hR, if_false, zero_add]
    · have hR : A ∉ RestSets Λ Δ := fun hA => hΔ hA.1
      simp only [Set.indicator, Set.mem_setOf_eq, hΔ, hΛ, hR, if_false, add_zero]

omit [Fintype S] in
/-- The rest term does not depend on the coordinates in `Λ`. -/
theorem rest_congr {Φ : Interaction S} (hΦ : IsInteraction Φ) {Λ Δ : Finset Plane}
    {ω ω' : Config S} (h : ∀ ξ, ξ ∉ Λ → ω ξ = ω' ξ) :
    ∑' A : RestSets Λ Δ, Φ A.1 ω = ∑' A : RestSets Λ Δ, Φ A.1 ω' := by
  refine tsum_congr fun A => hΦ A.1 ω ω' fun ξ hξ => h ξ fun hξΛ => A.2.2 ⟨ξ, ?_⟩
  exact Finset.mem_inter.2 ⟨hξ, hξΛ⟩

/-- **The Gibbs kernels of `set:def-gibbs` form a hard-constraint weight system**
(`W_Λ = e^{-βH_Λ}`). -/
def siteSystem (β : ℝ) (Φ : Interaction S) (hΦ : IsInteraction Φ)
    (hnn : IsNearestNeighbour Φ) : HardWeightSystem Plane S where
  W Λ ω := boltzmann β (energy Φ Λ ω)
  nonneg _ _ := boltzmann_nonneg β _
  range Λ := (nnSets Λ).biUnion id
  isLocal Λ ω ω' h := by
    letI : MeasurableSpace S := ⊤
    haveI : DiscreteMeasurableSpace S := ⟨fun _ => trivial⟩
    show boltzmann β (energy Φ Λ ω) = boltzmann β (energy Φ Λ ω')
    rw [energy_eq_sum hnn, energy_eq_sum hnn]
    congr 1
    refine Finset.sum_congr rfl fun A hA => ?_
    simp only [Set.indicator]
    split_ifs
    · exact hΦ A ω ω' fun ξ hξ => h ξ (Finset.mem_biUnion.2 ⟨A, hA, hξ⟩)
    · rfl
  ratio Λ Δ hΛΔ ω ω' h := by
    rw [energy_add Φ hΛΔ ω, energy_add Φ hΛΔ ω', boltzmann_add, boltzmann_add,
      rest_congr hΦ h]
    ring
  support Λ Δ hΛΔ ω h0 := by
    have h0' : boltzmann β (energy Φ Λ ω) = 0 := h0
    show boltzmann β (energy Φ Δ ω) = 0
    rw [energy_add Φ hΛΔ ω, boltzmann_add, h0', zero_mul]

/-- The statement-level kernel is the kernel of the site system. -/
theorem kernelApply_eq (β : ℝ) {Φ : Interaction S} (hΦ : IsInteraction Φ)
    (hnn : IsNearestNeighbour Φ) (Λ : Finset Plane) (F : Config S → ℝ) (ω : Config S) :
    kernelApply β Φ Λ F ω = (siteSystem β Φ hΦ hnn).expect Λ ω F := by
  simp only [kernelApply, HardWeightSystem.expect, HardWeightSystem.prob, HardWeightSystem.Z,
    partitionFunction, siteSystem, div_mul_eq_mul_div, Finset.sum_div]
  rfl

/-- Legal configurations are those at which every weight `e^{-βH_Λ}` is positive. -/
theorem isLegal_iff (β : ℝ) {Φ : Interaction S} (hΦ : IsInteraction Φ)
    (hnn : IsNearestNeighbour Φ) (ω : Config S) :
    IsLegal Φ ω ↔ ∀ Λ : Finset Plane, 0 < (siteSystem β Φ hΦ hnn).W Λ ω := by
  letI : MeasurableSpace S := ⊤
  haveI : DiscreteMeasurableSpace S := ⟨fun _ => trivial⟩
  constructor
  · intro h Λ
    exact boltzmann_pos (energy_lt_top_of_legal hnn Λ h)
  · intro h A
    by_contra hA
    rw [not_lt, top_le_iff] at hA
    -- `A ≠ ∅`: the empty set carries no term of a nearest-neighbour interaction
    have hne : (A ∩ A).Nonempty := by
      rw [Finset.inter_self, Finset.nonempty_iff_ne_empty]
      rintro rfl
      have h0 : Φ ∅ ω = 0 := hnn ∅ (fun ⟨ξ, hξ⟩ => by simpa using hξ.symm)
        (fun ⟨ξ, hξ⟩ => by simpa using hξ.symm) (fun ⟨ξ, hξ⟩ => by simpa using hξ.symm) ω
      rw [h0] at hA
      exact ENNReal.zero_ne_top hA
    have htop : energy Φ A ω = ⊤ := by
      refine top_le_iff.1 ?_
      rw [← hA]
      exact ENNReal.le_tsum (f := fun A' : {A' : Finset Plane // (A' ∩ A).Nonempty} => Φ A'.1 ω)
        ⟨A, hne⟩
    have := h A
    simp only [siteSystem, boltzmann, htop, if_true, lt_self_iff_false] at this

/-- **The statement-level Gibbs measures are the Gibbs measures of the site system.** -/
theorem isGibbs_iff [MeasurableSpace S] [DiscreteMeasurableSpace S] (β : ℝ) {Φ : Interaction S}
    (hΦ : IsInteraction Φ) (hnn : IsNearestNeighbour Φ) (μ : Measure (Config S)) :
    UPD.IsGibbs β Φ μ ↔ (siteSystem β Φ hΦ hnn).IsGibbs μ := by
  have hk : ∀ Λ F, (fun ω => kernelApply β Φ Λ F ω) =
      fun ω => (siteSystem β Φ hΦ hnn).expect Λ ω F := fun Λ F =>
    funext fun ω => kernelApply_eq β hΦ hnn Λ F ω
  unfold UPD.IsGibbs HardWeightSystem.IsGibbs
  simp only [hk]
  constructor
  · rintro ⟨hP, hL, hD⟩
    refine ⟨hP, ?_, hD⟩
    have hae : ∀ᵐ ω ∂μ, ω ∈ {ω : Config S | IsLegal Φ ω} :=
      (ae_iff_measure_eq (measurableSet_legal hΦ).nullMeasurableSet).2 (by rw [hL, measure_univ])
    filter_upwards [hae] with ω hω using (isLegal_iff β hΦ hnn ω).1 hω
  · rintro ⟨hP, hL, hD⟩
    refine ⟨hP, ?_, hD⟩
    have hae : ∀ᵐ ω ∂μ, ω ∈ {ω : Config S | IsLegal Φ ω} := by
      filter_upwards [hL] with ω hω using (isLegal_iff β hΦ hnn ω).2 hω
    rw [(ae_iff_measure_eq (measurableSet_legal hΦ).nullMeasurableSet).1 hae, measure_univ]

end Site

end Gibbs

end UPD

/-
# Specifications from positive finite-range weights

The paper's kernels (`set:def-gibbs`, the factor specifications after it, the frozen kernels of
`lem:freeze`, the Ising models of `set:sub-ising`) are all of one form: for a finite set `Λ` of
coordinates and a boundary condition `ω`,
`γ_Λ(· | ω) = ∑_ζ W_Λ(ω^ζ) / Z_Λ(ω) · δ_{ω^ζ}`, `ω^ζ = fillOn ω Λ ζ`,
where `ζ` ranges over the fillings `Λ → E`. This file treats the case of strictly positive weights
`W_Λ` with finite range and the "ratio property" (`W_Δ / W_Λ` does not depend on the coordinates in
`Λ` when `Λ ⊆ Δ`), which is the case of positive factors (the paragraph after `set:def-gibbs`):
* `WeightSystem.expect_expect`: `γ_Δ γ_Λ = γ_Δ` for `Λ ⊆ Δ` (`set:consistency`);
* `WeightSystem.toSpecification`: the kernels form a `Specification` in the sense of `H1`
  (proper probability kernels from `ℱ_{Λᶜ}` to `ℱ`, consistent);
* `WeightSystem.isQuasilocal`: it is quasilocal (finite range);
* `WeightSystem.isGibbsMeasure_of_isDLR`: a measure satisfying the paper's DLR identity
  (`∫ F dμ = ∫ γ_Λ F dμ` for bounded measurable `F`) is compatible in the sense of `H1`.
-/
import UndecidablePhaseDiagram.Hypotheses
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace UPD

namespace Gibbs

variable {I E : Type} [DecidableEq I]

/-! ## Fillings -/

/-- The configuration equal to `ζ` on `Λ` and to `ω` off `Λ` (for `I = Plane` this is `fill`). -/
def fillOn (ω : I → E) (Λ : Finset I) (ζ : Λ → E) : I → E :=
  fun i => if h : i ∈ Λ then ζ ⟨i, h⟩ else ω i

theorem fillOn_of_mem (ω : I → E) {Λ : Finset I} (ζ : Λ → E) {i : I} (h : i ∈ Λ) :
    fillOn ω Λ ζ i = ζ ⟨i, h⟩ := by simp [fillOn, h]

theorem fillOn_of_not_mem (ω : I → E) {Λ : Finset I} (ζ : Λ → E) {i : I} (h : i ∉ Λ) :
    fillOn ω Λ ζ i = ω i := by simp [fillOn, h]

/-- A filling depends on `ω` only off `Λ`. -/
theorem fillOn_congr {ω ω' : I → E} {Λ : Finset I} (h : ∀ i, i ∉ Λ → ω i = ω' i)
    (ζ : Λ → E) : fillOn ω Λ ζ = fillOn ω' Λ ζ := by
  funext i
  by_cases hi : i ∈ Λ
  · simp [fillOn, hi]
  · simp [fillOn, hi, h i hi]

theorem fillOn_self (ω : I → E) (Λ : Finset I) : fillOn ω Λ (fun x => ω x.1) = ω := by
  funext i
  by_cases hi : i ∈ Λ <;> simp [fillOn, hi]

/-- `ω` and its fillings on `Λ` agree off `Λ`. -/
theorem fillOn_agree (ω : I → E) (Λ : Finset I) (ζ : Λ → E) :
    ∀ i, i ∉ Λ → fillOn ω Λ ζ i = ω i := fun _ h => fillOn_of_not_mem ω ζ h

/-- Two fillings of `Λ` by `ζ` from boundary conditions that agree on `D` agree on `D`. -/
theorem fillOn_agree_on {ω ω' : I → E} {Λ D : Finset I} (h : ∀ i ∈ D, ω i = ω' i)
    (ζ : Λ → E) : ∀ i ∈ D, fillOn ω Λ ζ i = fillOn ω' Λ ζ i := by
  intro i hi
  by_cases hΛ : i ∈ Λ
  · simp [fillOn, hΛ]
  · simp [fillOn, hΛ, h i hi]

/-- `ζ'` on `Δ` overwritten by `ζ` on `Λ ⊆ Δ`. -/
def merge {Λ Δ : Finset I} (ζ' : Δ → E) (ζ : Λ → E) : Δ → E :=
  fun x => if h : x.1 ∈ Λ then ζ ⟨x.1, h⟩ else ζ' x

theorem fillOn_fillOn {Λ Δ : Finset I} (hΛΔ : Λ ⊆ Δ) (ω : I → E) (ζ' : Δ → E) (ζ : Λ → E) :
    fillOn (fillOn ω Δ ζ') Λ ζ = fillOn ω Δ (merge ζ' ζ) := by
  funext i
  by_cases hΛ : i ∈ Λ
  · simp [fillOn, merge, hΛ, hΛΔ hΛ]
  · by_cases hΔ : i ∈ Δ <;> simp [fillOn, merge, hΛ, hΔ]

/-- Two fillings of `Δ` agree off `Λ`. -/
def AgreeOff {Δ : Finset I} (Λ : Finset I) (ζ ζ' : Δ → E) : Prop := ∀ x : Δ, x.1 ∉ Λ → ζ x = ζ' x

instance [Fintype E] [DecidableEq E] {Δ : Finset I} (Λ : Finset I) (ζ ζ' : Δ → E) :
    Decidable (AgreeOff Λ ζ ζ') := by unfold AgreeOff; infer_instance

theorem AgreeOff.symm {Λ Δ : Finset I} {ζ ζ' : Δ → E} (h : AgreeOff Λ ζ ζ') :
    AgreeOff Λ ζ' ζ := fun x hx => (h x hx).symm

theorem AgreeOff.fillOn {Λ Δ : Finset I} {ζ ζ' : Δ → E} (h : AgreeOff Λ ζ ζ') (ω : I → E) :
    ∀ i, i ∉ Λ → fillOn ω Δ ζ i = fillOn ω Δ ζ' i := by
  intro i hi
  by_cases hΔ : i ∈ Δ
  · simp only [Gibbs.fillOn, hΔ, dif_pos]; exact h ⟨i, hΔ⟩ hi
  · simp [Gibbs.fillOn, hΔ]

/-- The fillings of `Λ ⊆ Δ` starting from a filling `ζ'` of `Δ` are the fillings of `Δ` that agree
with `ζ'` off `Λ`, each once. -/
theorem sum_fillOn_fillOn [Fintype E] [DecidableEq E] {Λ Δ : Finset I} (hΛΔ : Λ ⊆ Δ)
    (ω : I → E) (ζ' : Δ → E) (f : (I → E) → ℝ) :
    ∑ ζ : Λ → E, f (fillOn (fillOn ω Δ ζ') Λ ζ) =
      ∑ ζ'' : Δ → E, if AgreeOff Λ ζ'' ζ' then f (fillOn ω Δ ζ'') else 0 := by
  rw [← Finset.sum_filter]
  refine Finset.sum_nbij' (fun ζ => merge ζ' ζ) (fun ζ'' x => ζ'' ⟨x.1, hΛΔ x.2⟩)
    ?_ ?_ ?_ ?_ ?_
  · intro ζ _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro x hx
    simp [merge, hx]
  · intro _ _; exact Finset.mem_univ _
  · intro ζ _
    funext x
    simp [merge, x.2]
  · intro ζ'' h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
    funext x
    by_cases hx : x.1 ∈ Λ
    · simp [merge, hx]
    · simp only [merge, hx, dif_neg, not_false_eq_true]
      exact (h x hx).symm
  · intro ζ _
    rw [fillOn_fillOn hΛΔ]

/-! ## Measurability of local functions and of fillings -/

section Measurability

variable [MeasurableSpace E]

/-- A function of finitely many coordinates is measurable (finite discrete spin set). -/
theorem measurable_of_dependsOn [Finite E] [DiscreteMeasurableSpace E] {β : Type}
    [MeasurableSpace β] (D : Finset I) (f : (I → E) → β)
    (hf : ∀ ω ω' : I → E, (∀ i ∈ D, ω i = ω' i) → f ω = f ω') : Measurable f := by
  rcases isEmpty_or_nonempty (I → E) with h | ⟨⟨ω₀⟩⟩
  · intro s _
    rw [Set.eq_empty_of_isEmpty (f ⁻¹' s)]
    exact MeasurableSet.empty
  · have hfac : f = (fun ζ : D → E => f (fillOn ω₀ D ζ)) ∘ (fun ω (x : D) => ω x.1) := by
      funext ω
      exact hf ω _ (fun i hi => by simp [fillOn, hi])
    rw [hfac]
    exact (measurable_of_countable _).comp
      (Measurable.of_eval (fun x => measurable_pi_apply x.1))

/-- A set of configurations that depends on finitely many coordinates is measurable. -/
theorem measurableSet_of_dependsOn [Finite E] [DiscreteMeasurableSpace E] (D : Finset I)
    (C : Set (I → E)) (hC : ∀ ω ω' : I → E, (∀ i ∈ D, ω i = ω' i) → (ω ∈ C ↔ ω' ∈ C)) :
    MeasurableSet C := by
  classical
  have : Measurable (fun ω : I → E => decide (ω ∈ C)) :=
    measurable_of_dependsOn D _ (fun ω ω' h => by simp [hC ω ω' h])
  have hpre : (fun ω : I → E => decide (ω ∈ C)) ⁻¹' {true} = C := by ext; simp
  rw [← hpre]
  exact this (measurableSet_singleton true)

/-- The filling map is measurable from `ℱ_{Λᶜ}` to `ℱ`. -/
theorem measurable_fillOn (Λ : Finset I) (ζ : Λ → E) :
    Measurable[cylinderEvents ((Λ : Set I)ᶜ)] (fun ω : I → E => fillOn ω Λ ζ) := by
  refine @measurable_pi_lambda _ _ _ (cylinderEvents _) _ _ (fun i => ?_)
  by_cases h : i ∈ Λ
  · simp only [fillOn, h, dif_pos]
    exact @measurable_const _ _ _ (cylinderEvents _) _
  · simp only [fillOn, h, dif_neg, not_false_eq_true]
    exact measurable_cylinderEvent_apply (by simpa using h)

/-- The family of all fillings of `Λ` is measurable from `ℱ_{Λᶜ}`. -/
theorem measurable_fillings (Λ : Finset I) :
    Measurable[cylinderEvents ((Λ : Set I)ᶜ)]
      (fun ω : I → E => fun ζ : Λ → E => fillOn ω Λ ζ) :=
  @measurable_pi_lambda _ _ _ (cylinderEvents _) _ _ (fun ζ => measurable_fillOn Λ ζ)

/-- An event of `ℱ_T` does not distinguish configurations that agree on `T`. -/
theorem mem_iff_of_cylinderEvents {T : Set I} {B : Set (I → E)}
    (hB : MeasurableSet[cylinderEvents T] B) {ω ω' : I → E} (h : ∀ i ∈ T, ω i = ω' i) :
    ω ∈ B ↔ ω' ∈ B := by
  let M : MeasurableSpace (I → E) :=
    { MeasurableSet' := fun B => ∀ ω ω' : I → E, (∀ i ∈ T, ω i = ω' i) → (ω ∈ B ↔ ω' ∈ B)
      measurableSet_empty := fun _ _ _ => by simp
      measurableSet_compl := fun B hB ω ω' h => by simp [hB ω ω' h]
      measurableSet_iUnion := fun B hB ω ω' h => by
        simp only [Set.mem_iUnion]
        exact exists_congr fun n => hB n ω ω' h }
  have hle : cylinderEvents (X := fun _ : I => E) T ≤ M := by
    refine iSup₂_le fun i hi => ?_
    rw [MeasurableSpace.comap_le_iff_le_map]
    intro s _ ω ω' h
    simp only [Set.mem_preimage]
    rw [h i hi]
  exact hle B hB ω ω' h

end Measurability

/-! ## Weight systems -/

/-- Strictly positive weights `W_Λ` with finite range (`W_Λ` depends only on the coordinates in
`range Λ`) and the ratio property: for `Λ ⊆ Δ`, `W_Δ / W_Λ` does not depend on the coordinates in
`Λ`, written without division. A product of positive factors, `W_Λ = ∏` over the factors meeting
`Λ`, is the basic example. -/
structure WeightSystem (I E : Type) [DecidableEq I] where
  /-- The weight `W_Λ(ω)`. -/
  W : Finset I → (I → E) → ℝ
  pos : ∀ (Λ : Finset I) (ω : I → E), 0 < W Λ ω
  /-- A finite set of coordinates on which `W_Λ` depends. -/
  range : Finset I → Finset I
  isLocal : ∀ (Λ : Finset I) (ω ω' : I → E), (∀ i ∈ range Λ, ω i = ω' i) → W Λ ω = W Λ ω'
  ratio : ∀ (Λ Δ : Finset I), Λ ⊆ Δ → ∀ ω ω' : I → E, (∀ i, i ∉ Λ → ω i = ω' i) →
    W Δ ω * W Λ ω' = W Δ ω' * W Λ ω

namespace WeightSystem

variable [Fintype E] (ws : WeightSystem I E)

/-- The partition function `Z_Λ(ω) = ∑_ζ W_Λ(ω^ζ)`. -/
def Z (Λ : Finset I) (ω : I → E) : ℝ := ∑ ζ : Λ → E, ws.W Λ (fillOn ω Λ ζ)

/-- The probability `W_Λ(ω^ζ) / Z_Λ(ω)` of the filling `ζ`. -/
def prob (Λ : Finset I) (ω : I → E) (ζ : Λ → E) : ℝ := ws.W Λ (fillOn ω Λ ζ) / ws.Z Λ ω

/-- The kernel applied to a function: `(γ_Λ F)(ω) = ∑_ζ prob ζ · F(ω^ζ)`. -/
def expect (Λ : Finset I) (ω : I → E) (F : (I → E) → ℝ) : ℝ :=
  ∑ ζ : Λ → E, ws.prob Λ ω ζ * F (fillOn ω Λ ζ)

/-- The kernel `γ_Λ(· | ω)` as a measure: a finite sum of point masses. -/
def kernel [MeasurableSpace E] (Λ : Finset I) (ω : I → E) : Measure (I → E) :=
  ∑ ζ : Λ → E, ENNReal.ofReal (ws.prob Λ ω ζ) • Measure.dirac (fillOn ω Λ ζ)

theorem Z_pos (Λ : Finset I) (ω : I → E) : 0 < ws.Z Λ ω :=
  Finset.sum_pos (fun _ _ => ws.pos _ _) ⟨fun x => ω x.1, Finset.mem_univ _⟩

theorem prob_nonneg (Λ : Finset I) (ω : I → E) (ζ : Λ → E) : 0 ≤ ws.prob Λ ω ζ :=
  div_nonneg (ws.pos _ _).le (ws.Z_pos _ _).le

theorem sum_prob (Λ : Finset I) (ω : I → E) : ∑ ζ : Λ → E, ws.prob Λ ω ζ = 1 := by
  simp only [prob, ← Finset.sum_div]
  exact div_self (ws.Z_pos Λ ω).ne'

/-- The kernel depends on `ω` only off `Λ`. -/
theorem Z_congr {Λ : Finset I} {ω ω' : I → E} (h : ∀ i, i ∉ Λ → ω i = ω' i) :
    ws.Z Λ ω = ws.Z Λ ω' := by
  simp only [Z, fillOn_congr h]

theorem prob_congr {Λ : Finset I} {ω ω' : I → E} (h : ∀ i, i ∉ Λ → ω i = ω' i) (ζ : Λ → E) :
    ws.prob Λ ω ζ = ws.prob Λ ω' ζ := by
  simp only [prob, fillOn_congr h, ws.Z_congr h]

theorem expect_congr {Λ : Finset I} {ω ω' : I → E} (h : ∀ i, i ∉ Λ → ω i = ω' i)
    (F : (I → E) → ℝ) : ws.expect Λ ω F = ws.expect Λ ω' F := by
  simp only [expect, fillOn_congr h, ws.prob_congr h]

theorem expect_nonneg (Λ : Finset I) (ω : I → E) {F : (I → E) → ℝ} (hF : ∀ η, 0 ≤ F η) :
    0 ≤ ws.expect Λ ω F :=
  Finset.sum_nonneg fun ζ _ => mul_nonneg (ws.prob_nonneg _ _ _) (hF _)

/-- A function that does not depend on the coordinates in `Λ` is left unchanged. -/
theorem expect_of_outside (Λ : Finset I) (ω : I → E) (F : (I → E) → ℝ)
    (hF : ∀ η, (∀ i, i ∉ Λ → η i = ω i) → F η = F ω) : ws.expect Λ ω F = F ω := by
  simp only [expect]
  rw [Finset.sum_congr rfl (fun ζ _ => by rw [hF _ (fillOn_agree ω Λ ζ)]), ← Finset.sum_mul,
    ws.sum_prob, one_mul]

/-- **`set:consistency`** (`γ_Δ γ_Λ = γ_Δ` for `Λ ⊆ Δ`), for functions: the ratio property gives
detailed balance of `γ_Λ` with respect to `γ_Δ(· | ω)`. -/
theorem expect_expect [DecidableEq E] {Λ Δ : Finset I} (hΛΔ : Λ ⊆ Δ) (ω : I → E)
    (g : (I → E) → ℝ) :
    ∑ ζ' : Δ → E, ws.prob Δ ω ζ' * ws.expect Λ (fillOn ω Δ ζ') g = ws.expect Δ ω g := by
  set f : (Δ → E) → (I → E) := fillOn ω Δ with hf
  -- the partition function of `Λ` at `f ζ'`, as a sum over the fillings of `Δ`
  have hZ : ∀ ζ' : Δ → E, ws.Z Λ (f ζ') =
      ∑ ζ'' : Δ → E, if AgreeOff Λ ζ'' ζ' then ws.W Λ (f ζ'') else 0 := fun ζ' =>
    sum_fillOn_fillOn hΛΔ ω ζ' (ws.W Λ)
  -- the inner expectation as a sum over the fillings of `Δ`
  have hE : ∀ ζ' : Δ → E, ws.expect Λ (f ζ') g =
      ∑ ζ'' : Δ → E, if AgreeOff Λ ζ'' ζ' then
        ws.W Λ (f ζ'') / ws.Z Λ (f ζ') * g (f ζ'') else 0 := fun ζ' =>
    sum_fillOn_fillOn hΛΔ ω ζ' (fun η => ws.W Λ η / ws.Z Λ (f ζ') * g η)
  -- detailed balance
  have hdb : ∀ ζ' ζ'' : Δ → E, AgreeOff Λ ζ'' ζ' →
      ws.prob Δ ω ζ' * (ws.W Λ (f ζ'') / ws.Z Λ (f ζ')) =
        ws.prob Δ ω ζ'' * (ws.W Λ (f ζ') / ws.Z Λ (f ζ'')) := by
    intro ζ' ζ'' h
    have hag : ∀ i, i ∉ Λ → f ζ' i = f ζ'' i := (h.symm).fillOn ω
    have hZeq : ws.Z Λ (f ζ') = ws.Z Λ (f ζ'') := ws.Z_congr hag
    have hr := ws.ratio Λ Δ hΛΔ (f ζ') (f ζ'') hag
    simp only [prob, hZeq, ← hf]
    rw [div_mul_div_comm, div_mul_div_comm, hr]
  -- the inner sums of probabilities are one
  have hone : ∀ ζ'' : Δ → E,
      ∑ ζ' : Δ → E, (if AgreeOff Λ ζ'' ζ' then ws.W Λ (f ζ') / ws.Z Λ (f ζ'') else 0) = 1 := by
    intro ζ''
    have : ∑ ζ' : Δ → E, (if AgreeOff Λ ζ'' ζ' then ws.W Λ (f ζ') / ws.Z Λ (f ζ'') else 0) =
        (∑ ζ' : Δ → E, if AgreeOff Λ ζ' ζ'' then ws.W Λ (f ζ') else 0) / ws.Z Λ (f ζ'') := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun ζ' _ => ?_
      by_cases h : AgreeOff Λ ζ'' ζ'
      · simp [h, h.symm]
      · have h' : ¬ AgreeOff Λ ζ' ζ'' := fun h' => h h'.symm
        simp [h, h']
    rw [this, ← hZ, div_self (ws.Z_pos _ _).ne']
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
    _ = ∑ ζ'' : Δ → E, ws.prob Δ ω ζ'' * g (f ζ'') *
          ∑ ζ' : Δ → E, (if AgreeOff Λ ζ'' ζ' then ws.W Λ (f ζ') / ws.Z Λ (f ζ'') else 0) := by
        refine Finset.sum_congr rfl fun ζ'' _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun ζ' _ => ?_
        by_cases h : AgreeOff Λ ζ'' ζ'
        · simp only [h, if_true]; ring
        · simp [h]
    _ = ws.expect Δ ω g := by
        rw [Finset.sum_congr rfl fun ζ'' _ => by rw [hone ζ'', mul_one]]
        rfl

/-! ## The kernel as a measure -/

omit [DecidableEq I] [Fintype E] in
theorem indicator_one_nonneg (A : Set (I → E)) (η : I → E) :
    0 ≤ A.indicator (1 : (I → E) → ℝ) η := by
  by_cases h : η ∈ A <;> simp [h]

omit [DecidableEq I] [Fintype E] in
theorem indicator_one_le (A : Set (I → E)) (η : I → E) :
    A.indicator (1 : (I → E) → ℝ) η ≤ 1 := by
  by_cases h : η ∈ A <;> simp [h]

section Kernel

variable [MeasurableSpace E]

theorem kernel_apply (Λ : Finset I) (ω : I → E) {A : Set (I → E)} (hA : MeasurableSet A) :
    ws.kernel Λ ω A = ENNReal.ofReal (ws.expect Λ ω (A.indicator 1)) := by
  rw [expect, ENNReal.ofReal_sum_of_nonneg
    (fun ζ _ => mul_nonneg (ws.prob_nonneg _ _ _) (indicator_one_nonneg _ _))]
  simp only [kernel, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ hA]
  refine Finset.sum_congr rfl fun ζ _ => ?_
  rw [ENNReal.ofReal_mul (ws.prob_nonneg _ _ _)]
  congr 1
  by_cases h : fillOn ω Λ ζ ∈ A <;> simp [h]

/-- The same, for every set, when singletons are measurable (countably many coordinates). -/
theorem kernel_apply' [MeasurableSingletonClass (I → E)] (Λ : Finset I) (ω : I → E)
    (A : Set (I → E)) : ws.kernel Λ ω A = ENNReal.ofReal (ws.expect Λ ω (A.indicator 1)) := by
  rw [expect, ENNReal.ofReal_sum_of_nonneg
    (fun ζ _ => mul_nonneg (ws.prob_nonneg _ _ _) (indicator_one_nonneg _ _))]
  simp only [kernel, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply]
  refine Finset.sum_congr rfl fun ζ _ => ?_
  rw [ENNReal.ofReal_mul (ws.prob_nonneg _ _ _)]
  congr 1
  by_cases h : fillOn ω Λ ζ ∈ A <;> simp [h]

theorem isProbability_kernel (Λ : Finset I) (ω : I → E) :
    IsProbabilityMeasure (ws.kernel Λ ω) := by
  constructor
  rw [ws.kernel_apply Λ ω MeasurableSet.univ]
  simp only [Set.indicator_univ, expect, Pi.one_apply, mul_one, ws.sum_prob, ENNReal.ofReal_one]

/-- For measurable `F`, `ω ↦ (γ_Λ F)(ω)` is `ℱ_{Λᶜ}`-measurable. -/
theorem measurable_expect [Finite E] [DiscreteMeasurableSpace E] (Λ : Finset I)
    {F : (I → E) → ℝ} (hF : Measurable F) :
    Measurable[cylinderEvents ((Λ : Set I)ᶜ)] (fun ω => ws.expect Λ ω F) := by
  have hW : Measurable (ws.W Λ) := measurable_of_dependsOn (ws.range Λ) _ (ws.isLocal Λ)
  let Ψ : ((Λ → E) → (I → E)) → ℝ := fun φ =>
    ∑ ζ : Λ → E, ws.W Λ (φ ζ) / (∑ ζ'' : Λ → E, ws.W Λ (φ ζ'')) * F (φ ζ)
  have hΨ : Measurable Ψ := by
    refine Finset.measurable_sum _ fun ζ _ => ?_
    refine Measurable.mul ?_ (hF.comp (measurable_pi_apply ζ))
    exact (hW.comp (measurable_pi_apply ζ)).div
      (Finset.measurable_sum _ fun ζ'' _ => hW.comp (measurable_pi_apply ζ''))
  exact hΨ.comp (measurable_fillings Λ)

theorem measurable_expect' [Finite E] [DiscreteMeasurableSpace E] (Λ : Finset I)
    {F : (I → E) → ℝ} (hF : Measurable F) : Measurable (fun ω => ws.expect Λ ω F) :=
  (ws.measurable_expect Λ hF).mono cylinderEvents_le_pi le_rfl

/-- **The kernels form a specification** in the sense of `H1` ([FV, Definitions 6.9, 6.11]). -/
def toSpecification [Finite E] [DiscreteMeasurableSpace E] [DecidableEq E] :
    Specification I E where
  kernel := ws.kernel
  isProbability := ws.isProbability_kernel
  measurable Λ A hA := by
    have hfun : (fun ω => ws.kernel Λ ω A) =
        fun ω => ENNReal.ofReal (ws.expect Λ ω (A.indicator 1)) :=
      funext fun ω => ws.kernel_apply Λ ω hA
    change Measurable[cylinderEvents ((Λ : Set I)ᶜ)] (fun ω => ws.kernel Λ ω A)
    rw [hfun]
    exact ENNReal.measurable_ofReal.comp
      (ws.measurable_expect Λ (measurable_const.indicator hA))
  proper Λ B hB ω := by
    show ws.kernel Λ ω B = _
    rw [ws.kernel_apply Λ ω (cylinderEvents_le_pi _ hB)]
    rw [ws.expect_of_outside Λ ω _ (fun η hη => by
      have : η ∈ B ↔ ω ∈ B := mem_iff_of_cylinderEvents hB (fun i hi => hη i (by simpa using hi))
      by_cases h : ω ∈ B <;> simp [h, this])]
    by_cases h : ω ∈ B <;> simp [h]
  consistent Λ Δ hΛΔ ω A hA := by
    show ∫⁻ ω', ws.kernel Λ ω' A ∂(ws.kernel Δ ω) = ws.kernel Δ ω A
    have hfun : (fun ω' => ws.kernel Λ ω' A) =
        fun ω' => ENNReal.ofReal (ws.expect Λ ω' (A.indicator 1)) :=
      funext fun ω' => ws.kernel_apply Λ ω' hA
    have hmeas : Measurable (fun ω' => ENNReal.ofReal (ws.expect Λ ω' (A.indicator 1))) :=
      ENNReal.measurable_ofReal.comp (ws.measurable_expect' Λ (measurable_const.indicator hA))
    rw [hfun, ws.kernel_apply Δ ω hA]
    unfold kernel
    rw [lintegral_finsetSum_measure]
    simp only [lintegral_smul_measure, lintegral_dirac' _ hmeas, smul_eq_mul]
    rw [← ws.expect_expect hΛΔ ω (A.indicator 1), ENNReal.ofReal_sum_of_nonneg
      (fun ζ' _ => mul_nonneg (ws.prob_nonneg _ _ _)
        (ws.expect_nonneg _ _ (indicator_one_nonneg A)))]
    refine Finset.sum_congr rfl fun ζ' _ => ?_
    rw [ENNReal.ofReal_mul (ws.prob_nonneg _ _ _)]

theorem toSpecification_kernel [Finite E] [DiscreteMeasurableSpace E] [DecidableEq E] :
    ws.toSpecification.kernel = ws.kernel := rfl

/-- **Quasilocality** (finite range): `γ_Λ(C | ·)` is locally constant for a cylinder `C`. -/
theorem isQuasilocal [Finite E] [DiscreteMeasurableSpace E] [DecidableEq E] :
    ws.toSpecification.IsQuasilocal := by
  intro Λ C hC ω ε hε
  obtain ⟨D, hD⟩ := hC
  have hCm : MeasurableSet C := measurableSet_of_dependsOn D C hD
  refine ⟨ws.range Λ ∪ D, fun ω' h => ?_⟩
  have hfill : ∀ ζ : Λ → E, ∀ i ∈ ws.range Λ ∪ D, fillOn ω' Λ ζ i = fillOn ω Λ ζ i :=
    fun ζ => fillOn_agree_on h ζ
  have hW : ∀ ζ : Λ → E, ws.W Λ (fillOn ω' Λ ζ) = ws.W Λ (fillOn ω Λ ζ) := fun ζ =>
    ws.isLocal Λ _ _ (fun i hi => hfill ζ i (Finset.mem_union_left _ hi))
  have hCeq : ∀ ζ : Λ → E, (fillOn ω' Λ ζ ∈ C ↔ fillOn ω Λ ζ ∈ C) := fun ζ =>
    hD _ _ (fun i hi => hfill ζ i (Finset.mem_union_right _ hi))
  have hZ : ws.Z Λ ω' = ws.Z Λ ω := by simp only [Z, hW]
  have heq : ws.expect Λ ω' (C.indicator 1) = ws.expect Λ ω (C.indicator 1) := by
    simp only [expect, prob, hW, hZ]
    refine Finset.sum_congr rfl fun ζ _ => ?_
    by_cases h1 : fillOn ω Λ ζ ∈ C
    · simp [h1, (hCeq ζ).2 h1]
    · simp [h1, mt (hCeq ζ).1 h1]
  show |((ws.kernel Λ ω') C).toReal - ((ws.kernel Λ ω) C).toReal| < ε
  rw [ws.kernel_apply Λ ω' hCm, ws.kernel_apply Λ ω hCm, heq, sub_self, abs_zero]
  exact hε

/-- The paper's notion (`set:def-gibbs` and the paragraph after it): `μ` is a probability measure
and `∫ F dμ = ∫ γ_Λ F dμ` for every finite `Λ` and every bounded measurable `F`. -/
def IsDLR (μ : Measure (I → E)) : Prop :=
  IsProbabilityMeasure μ ∧ ∀ (Λ : Finset I) (F : (I → E) → ℝ), Measurable F →
    (∃ C : ℝ, ∀ ω, |F ω| ≤ C) → ∫ ω, F ω ∂μ = ∫ ω, ws.expect Λ ω F ∂μ

/-- A measure satisfying the paper's DLR identity is compatible with the specification
([FV, Definition 6.12]); `F` is the indicator of the event. -/
theorem isGibbsMeasure_of_isDLR [Finite E] [DiscreteMeasurableSpace E] [DecidableEq E]
    {μ : Measure (I → E)} (h : ws.IsDLR μ) : ws.toSpecification.IsGibbsMeasure μ := by
  obtain ⟨hμ, hdlr⟩ := h
  refine ⟨hμ, fun Λ A hA => ?_⟩
  have hF : Measurable (A.indicator (1 : (I → E) → ℝ)) := measurable_const.indicator hA
  have hb : ∃ C : ℝ, ∀ ω, |A.indicator (1 : (I → E) → ℝ) ω| ≤ C :=
    ⟨1, fun ω => by by_cases h : ω ∈ A <;> simp [h]⟩
  have h1 := hdlr Λ _ hF hb
  have hk : ∀ ω, ws.toSpecification.kernel Λ ω A =
      ENNReal.ofReal (ws.expect Λ ω (A.indicator 1)) := fun ω => ws.kernel_apply Λ ω hA
  have hle : ∀ ω, ws.expect Λ ω (A.indicator 1) ≤ 1 := fun ω => by
    have := ws.isProbability_kernel Λ ω
    have h2 : ws.kernel Λ ω A ≤ 1 := prob_le_one
    rw [ws.kernel_apply Λ ω hA] at h2
    exact (ENNReal.ofReal_le_one).1 h2
  have hnn : ∀ ω, 0 ≤ ws.expect Λ ω (A.indicator 1) := fun ω =>
    ws.expect_nonneg _ _ (indicator_one_nonneg A)
  have hmeas := ws.measurable_expect' Λ hF
  -- both sides are finite; compare their real parts
  have hL : (∫⁻ ω, ws.toSpecification.kernel Λ ω A ∂μ).toReal =
      ∫ ω, ws.expect Λ ω (A.indicator 1) ∂μ := by
    simp only [hk]
    rw [← integral_toReal hmeas.ennreal_ofReal.aemeasurable
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    simp only [ENNReal.toReal_ofReal (hnn _)]
  have hR : (μ A).toReal = ∫ ω, A.indicator (1 : (I → E) → ℝ) ω ∂μ := by
    rw [integral_indicator_one hA, measureReal_def]
  have hfin : ∫⁻ ω, ws.toSpecification.kernel Λ ω A ∂μ ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := ∫⁻ _, 1 ∂μ) (by simp) (lintegral_mono fun ω => ?_)
    rw [hk]; exact ENNReal.ofReal_le_one.2 (hle ω)
  rw [← ENNReal.toReal_eq_toReal_iff' hfin (measure_ne_top μ A), hL, hR, h1]

end Kernel

end WeightSystem

end Gibbs

end UPD

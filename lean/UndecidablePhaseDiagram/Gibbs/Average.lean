/-
# Translation-invariant Gibbs measures by averaging (Krylov–Bogolyubov)

New in this project (session 10). For a nearest-neighbour, translation-invariant interaction `Φ`
on a finite alphabet and a Gibbs measure `μ` for `βΦ`, the Cesàro averages
`μ_n = |B_n|⁻¹ ∑_{a ∈ B_n} T_a μ` over the boxes `B_n = [0, n]²` have translation-invariant Gibbs
cluster points. This gives the existence halves of `thm:main`(i), (ii) without any measurability
in the phase (the paper's existence argument for `prop:scaffold-ti`(b), "average the translates
... over growing boxes and take a limit point", in the Gibbs setting).

* `isGibbs_map_shift`: `T_a μ` is Gibbs (covariance of the energy `energy_shift` and of the
  kernels `kernelApply_shift`); `isGibbs_finsetAvg`: finite averages of Gibbs measures are Gibbs;
  `isGibbs_avgMeasure`: hence so is `μ_n`.
* `abs_avgMeasure_shift_sub_le`: `|μ_n(T_a⁻¹ s) - μ_n(s)| ≤ 1 / (n + 1)` for `a = e₁, e₂`
  (telescoping along the rows or columns of the box, `abs_sum_avgBox_shift_sub_le`);
  `isTranslationInvariantMeasure_of_e1_e2`: invariance under `e₁`, `e₂` gives invariance under
  `ℤ²`.
* `isGibbs_of_clusterPt`: a cluster point of Gibbs measures (in the weak topology on the compact
  space of probability measures on `Config S`) is Gibbs: `X_Φ` is the intersection of the local
  events `{Φ_A < ∞}`, and the Gibbs property is detailed balance on elementary cylinders
  (`HardWeightSystem.db_of_isGibbs`, `HardWeightSystem.isGibbs_of_db`), a closed condition;
  `isTranslationInvariantMeasure_of_clusterPt`: a cluster point of the `μ_n` is translation
  invariant (cylinder masses, `ext_cyl`).
* **`exists_ti_gibbs_avg`** (local `f`), `exists_ti_gibbs_avg_of_continuous` (continuous `f`):
  a translation-invariant Gibbs measure `μ̄` with `∫ f dμ̄` a cluster value of the box averages
  `A_n = |B_n|⁻¹ ∑_{a ∈ B_n} ∫ f ∘ T_a dμ` (`boxAvg`); `exists_ti_gibbs_avg₂`,
  `exists_ti_gibbs_avg₂_of_continuous`: the same for two Gibbs measures at once (a joint cluster
  point); `exists_ti_gibbs`; `le_boxAvg`, `boxAvg_le`: uniform bounds on the translates bound the
  box averages.
-/
import UndecidablePhaseDiagram.Gibbs.Existence
import UndecidablePhaseDiagram.Gibbs.Cylinder
import Mathlib.MeasureTheory.Measure.Prokhorov

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace UPD

namespace Gibbs

/-! ## Translations -/

section Shift

variable {S : Type}

/-- `T_a T_b = T_{a+b}`. -/
theorem shift_shift (a b : Plane) (ω : Config S) : shift a (shift b ω) = shift (a + b) ω := by
  funext ξ
  simp only [shift, sub_sub]

/-- `T_0 = id`. -/
theorem shift_zero_apply (ω : Config S) : shift 0 ω = ω := by
  funext ξ
  simp only [shift, sub_zero]

/-- `(A - a) + a = A`. -/
theorem image_add_image_sub (A : Finset Plane) (a : Plane) :
    (A.image fun ξ => ξ - a).image (fun ξ => ξ + a) = A := by
  rw [Finset.image_image]
  convert Finset.image_id (s := A) using 2
  funext ξ; simp

/-- `(A + a) - a = A`. -/
theorem image_sub_image_add (A : Finset Plane) (a : Plane) :
    (A.image fun ξ => ξ + a).image (fun ξ => ξ - a) = A := by
  rw [Finset.image_image]
  convert Finset.image_id (s := A) using 2
  funext ξ; simp

/-- `ξ ∈ A + a ↔ ξ - a ∈ A`. -/
theorem mem_image_add {A : Finset Plane} {a ξ : Plane} :
    ξ ∈ A.image (fun x => x + a) ↔ ξ - a ∈ A := by
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro h
    exact ⟨ξ - a, h, by simp⟩

/-- Legality is invariant under translations (translation-invariant `Φ`). -/
theorem isLegal_shift_iff {Φ : Interaction S} (hti : IsTranslationInvariant Φ) (a : Plane)
    (ω : Config S) : IsLegal Φ (shift a ω) ↔ IsLegal Φ ω := by
  constructor
  · intro h A
    rw [← hti A a ω]
    exact h _
  · intro h A
    rw [← image_add_image_sub A a, hti]
    exact h _

/-- **Covariance of the energy**: `H_{Λ+a}(T_a η) = H_Λ(η)`. -/
theorem energy_shift {Φ : Interaction S} (hti : IsTranslationInvariant Φ) (Λ : Finset Plane)
    (a : Plane) (η : Config S) :
    energy Φ (Λ.image fun x => x + a) (shift a η) = energy Φ Λ η := by
  unfold energy
  let e : {A : Finset Plane // (A ∩ Λ).Nonempty} ≃
      {A : Finset Plane // (A ∩ Λ.image fun x => x + a).Nonempty} :=
    { toFun := fun B => ⟨B.1.image fun x => x + a, by
        obtain ⟨x, hx⟩ := B.2
        rw [Finset.mem_inter] at hx
        exact ⟨x + a, Finset.mem_inter.2
          ⟨Finset.mem_image_of_mem _ hx.1, Finset.mem_image_of_mem _ hx.2⟩⟩⟩
      invFun := fun A => ⟨A.1.image fun x => x - a, by
        obtain ⟨y, hy⟩ := A.2
        rw [Finset.mem_inter] at hy
        exact ⟨y - a, Finset.mem_inter.2 ⟨Finset.mem_image_of_mem _ hy.1, mem_image_add.1 hy.2⟩⟩⟩
      left_inv := fun B => Subtype.ext (image_sub_image_add B.1 a)
      right_inv := fun A => Subtype.ext (image_add_image_sub A.1 a) }
  rw [← e.tsum_eq]
  exact tsum_congr fun B => hti B.1 a η

/-- **Covariance of the kernels**: `(γ_{Λ+a} F)(T_a ω) = (γ_Λ (F ∘ T_a))(ω)`. -/
theorem kernelApply_shift [Fintype S] {Φ : Interaction S} (hti : IsTranslationInvariant Φ)
    (β : ℝ) (Λ : Finset Plane) (a : Plane) (F : Config S → ℝ) (ω : Config S) :
    kernelApply β Φ (Λ.image fun x => x + a) F (shift a ω) =
      kernelApply β Φ Λ (fun η => F (shift a η)) ω := by
  set Λ' := Λ.image fun x => x + a with hΛ'
  let σ : (Λ → S) ≃ (Λ' → S) :=
    { toFun := fun ζ y => ζ ⟨y.1 - a, mem_image_add.1 y.2⟩
      invFun := fun ζ' x => ζ' ⟨x.1 + a, Finset.mem_image_of_mem _ x.2⟩
      left_inv := fun ζ => funext fun x => congrArg ζ (Subtype.ext (add_sub_cancel_right x.1 a))
      right_inv := fun ζ' => funext fun y => congrArg ζ' (Subtype.ext (sub_add_cancel y.1 a)) }
  have hfill : ∀ ζ : Λ → S, fill (shift a ω) Λ' (σ ζ) = shift a (fill ω Λ ζ) := by
    intro ζ
    funext ξ
    by_cases h : ξ - a ∈ Λ
    · have h' : ξ ∈ Λ' := mem_image_add.2 h
      simp only [fill, shift, h, h', dif_pos]
      rfl
    · have h' : ξ ∉ Λ' := fun hh => h (mem_image_add.1 hh)
      simp only [fill, shift, h, h', dif_neg, not_false_eq_true]
  have hen : ∀ ζ : Λ → S,
      energy Φ Λ' (fill (shift a ω) Λ' (σ ζ)) = energy Φ Λ (fill ω Λ ζ) := by
    intro ζ
    rw [hfill, hΛ', energy_shift hti]
  unfold kernelApply partitionFunction
  have hnum : ∑ ζ' : Λ' → S, boltzmann β (energy Φ Λ' (fill (shift a ω) Λ' ζ')) *
      F (fill (shift a ω) Λ' ζ') = ∑ ζ : Λ → S, boltzmann β (energy Φ Λ (fill ω Λ ζ)) *
      F (shift a (fill ω Λ ζ)) :=
    (Fintype.sum_equiv σ _ _ fun ζ => by rw [hen, hfill]).symm
  have hden : ∑ ζ' : Λ' → S, boltzmann β (energy Φ Λ' (fill (shift a ω) Λ' ζ')) =
      ∑ ζ : Λ → S, boltzmann β (energy Φ Λ (fill ω Λ ζ)) :=
    (Fintype.sum_equiv σ _ _ fun ζ => by rw [hen]).symm
  rw [hnum, hden]

variable [MeasurableSpace S]

/-- `T_a` is measurable. -/
theorem measurable_shiftConfig (a : Plane) : Measurable (shift a : Config S → Config S) :=
  Measurable.of_eval fun ξ => measurable_pi_apply (ξ - a)

/-- `T_a (T_b μ) = T_{a+b} μ`. -/
theorem map_shift_map_shift (μ : Measure (Config S)) (a b : Plane) :
    (μ.map (shift b)).map (shift a) = μ.map (shift (a + b)) := by
  rw [Measure.map_map (measurable_shiftConfig a) (measurable_shiftConfig b)]
  congr 1
  funext ω
  exact shift_shift a b ω

/-- `T_0 μ = μ`. -/
theorem map_shift_zero (μ : Measure (Config S)) : μ.map (shift 0) = μ := by
  have h : (shift 0 : Config S → Config S) = id := funext shift_zero_apply
  rw [h, Measure.map_id]

/-- **Translation invariance from the two unit translations** `e₁`, `e₂` (they generate `ℤ²`). -/
theorem isTranslationInvariantMeasure_of_e1_e2 {ν : Measure (Config S)}
    (h1 : ν.map (shift e1) = ν) (h2 : ν.map (shift e2) = ν) :
    IsTranslationInvariantMeasure ν := by
  let G : AddSubgroup Plane :=
    { carrier := {a | ν.map (shift a) = ν}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [← map_shift_map_shift, hb, ha]
      zero_mem' := map_shift_zero ν
      neg_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at ha ⊢
        conv_lhs => rw [← ha]
        rw [map_shift_map_shift, neg_add_cancel, map_shift_zero] }
  intro a
  have ha : a = a.1 • e1 + a.2 • e2 := by
    ext <;> simp [e1, e2]
  have hm : a.1 • e1 + a.2 • e2 ∈ G := G.add_mem (G.zsmul_mem h1 a.1) (G.zsmul_mem h2 a.2)
  rw [← ha] at hm
  exact hm

end Shift

/-! ## Gibbs measures: translates and finite averages -/

section GibbsAvg

variable {S : Type} [Fintype S] [MeasurableSpace S] [DiscreteMeasurableSpace S]

/-- **Translates of Gibbs measures are Gibbs** (translation-invariant `Φ`): `T_a μ` is Gibbs for
`βΦ` whenever `μ` is. -/
theorem isGibbs_map_shift {Φ : Interaction S} (hΦ : IsInteraction Φ)
    (hti : IsTranslationInvariant Φ) {β : ℝ} {μ : Measure (Config S)} (hμ : IsGibbs β Φ μ)
    (a : Plane) : IsGibbs β Φ (μ.map (shift a)) := by
  obtain ⟨hP, hL, hD⟩ := hμ
  haveI := hP
  have hm := measurable_shiftConfig (S := S) a
  refine ⟨(Measure.isProbabilityMeasure_map_iff hm.aemeasurable).2 inferInstance, ?_, fun Λ F hF ⟨C, hC⟩ => ?_⟩
  · rw [Measure.map_apply hm (measurableSet_legal hΦ)]
    have e : shift a ⁻¹' {ω : Config S | IsLegal Φ ω} = {ω | IsLegal Φ ω} := by
      ext ω
      exact isLegal_shift_iff hti a ω
    rw [e, hL]
  · rw [integral_map hm.aemeasurable hF.aestronglyMeasurable,
      integral_map hm.aemeasurable (measurable_kernelApply hΦ β Λ hF).aestronglyMeasurable,
      hD (Λ.image fun x => x - a) (fun ω => F (shift a ω)) (hF.comp hm) ⟨C, fun ω => hC _⟩]
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    have h := kernelApply_shift hti β (Λ.image fun x => x - a) a F ω
    rw [image_add_image_sub] at h
    exact h.symm

/-- **Finite averages of Gibbs measures are Gibbs** (the DLR identity is linear in `μ`). -/
theorem isGibbs_finsetAvg {Φ : Interaction S} (hΦ : IsInteraction Φ) {β : ℝ} {ι : Type}
    (s : Finset ι) (hs : s.Nonempty) (ν : ι → Measure (Config S))
    (h : ∀ i ∈ s, IsGibbs β Φ (ν i)) :
    IsGibbs β Φ ((s.card : ℝ≥0∞)⁻¹ • ∑ i ∈ s, ν i) := by
  have hc0 : (s.card : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 hs.card_pos.ne'
  have hmass : ∀ A : Set (Config S), (∀ i ∈ s, ν i A = 1) →
      ((s.card : ℝ≥0∞)⁻¹ • ∑ i ∈ s, ν i) A = 1 := by
    intro A hA
    rw [Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply, Finset.sum_congr rfl hA,
      smul_eq_mul, Finset.sum_const, nsmul_eq_mul, mul_one]
    exact ENNReal.inv_mul_cancel hc0 (ENNReal.natCast_ne_top _)
  refine ⟨⟨hmass _ fun i hi => (h i hi).1.measure_univ⟩, hmass _ fun i hi => (h i hi).2.1,
    fun Λ F hF ⟨C, hC⟩ => ?_⟩
  have hint : ∀ G : Config S → ℝ, Measurable G → (∀ ω, |G ω| ≤ C) →
      ∀ i ∈ s, Integrable G (ν i) := fun G hG hGC i hi => by
    haveI := (h i hi).1
    exact Integrable.of_bound hG.aestronglyMeasurable C
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hGC ω)
  rw [integral_smul_measure, integral_smul_measure, integral_finsetSum_measure (hint F hF hC),
    integral_finsetSum_measure (hint _ (measurable_kernelApply hΦ β Λ hF)
      (abs_kernelApply_le β Φ Λ hC))]
  congr 1
  exact Finset.sum_congr rfl fun i hi => (h i hi).2.2 Λ F hF ⟨C, hC⟩

end GibbsAvg

/-! ## Boxes and Cesàro averages -/

section Box

/-- The site `(i, j) ∈ ℤ²` of a pair of naturals. -/
def natSite (p : ℕ × ℕ) : Plane := ((p.1 : ℤ), (p.2 : ℤ))

/-- `natSite` is injective. -/
theorem natSite_injective : Function.Injective natSite := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ h
  simp only [natSite, Prod.mk.injEq, Nat.cast_inj] at h
  rw [h.1, h.2]

/-- The box `B_n = [0, n]² ⊆ ℤ²`. -/
def avgBox (n : ℕ) : Finset Plane :=
  (Finset.range (n + 1) ×ˢ Finset.range (n + 1)).image natSite

/-- `|B_n| = (n + 1)²`. -/
theorem card_avgBox (n : ℕ) : (avgBox n).card = (n + 1) ^ 2 := by
  rw [avgBox, Finset.card_image_of_injective _ natSite_injective, Finset.card_product,
    Finset.card_range, sq]

/-- `B_n` is nonempty. -/
theorem avgBox_nonempty (n : ℕ) : (avgBox n).Nonempty :=
  ⟨natSite (0, 0), Finset.mem_image_of_mem _ (by simp)⟩

/-- A sum over `B_n` as a double sum over the rows and columns. -/
theorem sum_avgBox {M : Type} [AddCommMonoid M] (n : ℕ) (φ : Plane → M) :
    ∑ c ∈ avgBox n, φ c =
      ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1), φ ((i : ℤ), (j : ℤ)) := by
  rw [avgBox, Finset.sum_image (fun p _ q _ h => natSite_injective h), Finset.sum_product]
  rfl

/-- **The boundary estimate**: for `0 ≤ φ ≤ 1` and `a = e₁` or `a = e₂`,
`|∑_{c ∈ B_n} φ(a + c) - ∑_{c ∈ B_n} φ(c)| ≤ n + 1` (telescoping along the rows or the
columns of the box). -/
theorem abs_sum_avgBox_shift_sub_le (n : ℕ) (φ : Plane → ℝ) (hφ : ∀ c, 0 ≤ φ c ∧ φ c ≤ 1)
    {a : Plane} (ha : a = e1 ∨ a = e2) :
    |∑ c ∈ avgBox n, φ (a + c) - ∑ c ∈ avgBox n, φ c| ≤ n + 1 := by
  have h1 : ∀ x y : Plane, |φ x - φ y| ≤ 1 := fun x y => by
    rw [abs_le]
    constructor <;> linarith [(hφ x).1, (hφ x).2, (hφ y).1, (hφ y).2]
  have hsum : ∑ j ∈ Finset.range (n + 1), (1 : ℝ) = n + 1 := by simp
  rw [sum_avgBox, sum_avgBox, ← Finset.sum_sub_distrib]
  simp only [← Finset.sum_sub_distrib]
  rcases ha with rfl | rfl
  · have e : ∀ i j : ℕ, e1 + ((i : ℤ), (j : ℤ)) = (((i + 1 : ℕ) : ℤ), (j : ℤ)) := fun i j => by
      simp only [e1, Prod.mk_add_mk, Nat.cast_add, Nat.cast_one, zero_add]
      rw [add_comm]
    simp only [e]
    rw [Finset.sum_comm]
    have ht : ∀ j : ℕ, ∑ i ∈ Finset.range (n + 1),
        (φ (((i + 1 : ℕ) : ℤ), (j : ℤ)) - φ ((i : ℤ), (j : ℤ))) =
        φ (((n + 1 : ℕ) : ℤ), (j : ℤ)) - φ (((0 : ℕ) : ℤ), (j : ℤ)) := fun j =>
      Finset.sum_range_sub (fun i : ℕ => φ ((i : ℤ), (j : ℤ))) (n + 1)
    rw [Finset.sum_congr rfl fun j _ => ht j, ← hsum]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => h1 _ _)
  · have e : ∀ i j : ℕ, e2 + ((i : ℤ), (j : ℤ)) = ((i : ℤ), ((j + 1 : ℕ) : ℤ)) := fun i j => by
      simp only [e2, Prod.mk_add_mk, Nat.cast_add, Nat.cast_one, zero_add]
      rw [add_comm (1 : ℤ)]
    simp only [e]
    have ht : ∀ i : ℕ, ∑ j ∈ Finset.range (n + 1),
        (φ ((i : ℤ), ((j + 1 : ℕ) : ℤ)) - φ ((i : ℤ), (j : ℤ))) =
        φ ((i : ℤ), ((n + 1 : ℕ) : ℤ)) - φ ((i : ℤ), ((0 : ℕ) : ℤ)) := fun i =>
      Finset.sum_range_sub (fun j : ℕ => φ ((i : ℤ), (j : ℤ))) (n + 1)
    rw [Finset.sum_congr rfl fun i _ => ht i, ← hsum]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => h1 _ _)

variable {S : Type} [MeasurableSpace S]

/-- The Cesàro average `μ_n = |B_n|⁻¹ ∑_{a ∈ B_n} T_a μ`. -/
def avgMeasure (μ : Measure (Config S)) (n : ℕ) : Measure (Config S) :=
  ((avgBox n).card : ℝ≥0∞)⁻¹ • ∑ a ∈ avgBox n, μ.map (shift a)

/-- The box averages `A_n = |B_n|⁻¹ ∑_{a ∈ B_n} ∫ f ∘ T_a dμ`. -/
def boxAvg (μ : Measure (Config S)) (f : Config S → ℝ) (n : ℕ) : ℝ :=
  ((avgBox n).card : ℝ)⁻¹ * ∑ a ∈ avgBox n, ∫ ω, f (shift a ω) ∂μ

/-- `μ_n` is a probability measure. -/
theorem isProbabilityMeasure_avgMeasure (μ : Measure (Config S)) [IsProbabilityMeasure μ]
    (n : ℕ) : IsProbabilityMeasure (avgMeasure μ n) := by
  constructor
  have hc0 : ((avgBox n).card : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 (avgBox_nonempty n).card_pos.ne'
  have h1 : ∀ a ∈ avgBox n, μ.map (shift a) Set.univ = 1 := fun a _ => by
    rw [Measure.map_apply (measurable_shiftConfig a) MeasurableSet.univ, Set.preimage_univ,
      measure_univ]
  rw [avgMeasure, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply,
    Finset.sum_congr rfl h1, smul_eq_mul, Finset.sum_const, nsmul_eq_mul, mul_one]
  exact ENNReal.inv_mul_cancel hc0 (ENNReal.natCast_ne_top _)

/-- The Cesàro averages as points of the space of probability measures. -/
def avgPM (μ : Measure (Config S)) (hμ : IsProbabilityMeasure μ) (n : ℕ) :
    ProbabilityMeasure (Config S) :=
  ⟨avgMeasure μ n, isProbabilityMeasure_avgMeasure μ n⟩

/-- `∫ f dμ_n = A_n` for bounded measurable `f`. -/
theorem integral_avgMeasure (μ : Measure (Config S)) [IsProbabilityMeasure μ] (n : ℕ)
    {f : Config S → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ ω, |f ω| ≤ C) :
    ∫ ω, f ω ∂(avgMeasure μ n) = boxAvg μ f n := by
  have hint : ∀ a ∈ avgBox n, Integrable f (μ.map (shift a)) := fun a _ => by
    haveI := (Measure.isProbabilityMeasure_map_iff (μ := μ) (measurable_shiftConfig a).aemeasurable).2 inferInstance
    exact Integrable.of_bound hf.aestronglyMeasurable C
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hC ω)
  rw [avgMeasure, integral_smul_measure, integral_finsetSum_measure hint, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, smul_eq_mul, boxAvg]
  congr 1
  exact Finset.sum_congr rfl fun a _ =>
    integral_map (measurable_shiftConfig a).aemeasurable hf.aestronglyMeasurable

/-- The mass of a measurable set under `μ_n`. -/
theorem measureReal_avgMeasure (μ : Measure (Config S)) [IsProbabilityMeasure μ] (n : ℕ)
    {s : Set (Config S)} (hs : MeasurableSet s) :
    (avgMeasure μ n).real s = ((avgBox n).card : ℝ)⁻¹ * ∑ a ∈ avgBox n, μ.real (shift a ⁻¹' s) := by
  have h : ∀ a ∈ avgBox n, μ.map (shift a) s = μ (shift a ⁻¹' s) := fun a _ =>
    Measure.map_apply (measurable_shiftConfig a) hs
  rw [measureReal_def, avgMeasure, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply,
    Finset.sum_congr rfl h, smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, ENNReal.toReal_sum fun a _ => measure_ne_top μ _]
  rfl

/-- **Almost invariance of the Cesàro averages**: for `a = e₁, e₂` and measurable `s`,
`|μ_n(T_a⁻¹ s) - μ_n(s)| ≤ 1 / (n + 1)`. -/
theorem abs_avgMeasure_shift_sub_le (μ : Measure (Config S)) [IsProbabilityMeasure μ] (n : ℕ)
    {s : Set (Config S)} (hs : MeasurableSet s) {a : Plane} (ha : a = e1 ∨ a = e2) :
    |(avgMeasure μ n).real (shift a ⁻¹' s) - (avgMeasure μ n).real s| ≤ 1 / ((n : ℝ) + 1) := by
  have hs' : MeasurableSet (shift a ⁻¹' s) := measurable_shiftConfig a hs
  rw [measureReal_avgMeasure μ n hs', measureReal_avgMeasure μ n hs]
  have hpre : ∀ c : Plane, shift c ⁻¹' (shift a ⁻¹' s) = shift (a + c) ⁻¹' s := fun c => by
    ext ω
    simp only [Set.mem_preimage, shift_shift]
  simp only [hpre]
  have hcard : ((avgBox n).card : ℝ) = ((n : ℝ) + 1) ^ 2 := by
    rw [card_avgBox]; push_cast; ring
  have hb := abs_sum_avgBox_shift_sub_le n (fun c => μ.real (shift c ⁻¹' s))
    (fun c => ⟨measureReal_nonneg, measureReal_le_one⟩) ha
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [← mul_sub, abs_mul, abs_of_pos (inv_pos.2 (by rw [hcard]; positivity)), hcard]
  calc (((n : ℝ) + 1) ^ 2)⁻¹ * |∑ c ∈ avgBox n, μ.real (shift (a + c) ⁻¹' s) -
        ∑ c ∈ avgBox n, μ.real (shift c ⁻¹' s)|
      ≤ (((n : ℝ) + 1) ^ 2)⁻¹ * ((n : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = 1 / ((n : ℝ) + 1) := by field_simp

/-- If every translate has `∫ f ∘ T_a dμ ≥ c`, so does every box average. -/
theorem le_boxAvg (μ : Measure (Config S)) (f : Config S → ℝ) {c : ℝ}
    (h : ∀ a, c ≤ ∫ ω, f (shift a ω) ∂μ) (n : ℕ) : c ≤ boxAvg μ f n := by
  have hpos : (0 : ℝ) < (avgBox n).card := by exact_mod_cast (avgBox_nonempty n).card_pos
  rw [boxAvg, le_inv_mul_iff₀ hpos]
  calc ((avgBox n).card : ℝ) * c = ∑ _a ∈ avgBox n, c := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ a ∈ avgBox n, ∫ ω, f (shift a ω) ∂μ := Finset.sum_le_sum fun a _ => h a

/-- If every translate has `∫ f ∘ T_a dμ ≤ c`, so does every box average. -/
theorem boxAvg_le (μ : Measure (Config S)) (f : Config S → ℝ) {c : ℝ}
    (h : ∀ a, ∫ ω, f (shift a ω) ∂μ ≤ c) (n : ℕ) : boxAvg μ f n ≤ c := by
  have hpos : (0 : ℝ) < (avgBox n).card := by exact_mod_cast (avgBox_nonempty n).card_pos
  rw [boxAvg, inv_mul_le_iff₀ hpos]
  calc ∑ a ∈ avgBox n, ∫ ω, f (shift a ω) ∂μ ≤ ∑ _a ∈ avgBox n, c :=
        Finset.sum_le_sum fun a _ => h a
    _ =((avgBox n).card : ℝ) * c := by rw [Finset.sum_const, nsmul_eq_mul]

end Box

/-- **The Cesàro averages of a Gibbs measure are Gibbs** (translation-invariant `Φ`). -/
theorem isGibbs_avgMeasure {S : Type} [Fintype S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
    {Φ : Interaction S} (hΦ : IsInteraction Φ) (hti : IsTranslationInvariant Φ) {β : ℝ}
    {μ : Measure (Config S)} (hμ : IsGibbs β Φ μ) (n : ℕ) : IsGibbs β Φ (avgMeasure μ n) :=
  isGibbs_finsetAvg hΦ (avgBox n) (avgBox_nonempty n) _ fun a _ => isGibbs_map_shift hΦ hti hμ a

/-! ## Cluster points of the Cesàro averages -/

/-- A cluster point of a sequence satisfies every closed condition that the sequence satisfies
eventually. -/
theorem mem_of_clusterPt {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {x : X}
    {P : ℕ → X} (hx : ClusterPt x (map P atTop)) {Ψ : X → Y} (hΨ : Continuous Ψ) {C : Set Y}
    (hC : IsClosed C) (hev : ∀ᶠ n in atTop, Ψ (P n) ∈ C) : Ψ x ∈ C := by
  have h := clusterPt_iff_forall_mem_closure.1 hx (Ψ ⁻¹' C) hev
  rwa [(hC.preimage hΨ).closure_eq] at h


/-- An elementary cylinder depends only on the sites of its base. -/
theorem cyl_local {S : Type} (J : Finset Plane) (b : Config S) :
    ∀ ω ω' : Config S, (∀ ξ ∈ J, ω ξ = ω' ξ) → (ω ∈ cyl J b ↔ ω' ∈ cyl J b) := by
  intro ω ω' h
  simp only [mem_cyl]
  exact ⟨fun hω i hi => (h i hi).symm.trans (hω i hi), fun hω i hi => (h i hi).trans (hω i hi)⟩

section Limit

variable {S : Type} [Fintype S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  [TopologicalSpace S] [DiscreteTopology S] [BorelSpace S]

omit [Fintype S] [MeasurableSpace S] [DiscreteMeasurableSpace S] [BorelSpace S] in
/-- A function of finitely many sites is continuous. -/
theorem continuous_of_local (D : Finset Plane) (f : Config S → ℝ)
    (hf : ∀ ω ω' : Config S, (∀ ξ ∈ D, ω ξ = ω' ξ) → f ω = f ω') : Continuous f :=
  WeightSystem.continuous_of_dependsOn D f hf

omit [DiscreteMeasurableSpace S] in
/-- `m ↦ ∫ g dm` is continuous on the probability measures for continuous `g` (`Config S` is
compact, so `g` is bounded). -/
theorem continuous_integral_of_continuous {g : Config S → ℝ} (hg : Continuous g) :
    Continuous fun m : ProbabilityMeasure (Config S) => ∫ ω, g ω ∂(m : Measure (Config S)) :=
  ProbabilityMeasure.continuous_integral_boundedContinuousFunction
    (BoundedContinuousFunction.mkOfCompact ⟨g, hg⟩)

/-- The mass of an event that depends on finitely many sites is a continuous function of the
probability measure. -/
theorem continuous_measureReal_of_local (D : Finset Plane) (s : Set (Config S))
    (hs : ∀ ω ω' : Config S, (∀ ξ ∈ D, ω ξ = ω' ξ) → (ω ∈ s ↔ ω' ∈ s)) :
    Continuous fun m : ProbabilityMeasure (Config S) => (m : Measure (Config S)).real s := by
  have hloc : ∀ ω ω' : Config S, (∀ ξ ∈ D, ω ξ = ω' ξ) →
      s.indicator (1 : Config S → ℝ) ω = s.indicator 1 ω' := by
    intro ω ω' h
    by_cases hω : ω ∈ s
    · simp [Set.indicator, hω, (hs ω ω' h).1 hω]
    · simp [Set.indicator, hω, mt (hs ω ω' h).2 hω]
  have hm : MeasurableSet s := measurableSet_of_dependsOn D s hs
  have e : (fun m : ProbabilityMeasure (Config S) => (m : Measure (Config S)).real s) =
      fun m : ProbabilityMeasure (Config S) =>
        ∫ ω, s.indicator (1 : Config S → ℝ) ω ∂(m : Measure (Config S)) := by
    funext m
    exact (integral_indicator_one hm).symm
  rw [e]
  exact continuous_integral_of_continuous (continuous_of_local D _ hloc)

/-- **The Gibbs measures of a nearest-neighbour `Φ` are closed**: a cluster point of a sequence of
Gibbs measures is Gibbs. `X_Φ` is an intersection of events `{Φ_A < ∞}` that depend on finitely
many sites, and the Gibbs property is detailed balance on elementary cylinders
(`HardWeightSystem.isGibbs_of_db`), finitely many cylinder masses at a time. -/
theorem isGibbs_of_clusterPt {Φ : Interaction S} (hΦ : IsInteraction Φ)
    (hnn : IsNearestNeighbour Φ) {β : ℝ} {P : ℕ → ProbabilityMeasure (Config S)}
    (hP : ∀ n, IsGibbs β Φ (P n : Measure (Config S))) {ν : ProbabilityMeasure (Config S)}
    (hν : ClusterPt ν (map P atTop)) : IsGibbs β Φ (ν : Measure (Config S)) := by
  classical
  -- `ν(X_Φ) = 1`: each `{Φ_A < ∞}` is a local event of mass one under every `P n`
  have hA : ∀ A : Finset Plane, ∀ᵐ ω ∂(ν : Measure (Config S)), Φ A ω < ⊤ := by
    intro A
    have hloc : ∀ ω ω' : Config S, (∀ ξ ∈ A, ω ξ = ω' ξ) →
        (ω ∈ {ω : Config S | Φ A ω < ⊤} ↔ ω' ∈ {ω : Config S | Φ A ω < ⊤}) := by
      intro ω ω' h
      simp only [Set.mem_setOf_eq, hΦ A ω ω' h]
    have hmA : MeasurableSet {ω : Config S | Φ A ω < ⊤} :=
      measurableSet_lt (measurable_interaction hΦ A) measurable_const
    have h1 : (ν : Measure (Config S)).real {ω | Φ A ω < ⊤} = 1 := by
      refine mem_of_clusterPt hν (continuous_measureReal_of_local A _ hloc) isClosed_singleton
        (Eventually.of_forall fun n => ?_)
      have hsub : {ω : Config S | IsLegal Φ ω} ⊆ {ω | Φ A ω < ⊤} := fun ω hω => hω A
      have hn : (P n : Measure (Config S)) {ω | Φ A ω < ⊤} = 1 :=
        le_antisymm prob_le_one ((hP n).2.1 ▸ measure_mono hsub)
      show (P n : Measure (Config S)).real {ω | Φ A ω < ⊤} = 1
      rw [measureReal_def, hn, ENNReal.toReal_one]
    rw [measureReal_def, ENNReal.toReal_eq_one_iff] at h1
    exact (ae_iff_measure_eq hmA.nullMeasurableSet).2 (by rw [h1, measure_univ])
  have hlegal : ∀ᵐ ω ∂(ν : Measure (Config S)), IsLegal Φ ω := ae_all_iff.2 hA
  -- detailed balance on the elementary cylinders passes to the limit
  set ws := siteSystem β Φ hΦ hnn with hws
  have hdb : ∀ S₀ J : Finset Plane, S₀ ⊆ J → ws.range S₀ ⊆ J →
      ws.DB (ν : Measure (Config S)) S₀ J := by
    intro S₀ J hS hr a a' h
    have hc : ∀ b : Config S, Continuous fun m : ProbabilityMeasure (Config S) =>
        (m : Measure (Config S)).real (cyl J b) := fun b =>
      continuous_measureReal_of_local J _ (cyl_local J b)
    have hΨ : Continuous fun m : ProbabilityMeasure (Config S) =>
        (m : Measure (Config S)).real (cyl J a) * ws.W S₀ a' -
          (m : Measure (Config S)).real (cyl J a') * ws.W S₀ a :=
      ((hc a).mul continuous_const).sub ((hc a').mul continuous_const)
    have key := mem_of_clusterPt hν hΨ (isClosed_singleton (x := (0 : ℝ)))
      (Eventually.of_forall fun n => by
        have := ws.db_of_isGibbs ((isGibbs_iff β hΦ hnn _).1 (hP n)) hS hr a a' h
        show _ - _ = (0 : ℝ)
        rw [this, sub_self])
    exact sub_eq_zero.1 (Set.mem_singleton_iff.1 key)
  have hν' : ws.IsGibbs (ν : Measure (Config S)) := by
    refine ws.isGibbs_of_db (hlegal.mono fun ω hω => (isLegal_iff β hΦ hnn ω).1 hω)
      fun S₀ => ⟨S₀, subset_rfl, fun J₀ => ⟨J₀ ∪ S₀ ∪ ws.range S₀, ?_, ?_, ?_,
        hdb _ _ ?_ ?_⟩⟩
    · exact Finset.subset_union_left.trans Finset.subset_union_left
    · exact Finset.subset_union_right.trans Finset.subset_union_left
    · exact Finset.subset_union_right
    · exact Finset.subset_union_right.trans Finset.subset_union_left
    · exact Finset.subset_union_right
  exact (isGibbs_iff β hΦ hnn _).2 hν'

/-- **A cluster point of the Cesàro averages is translation invariant**: `T_a μ_n - μ_n` is of
order `1 / n` on every event, for `a = e₁, e₂`. -/
theorem isTranslationInvariantMeasure_of_clusterPt (μ : Measure (Config S))
    (hμ : IsProbabilityMeasure μ) {ν : ProbabilityMeasure (Config S)}
    (hν : ClusterPt ν (map (avgPM μ hμ) atTop)) :
    IsTranslationInvariantMeasure (ν : Measure (Config S)) := by
  have key : ∀ a : Plane, a = e1 ∨ a = e2 → (ν : Measure (Config S)).map (shift a) = ν := by
    intro a ha
    refine ext_cyl fun J b => ?_
    have hs : MeasurableSet (cyl J b) := measurableSet_cyl J b
    rw [Measure.map_apply (measurable_shiftConfig a) hs]
    have hls' : ∀ ω ω' : Config S, (∀ ξ ∈ J.image (fun x => x - a), ω ξ = ω' ξ) →
        (ω ∈ shift a ⁻¹' cyl J b ↔ ω' ∈ shift a ⁻¹' cyl J b) := by
      intro ω ω' h
      exact cyl_local J b _ _ fun ξ hξ => h (ξ - a) (Finset.mem_image_of_mem _ hξ)
    have hcont := (continuous_measureReal_of_local _ _ hls').sub
      (continuous_measureReal_of_local J _ (cyl_local J b))
    have hε : ∀ ε : ℝ, 0 < ε → |(ν : Measure (Config S)).real (shift a ⁻¹' cyl J b) -
        (ν : Measure (Config S)).real (cyl J b)| ≤ ε := by
      intro ε hε
      obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
      refine mem_of_clusterPt hν hcont (C := {x : ℝ | |x| ≤ ε})
        (isClosed_le continuous_abs continuous_const) ?_
      filter_upwards [eventually_ge_atTop N] with n hn
      show |(avgMeasure μ n).real (shift a ⁻¹' cyl J b) - (avgMeasure μ n).real (cyl J b)| ≤ ε
      refine (abs_avgMeasure_shift_sub_le μ n hs ha).trans (le_trans ?_ hN.le)
      have hNn : (N : ℝ) ≤ n := Nat.cast_le.2 hn
      exact one_div_le_one_div_of_le (by positivity) (by linarith)
    have h0 : (ν : Measure (Config S)).real (shift a ⁻¹' cyl J b) =
        (ν : Measure (Config S)).real (cyl J b) := by
      by_contra hne
      have hp := abs_pos.2 (sub_ne_zero.2 hne)
      have := hε _ (half_pos hp)
      linarith
    rwa [measureReal_def, measureReal_def, ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _)
      (measure_ne_top _ _)] at h0
  exact isTranslationInvariantMeasure_of_e1_e2 (key e1 (Or.inl rfl)) (key e2 (Or.inr rfl))

/-! ## Krylov–Bogolyubov -/

omit [DiscreteMeasurableSpace S] in
/-- A continuous function on the compact space `Config S` is measurable and bounded. -/
theorem bounded_of_continuous {f : Config S → ℝ} (hf : Continuous f) :
    Measurable f ∧ ∃ C : ℝ, ∀ ω, |f ω| ≤ C :=
  ⟨hf.measurable, ‖BoundedContinuousFunction.mkOfCompact ⟨f, hf⟩‖, fun ω => by
    rw [← Real.norm_eq_abs]
    exact (BoundedContinuousFunction.mkOfCompact ⟨f, hf⟩).norm_coe_le_norm ω⟩

/-- **Krylov–Bogolyubov for Gibbs measures.** Let `Φ` be a nearest-neighbour, translation-invariant
interaction, `μ` a Gibbs measure for `βΦ` and `f` continuous. A cluster point `μ̄` of the Cesàro
averages `μ_n = |B_n|⁻¹ ∑_{a ∈ B_n} T_a μ` is a translation-invariant Gibbs measure for `βΦ`, and
`∫ f dμ̄` is a cluster value of the box averages `A_n = |B_n|⁻¹ ∑_{a ∈ B_n} ∫ f ∘ T_a dμ`: it lies
in every closed set that eventually contains `A_n`. -/
theorem exists_ti_gibbs_avg_of_continuous {Φ : Interaction S} (hΦ : IsInteraction Φ)
    (hnn : IsNearestNeighbour Φ) (hti : IsTranslationInvariant Φ) {β : ℝ}
    {μ : Measure (Config S)} (hμ : IsGibbs β Φ μ) {f : Config S → ℝ} (hf : Continuous f) :
    ∃ μbar : Measure (Config S), IsGibbs β Φ μbar ∧ IsTranslationInvariantMeasure μbar ∧
      ∀ C : Set ℝ, IsClosed C → (∀ᶠ n in atTop, boxAvg μ f n ∈ C) →
        ∫ ω, f ω ∂μbar ∈ C := by
  haveI := hμ.1
  obtain ⟨hfm, Cf, hCf⟩ := bounded_of_continuous hf
  obtain ⟨ν, hν⟩ := exists_clusterPt_of_compactSpace (map (avgPM μ hμ.1) atTop)
  refine ⟨ν, isGibbs_of_clusterPt hΦ hnn (fun n => isGibbs_avgMeasure hΦ hti hμ n) hν,
    isTranslationInvariantMeasure_of_clusterPt μ hμ.1 hν, fun C hC hev => ?_⟩
  refine mem_of_clusterPt hν (continuous_integral_of_continuous hf) hC ?_
  filter_upwards [hev] with n hn
  show ∫ ω, f ω ∂(avgMeasure μ n) ∈ C
  rwa [integral_avgMeasure μ n hfm hCf]

/-- **Krylov–Bogolyubov for two Gibbs measures at once** (a joint cluster point): for Gibbs
measures `μ₁`, `μ₂` and continuous `f₁`, `f₂` there are translation-invariant Gibbs measures
`μ̄₁`, `μ̄₂` such that `(∫ f₁ dμ̄₁, ∫ f₂ dμ̄₂)` lies in every closed set of `ℝ²` that eventually
contains `(A_n(μ₁, f₁), A_n(μ₂, f₂))`. -/
theorem exists_ti_gibbs_avg₂_of_continuous {Φ : Interaction S} (hΦ : IsInteraction Φ)
    (hnn : IsNearestNeighbour Φ) (hti : IsTranslationInvariant Φ) {β : ℝ}
    {μ₁ μ₂ : Measure (Config S)} (hμ₁ : IsGibbs β Φ μ₁) (hμ₂ : IsGibbs β Φ μ₂)
    {f₁ f₂ : Config S → ℝ} (hf₁ : Continuous f₁) (hf₂ : Continuous f₂) :
    ∃ μbar₁ μbar₂ : Measure (Config S),
      IsGibbs β Φ μbar₁ ∧ IsTranslationInvariantMeasure μbar₁ ∧
      IsGibbs β Φ μbar₂ ∧ IsTranslationInvariantMeasure μbar₂ ∧
      ∀ C : Set (ℝ × ℝ), IsClosed C →
        (∀ᶠ n in atTop, (boxAvg μ₁ f₁ n, boxAvg μ₂ f₂ n) ∈ C) →
          (∫ ω, f₁ ω ∂μbar₁, ∫ ω, f₂ ω ∂μbar₂) ∈ C := by
  haveI := hμ₁.1
  haveI := hμ₂.1
  obtain ⟨hfm₁, C₁, hC₁⟩ := bounded_of_continuous hf₁
  obtain ⟨hfm₂, C₂, hC₂⟩ := bounded_of_continuous hf₂
  obtain ⟨⟨ν₁, ν₂⟩, hν⟩ := exists_clusterPt_of_compactSpace
    (map (fun n => (avgPM μ₁ hμ₁.1 n, avgPM μ₂ hμ₂.1 n)) atTop)
  have hν₁ : ClusterPt ν₁ (map (avgPM μ₁ hμ₁.1) atTop) :=
    hν.map continuous_fst.continuousAt (tendsto_map'_iff.2 tendsto_map)
  have hν₂ : ClusterPt ν₂ (map (avgPM μ₂ hμ₂.1) atTop) :=
    hν.map continuous_snd.continuousAt (tendsto_map'_iff.2 tendsto_map)
  refine ⟨ν₁, ν₂, isGibbs_of_clusterPt hΦ hnn (fun n => isGibbs_avgMeasure hΦ hti hμ₁ n) hν₁,
    isTranslationInvariantMeasure_of_clusterPt μ₁ hμ₁.1 hν₁,
    isGibbs_of_clusterPt hΦ hnn (fun n => isGibbs_avgMeasure hΦ hti hμ₂ n) hν₂,
    isTranslationInvariantMeasure_of_clusterPt μ₂ hμ₂.1 hν₂, fun C hC hev => ?_⟩
  have hΨ : Continuous fun m : ProbabilityMeasure (Config S) × ProbabilityMeasure (Config S) =>
      (∫ ω, f₁ ω ∂(m.1 : Measure (Config S)), ∫ ω, f₂ ω ∂(m.2 : Measure (Config S))) :=
    ((continuous_integral_of_continuous hf₁).comp continuous_fst).prodMk
      ((continuous_integral_of_continuous hf₂).comp continuous_snd)
  refine mem_of_clusterPt hν hΨ hC ?_
  filter_upwards [hev] with n hn
  show (∫ ω, f₁ ω ∂(avgMeasure μ₁ n), ∫ ω, f₂ ω ∂(avgMeasure μ₂ n)) ∈ C
  rwa [integral_avgMeasure μ₁ n hfm₁ hC₁, integral_avgMeasure μ₂ n hfm₂ hC₂]

/-- **Krylov–Bogolyubov, local form** (`f` depends on the finitely many sites in `D`): there is a
translation-invariant Gibbs measure `μ̄` for `βΦ` such that `∫ f dμ̄` is a cluster value of the box
averages `A_n`; in particular every eventual lower (upper) bound of `A_n` bounds `∫ f dμ̄`. -/
theorem exists_ti_gibbs_avg {Φ : Interaction S} (hΦ : IsInteraction Φ)
    (hnn : IsNearestNeighbour Φ) (hti : IsTranslationInvariant Φ) {β : ℝ}
    {μ : Measure (Config S)} (hμ : IsGibbs β Φ μ) (D : Finset Plane) {f : Config S → ℝ}
    (hf : ∀ ω ω' : Config S, (∀ ξ ∈ D, ω ξ = ω' ξ) → f ω = f ω') :
    ∃ μbar : Measure (Config S), IsGibbs β Φ μbar ∧ IsTranslationInvariantMeasure μbar ∧
      (∀ C : Set ℝ, IsClosed C → (∀ᶠ n in atTop, boxAvg μ f n ∈ C) →
        ∫ ω, f ω ∂μbar ∈ C) ∧
      (∀ c : ℝ, (∀ᶠ n in atTop, c ≤ boxAvg μ f n) → c ≤ ∫ ω, f ω ∂μbar) ∧
      (∀ c : ℝ, (∀ᶠ n in atTop, boxAvg μ f n ≤ c) → ∫ ω, f ω ∂μbar ≤ c) := by
  obtain ⟨μbar, hG, hT, hC⟩ :=
    exists_ti_gibbs_avg_of_continuous hΦ hnn hti hμ (continuous_of_local D f hf)
  exact ⟨μbar, hG, hT, hC, fun c h => hC (Set.Ici c) isClosed_Ici h,
    fun c h => hC (Set.Iic c) isClosed_Iic h⟩

/-- **Krylov–Bogolyubov for two Gibbs measures at once, local form** (`f₁`, `f₂` depend on the
finitely many sites in `D`). -/
theorem exists_ti_gibbs_avg₂ {Φ : Interaction S} (hΦ : IsInteraction Φ)
    (hnn : IsNearestNeighbour Φ) (hti : IsTranslationInvariant Φ) {β : ℝ}
    {μ₁ μ₂ : Measure (Config S)} (hμ₁ : IsGibbs β Φ μ₁) (hμ₂ : IsGibbs β Φ μ₂) (D : Finset Plane)
    {f₁ f₂ : Config S → ℝ} (hf₁ : ∀ ω ω' : Config S, (∀ ξ ∈ D, ω ξ = ω' ξ) → f₁ ω = f₁ ω')
    (hf₂ : ∀ ω ω' : Config S, (∀ ξ ∈ D, ω ξ = ω' ξ) → f₂ ω = f₂ ω') :
    ∃ μbar₁ μbar₂ : Measure (Config S),
      IsGibbs β Φ μbar₁ ∧ IsTranslationInvariantMeasure μbar₁ ∧
      IsGibbs β Φ μbar₂ ∧ IsTranslationInvariantMeasure μbar₂ ∧
      ∀ C : Set (ℝ × ℝ), IsClosed C →
        (∀ᶠ n in atTop, (boxAvg μ₁ f₁ n, boxAvg μ₂ f₂ n) ∈ C) →
          (∫ ω, f₁ ω ∂μbar₁, ∫ ω, f₂ ω ∂μbar₂) ∈ C :=
  exists_ti_gibbs_avg₂_of_continuous hΦ hnn hti hμ₁ hμ₂ (continuous_of_local D f₁ hf₁)
    (continuous_of_local D f₂ hf₂)

/-- **Existence of a translation-invariant Gibbs measure** for `βΦ` (nearest-neighbour,
translation-invariant `Φ`), given any Gibbs measure. -/
theorem exists_ti_gibbs {Φ : Interaction S} (hΦ : IsInteraction Φ) (hnn : IsNearestNeighbour Φ)
    (hti : IsTranslationInvariant Φ) {β : ℝ} {μ : Measure (Config S)} (hμ : IsGibbs β Φ μ) :
    ∃ μbar : Measure (Config S), IsGibbs β Φ μbar ∧ IsTranslationInvariantMeasure μbar := by
  obtain ⟨μbar, hG, hT, -⟩ :=
    exists_ti_gibbs_avg_of_continuous hΦ hnn hti hμ (f := fun _ => (0 : ℝ)) continuous_const
  exact ⟨μbar, hG, hT⟩

end Limit

--PART2

end Gibbs

end UPD

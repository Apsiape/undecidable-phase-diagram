/-
# Comparing two hard-constraint systems through their supports and weight ratios

New in this project (session 10). `pay:factor`(b) says that the frozen kernels are the kernels of
another factor system: the two weights agree "up to factors that do not involve the coordinates at
the sites of `Λ`; these cancel in the kernel". In Lean: two hard-constraint weight systems on
index sets related by an equivalence `e : I ≃ I'` have the same Gibbs measures (transported along
`x ↦ x ∘ e.symm`) if

* they have the same configurations with all weights positive (`Pos`), and
* at such configurations, a change inside a finite `Λ` that keeps all weights positive changes
  the weights of `Λ` and of `e(Λ)` by the same factor.

* `pos_of_pos`: a configuration that differs from a positive one inside `Λ` and has positive
  weight for `Λ` is positive.
* `expect_eq_of_ratio`: the kernels of `Λ` and `e(Λ)` agree at positive configurations.
* **`isGibbs_iff_of_ratio`**.
-/
import UndecidablePhaseDiagram.Gibbs.Transport

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace UPD

namespace Gibbs

namespace HardWeightSystem

variable {I E : Type} [DecidableEq I] [Fintype E] (ws : HardWeightSystem I E)

/-- All weights are positive at `x`. -/
def Pos (x : I → E) : Prop := ∀ Λ : Finset I, 0 < ws.W Λ x

/-- A configuration that differs from a positive one only inside `Λ`, with positive weight for
`Λ`, is positive (ratio and support properties). -/
theorem pos_of_pos {x y : I → E} (hx : ws.Pos x) {Λ : Finset I}
    (hy : ∀ i, i ∉ Λ → y i = x i) (h : 0 < ws.W Λ y) : ws.Pos y := by
  intro Δ
  have hr := ws.ratio Λ (Δ ∪ Λ) Finset.subset_union_right y x hy
  have h1 : 0 < ws.W (Δ ∪ Λ) y := by
    have hp : 0 < ws.W (Δ ∪ Λ) x * ws.W Λ y := mul_pos (hx _) h
    rw [← hr] at hp
    refine lt_of_le_of_ne (ws.nonneg _ _) fun h0 => ?_
    rw [← h0, zero_mul] at hp
    exact lt_irrefl 0 hp
  refine lt_of_le_of_ne (ws.nonneg _ _) fun h0 => ?_
  have := ws.support Δ (Δ ∪ Λ) Finset.subset_union_left y h0.symm
  rw [this] at h1
  exact lt_irrefl 0 h1

variable {I' : Type} [DecidableEq I'] (ws' : HardWeightSystem I' E) (e : I ≃ I')

/-- The image of a finite set under the equivalence, as an equivalence of its elements. -/
def mapEquiv (Λ : Finset I) : Λ ≃ Λ.map e.toEmbedding where
  toFun i := ⟨e i.1, Finset.mem_map_of_mem _ i.2⟩
  invFun i' := ⟨e.symm i'.1, by
    obtain ⟨i, hi, h⟩ := Finset.mem_map.1 i'.2
    rw [← h]; simpa using hi⟩
  left_inv i := by simp
  right_inv i' := by simp

theorem fillOn_map (x : I → E) (Λ : Finset I) (ζ' : Λ.map e.toEmbedding → E) :
    fillOn (fun i' => x (e.symm i')) (Λ.map e.toEmbedding) ζ' =
      fun i' => fillOn x Λ (fun i => ζ' (mapEquiv e Λ i)) (e.symm i') := by
  funext i'
  by_cases h : i' ∈ Λ.map e.toEmbedding
  · have h' : e.symm i' ∈ Λ := by
      obtain ⟨i, hi, hh⟩ := Finset.mem_map.1 h
      rw [← hh]; simpa using hi
    rw [fillOn_of_mem _ _ h, fillOn_of_mem _ _ h']
    congr 1
    exact Subtype.ext (by simp [mapEquiv])
  · have h' : e.symm i' ∉ Λ := fun hm => h (by
      rw [Finset.mem_map]; exact ⟨_, hm, by simp⟩)
    rw [fillOn_of_not_mem _ _ h, fillOn_of_not_mem _ _ h']

/-- **The kernels agree** at a positive configuration when the weight ratios agree. -/
theorem expect_eq_of_ratio
    (hpos : ∀ z : I → E, ws.Pos z ↔ ws'.Pos (fun i' => z (e.symm i')))
    {x : I → E} (hx : ws.Pos x) (Λ : Finset I)
    (hrat : ∀ y : I → E, ws.Pos y → (∀ i, i ∉ Λ → y i = x i) →
      ws.W Λ y * ws'.W (Λ.map e.toEmbedding) (fun i' => x (e.symm i')) =
        ws'.W (Λ.map e.toEmbedding) (fun i' => y (e.symm i')) * ws.W Λ x)
    (G : (I' → E) → ℝ) :
    ws'.expect (Λ.map e.toEmbedding) (fun i' => x (e.symm i')) G =
      ws.expect Λ x (fun y => G (fun i' => y (e.symm i'))) := by
  set Λ' := Λ.map e.toEmbedding
  have hx' : ws'.Pos (fun i' => x (e.symm i')) := (hpos x).1 hx
  have hWx := hx Λ
  have hWx' := hx' Λ'
  set c := ws'.W Λ' (fun i' => x (e.symm i')) / ws.W Λ x with hc
  have hcpos : 0 < c := div_pos hWx' hWx
  -- the weights of the fillings are proportional
  have hprop : ∀ ζ : Λ → E,
      ws'.W Λ' (fun i' => fillOn x Λ ζ (e.symm i')) = c * ws.W Λ (fillOn x Λ ζ) := by
    intro ζ
    have hy : ∀ i, i ∉ Λ → fillOn x Λ ζ i = x i := fun i hi => fillOn_of_not_mem _ _ hi
    by_cases h : 0 < ws.W Λ (fillOn x Λ ζ)
    · have hP := ws.pos_of_pos hx hy h
      have := hrat _ hP hy
      rw [hc]; field_simp; linarith
    · have h0 : ws.W Λ (fillOn x Λ ζ) = 0 := le_antisymm (not_lt.1 h) (ws.nonneg _ _)
      rw [h0, mul_zero]
      by_contra hne
      have hpos' : 0 < ws'.W Λ' (fun i' => fillOn x Λ ζ (e.symm i')) :=
        lt_of_le_of_ne (ws'.nonneg _ _) (Ne.symm hne)
      have hy' : ∀ i', i' ∉ Λ' → fillOn x Λ ζ (e.symm i') = x (e.symm i') := by
        intro i' hi'
        refine fillOn_of_not_mem _ _ fun hm => hi' ?_
        rw [Finset.mem_map]; exact ⟨_, hm, by simp⟩
      have hP' := ws'.pos_of_pos hx' hy' hpos'
      have hP := (hpos _).2 hP'
      exact h (hP Λ)
  -- reindex the fillings of `Λ'` by those of `Λ`
  have hre : ∀ F : (I' → E) → ℝ, ∑ ζ' : Λ' → E, F (fillOn (fun i' => x (e.symm i')) Λ' ζ') =
      ∑ ζ : Λ → E, F (fun i' => fillOn x Λ ζ (e.symm i')) := by
    intro F
    refine Fintype.sum_equiv ((mapEquiv e Λ).arrowCongr (Equiv.refl E)).symm _ _ fun ζ' => ?_
    rw [fillOn_map]
    congr 2
  unfold expect prob Z
  simp only [div_mul_eq_mul_div, ← Finset.sum_div]
  rw [hre (fun z => ws'.W Λ' z * G z), hre (fun z => ws'.W Λ' z)]
  simp only [hprop]
  rw [← Finset.mul_sum]
  simp only [mul_assoc]
  rw [← Finset.mul_sum, mul_div_mul_left _ _ hcpos.ne']

variable [MeasurableSpace E] [DiscreteMeasurableSpace E] [DecidableEq E]

theorem measurable_comp_equiv {α β : Type} (f : α ≃ β) :
    Measurable (fun (x : α → E) (b : β) => x (f.symm b)) :=
  Measurable.of_eval fun _ => measurable_pi_apply _

/-- **Same supports and weight ratios give the same Gibbs measures** (along `x ↦ x ∘ e.symm`). -/
theorem isGibbs_iff_of_ratio [Countable I] [Countable I']
    (hpos : ∀ z : I → E, ws.Pos z ↔ ws'.Pos (fun i' => z (e.symm i')))
    (hrat : ∀ x : I → E, ws.Pos x → ∀ (Λ : Finset I) (y : I → E), ws.Pos y →
      (∀ i, i ∉ Λ → y i = x i) →
      ws.W Λ y * ws'.W (Λ.map e.toEmbedding) (fun i' => x (e.symm i')) =
        ws'.W (Λ.map e.toEmbedding) (fun i' => y (e.symm i')) * ws.W Λ x)
    (μ : Measure (I → E)) :
    ws.IsGibbs μ ↔ ws'.IsGibbs (μ.map fun x i' => x (e.symm i')) := by
  have hf := measurable_comp_equiv (E := E) e
  have hg := measurable_comp_equiv (E := E) e.symm
  have hgf : ∀ x : I → E, (fun i => (fun i' => x (e.symm i')) (e.symm.symm i)) = x := by
    intro x; funext i; simp
  have hfg : ∀ x' : I' → E, (fun i' => (fun i => x' (e.symm.symm i)) (e.symm i')) = x' := by
    intro x'; funext i'; simp
  constructor
  · intro hμ
    refine HardWeightSystem.isGibbs_map ws ws' hf (A := {x | ws.Pos x})
      (fun x hx Λ' => (hpos x).1 hx Λ') (fun Λ' => ⟨Λ', Finset.Subset.refl _, Λ'.map e.symm.toEmbedding,
        fun x hx G => ?_⟩) hμ hμ.2.1
    have hΛ : (Λ'.map e.symm.toEmbedding).map e.toEmbedding = Λ' := by ext; simp
    have := expect_eq_of_ratio ws ws' e hpos hx (Λ'.map e.symm.toEmbedding)
      (fun y hy hyx => hrat x hx _ y hy hyx) G
    rw [hΛ] at this
    exact this
  · intro hμ'
    have key : ws.IsGibbs ((μ.map fun x i' => x (e.symm i')).map fun x' i => x' (e.symm.symm i)) := by
      refine HardWeightSystem.isGibbs_map ws' ws hg (A := {x' | ws'.Pos x'})
        (fun x' hx' Λ => (hpos _).2 (by rw [hfg]; exact hx') Λ)
        (fun Λ => ⟨Λ, Finset.Subset.refl _, Λ.map e.toEmbedding, fun x' hx' G => ?_⟩) hμ' hμ'.2.1
      have hx : ws.Pos (fun i => x' (e.symm.symm i)) := (hpos _).2 (by rw [hfg]; exact hx')
      have := expect_eq_of_ratio ws ws' e hpos hx Λ
        (fun y hy hyx => hrat _ hx _ y hy hyx) (fun z => G (fun i => z (e.symm.symm i)))
      rw [hfg] at this
      rw [this]
      simp only [hgf]
    rwa [Measure.map_map hg hf, show ((fun x' i => x' (e.symm.symm i)) ∘
      fun (x : I → E) i' => x (e.symm i')) = id from funext hgf, Measure.map_id] at key

end HardWeightSystem

end Gibbs

end UPD

/-
# Products of Gibbs measures over the components of a graph (`thm:main`, Step 3)

New in this project (BLUEPRINT C.2, item 3). The paper (proof of `thm:main`, Step 3): "A product of
Gibbs measures on the components of a graph is a Gibbs measure on the graph, because the kernel of
a finite set is the product of the kernels of its intersections with the components."

* `WeightSystem.expect_union`: the kernel of a union of non-interacting sets (disjoint, neither
  weight depending on the other set, weights multiplying) is the composition of their kernels;
  `expect_empty` (the kernel of `∅` is the identity), `abs_expect_le'`.
* Components: `IsingGraph.IsComponentMap c` (neighbours have the same label `c v`), the induced
  subgraph `IsingGraph.restrict c i` on the vertices with label `i`, configurations split and joined
  at a label (`splitAt`, `joinAt`, `lift`); `expect_lift`: the kernel of the induced subgraph is the
  kernel of the graph; `expect_label`: the kernel of a finite set is the composition of the kernels
  of its part with label `i` and of the rest.
* `dlr_component` (Fubini) and `isDLR_of_components` (induction on the number of vertices):
  a measure satisfying the DLR identity for finite sets inside single components satisfies it for
  all finite sets.
* **`isDLR_glue`**: the product `glue_* (⊗_i ν_i)` (`Measure.infinitePi`) of measures whose
  restrictions to the components are Gibbs measures of the induced subgraphs is a Gibbs measure of
  the graph; the components are independent under the product (`map_splitAt_glue`).
* `IsingGraph.Iso` (isomorphisms of Ising models) and **`Iso.isDLR_map`**: Gibbs measures are
  carried by isomorphisms (in Step 3, the plus and minus states of the square lattice are carried to
  the components of the depths `d ∈ 𝒟_n` by `m ↦ 𝐫_d(m)`).
-/
import UndecidablePhaseDiagram.Gibbs.Existence
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace UPD

namespace Gibbs

namespace WeightSystem

variable {I E : Type} [DecidableEq I] [Fintype E] (ws : WeightSystem I E)

omit [Fintype E] in
/-- Fillings of disjoint sets commute. -/
theorem fillOn_comm {Λ₁ Λ₂ : Finset I} (h : Disjoint Λ₁ Λ₂) (ω : I → E) (ζ₁ : Λ₁ → E)
    (ζ₂ : Λ₂ → E) : fillOn (fillOn ω Λ₁ ζ₁) Λ₂ ζ₂ = fillOn (fillOn ω Λ₂ ζ₂) Λ₁ ζ₁ := by
  funext i
  by_cases h1 : i ∈ Λ₁
  · have h2 : i ∉ Λ₂ := Finset.disjoint_left.1 h h1
    simp [fillOn, h1, h2]
  · by_cases h2 : i ∈ Λ₂ <;> simp [fillOn, h1, h2]

/-- The fillings of a disjoint union are the pairs of fillings. -/
def unionEquiv {Λ₁ Λ₂ : Finset I} (h : Disjoint Λ₁ Λ₂) :
    ((Λ₁ ∪ Λ₂ : Finset I) → E) ≃ (Λ₁ → E) × (Λ₂ → E) where
  toFun ζ := (fun x => ζ ⟨x.1, Finset.mem_union_left _ x.2⟩,
    fun x => ζ ⟨x.1, Finset.mem_union_right _ x.2⟩)
  invFun p := fun x => if hx : x.1 ∈ Λ₁ then p.1 ⟨x.1, hx⟩ else
    p.2 ⟨x.1, by have := x.2; simp only [Finset.mem_union] at this; tauto⟩
  left_inv ζ := by
    funext x
    by_cases hx : x.1 ∈ Λ₁ <;> simp [hx]
  right_inv p := by
    ext x
    · simp [x.2]
    · have hx : x.1 ∉ Λ₁ := Finset.disjoint_right.1 h x.2
      simp [hx]

omit [Fintype E] in
theorem fillOn_union {Λ₁ Λ₂ : Finset I} (h : Disjoint Λ₁ Λ₂) (ω : I → E)
    (ζ : (Λ₁ ∪ Λ₂ : Finset I) → E) :
    fillOn ω (Λ₁ ∪ Λ₂) ζ =
      fillOn (fillOn ω Λ₂ (unionEquiv h ζ).2) Λ₁ (unionEquiv h ζ).1 := by
  funext i
  by_cases h1 : i ∈ Λ₁
  · simp [fillOn, h1, unionEquiv]
  · by_cases h2 : i ∈ Λ₂
    · simp [fillOn, h1, h2, unionEquiv]
    · simp [fillOn, h1, h2]

/-- **The kernel of a union of non-interacting sets is the composition of their kernels**: if
`Λ₁, Λ₂` are disjoint, the weight of each depends on no coordinate of the other, and
`W_{Λ₁ ∪ Λ₂} = W_{Λ₁} W_{Λ₂}`, then `γ_{Λ₁ ∪ Λ₂} F = γ_{Λ₁}(γ_{Λ₂} F)`. -/
theorem expect_union {Λ₁ Λ₂ : Finset I} (h : Disjoint Λ₁ Λ₂)
    (hr1 : Disjoint (ws.range Λ₁) Λ₂) (hr2 : Disjoint (ws.range Λ₂) Λ₁)
    (hW : ∀ σ, ws.W (Λ₁ ∪ Λ₂) σ = ws.W Λ₁ σ * ws.W Λ₂ σ) (ω : I → E)
    (F : (I → E) → ℝ) :
    ws.expect (Λ₁ ∪ Λ₂) ω F = ws.expect Λ₁ ω (fun ω' => ws.expect Λ₂ ω' F) := by
  -- the weight of `Λ₁` ignores the filling of `Λ₂`, and conversely
  have f1 : ∀ (ω' : I → E) (ζ₁ : Λ₁ → E) (ζ₂ : Λ₂ → E),
      ws.W Λ₁ (fillOn (fillOn ω' Λ₂ ζ₂) Λ₁ ζ₁) = ws.W Λ₁ (fillOn ω' Λ₁ ζ₁) := by
    intro ω' ζ₁ ζ₂
    refine ws.isLocal _ _ _ (fun i hi => ?_)
    have : i ∉ Λ₂ := Finset.disjoint_left.1 hr1 hi
    by_cases h1 : i ∈ Λ₁ <;> simp [fillOn, h1, this]
  have f2 : ∀ (ω' : I → E) (ζ₁ : Λ₁ → E) (ζ₂ : Λ₂ → E),
      ws.W Λ₂ (fillOn (fillOn ω' Λ₁ ζ₁) Λ₂ ζ₂) = ws.W Λ₂ (fillOn ω' Λ₂ ζ₂) := by
    intro ω' ζ₁ ζ₂
    refine ws.isLocal _ _ _ (fun i hi => ?_)
    have : i ∉ Λ₁ := Finset.disjoint_left.1 hr2 hi
    by_cases h2 : i ∈ Λ₂ <;> simp [fillOn, h2, this]
  have fZ : ∀ ζ₁ : Λ₁ → E, ws.Z Λ₂ (fillOn ω Λ₁ ζ₁) = ws.Z Λ₂ ω := by
    intro ζ₁
    simp only [Z, f2]
  have hZ : ws.Z (Λ₁ ∪ Λ₂) ω = ws.Z Λ₁ ω * ws.Z Λ₂ ω := by
    simp only [Z]
    rw [← Fintype.sum_equiv (unionEquiv h).symm (fun p : (Λ₁ → E) × (Λ₂ → E) =>
      ws.W (Λ₁ ∪ Λ₂) (fillOn ω (Λ₁ ∪ Λ₂) ((unionEquiv h).symm p))) _ (fun _ => rfl)]
    rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun ζ₁ _ => Finset.sum_congr rfl fun ζ₂ _ => ?_
    rw [hW, fillOn_union h, Equiv.apply_symm_apply, f1]
    congr 1
    rw [← fillOn_comm h, f2]
  simp only [expect, prob]
  rw [← Fintype.sum_equiv (unionEquiv h).symm (fun p : (Λ₁ → E) × (Λ₂ → E) =>
    ws.W (Λ₁ ∪ Λ₂) (fillOn ω (Λ₁ ∪ Λ₂) ((unionEquiv h).symm p)) / ws.Z (Λ₁ ∪ Λ₂) ω *
      F (fillOn ω (Λ₁ ∪ Λ₂) ((unionEquiv h).symm p))) _ (fun _ => rfl)]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun ζ₁ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun ζ₂ _ => ?_
  rw [fillOn_union h, Equiv.apply_symm_apply, hW, f1, fZ, hZ, ← fillOn_comm h, f2]
  have h1 := ws.Z_pos Λ₁ ω
  have h2 := ws.Z_pos Λ₂ ω
  field_simp

/-- The kernel of the empty set is the identity. -/
theorem expect_empty (ω : I → E) (F : (I → E) → ℝ) : ws.expect ∅ ω F = F ω := by
  have hf : ∀ ζ : (∅ : Finset I) → E, fillOn ω ∅ ζ = ω := fun ζ => by
    funext i; simp [fillOn]
  have hu : (Finset.univ : Finset ((∅ : Finset I) → E)) = {fun x => (Finset.notMem_empty _ x.2).elim} := by
    ext ζ
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    funext x; exact (Finset.notMem_empty _ x.2).elim
  simp only [expect, prob, Z, hf, hu, Finset.sum_singleton]
  rw [div_self (ws.pos _ _).ne', one_mul]

/-- Expectations of bounded functions are bounded. -/
theorem abs_expect_le' (Λ : Finset I) (ω : I → E) {F : (I → E) → ℝ} {C : ℝ}
    (hC : ∀ η, |F η| ≤ C) : |ws.expect Λ ω F| ≤ C := by
  unfold expect
  calc |∑ ζ : Λ → E, ws.prob Λ ω ζ * F (fillOn ω Λ ζ)|
      ≤ ∑ ζ : Λ → E, |ws.prob Λ ω ζ * F (fillOn ω Λ ζ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ ζ : Λ → E, ws.prob Λ ω ζ * C := by
        refine Finset.sum_le_sum fun ζ _ => ?_
        rw [abs_mul, abs_of_nonneg (ws.prob_nonneg _ _ _)]
        exact mul_le_mul_of_nonneg_left (hC _) (ws.prob_nonneg _ _ _)
    _ = C := by rw [← Finset.sum_mul, ws.sum_prob, one_mul]

end WeightSystem

/-! ## Components -/

section Merge

variable {V ι E : Type} [DecidableEq V] [DecidableEq ι]

/-- The configuration equal to `a` on the vertices with label `i` and to `b` on the others. -/
def joinAt (c : V → ι) (i : ι) (a : {v // c v = i} → E) (b : {v // c v ≠ i} → E) : V → E :=
  fun v => if h : c v = i then a ⟨v, h⟩ else b ⟨v, h⟩

/-- The vertices of a finite set of labelled vertices, as a finite set of vertices. -/
def lift (c : V → ι) (i : ι) (A : Finset {v // c v = i}) : Finset V :=
  A.map (Function.Embedding.subtype _)

omit [DecidableEq V] [DecidableEq ι] in
theorem mem_lift {c : V → ι} {i : ι} {A : Finset {v // c v = i}} {v : V} :
    v ∈ lift c i A ↔ ∃ h : c v = i, ⟨v, h⟩ ∈ A := by
  simp only [lift, Finset.mem_map, Function.Embedding.coe_subtype]
  constructor
  · rintro ⟨x, hx, rfl⟩; exact ⟨x.2, hx⟩
  · rintro ⟨h, hA⟩; exact ⟨_, hA, rfl⟩

/-- `A` and its lift have the same elements. -/
def liftEquiv (c : V → ι) (i : ι) (A : Finset {v // c v = i}) : A ≃ lift c i A where
  toFun x := ⟨x.1.1, mem_lift.2 ⟨x.1.2, x.2⟩⟩
  invFun y := ⟨⟨y.1, (mem_lift.1 y.2).1⟩, (mem_lift.1 y.2).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem fillOn_joinAt (c : V → ι) (i : ι) (A : Finset {v // c v = i}) (a : {v // c v = i} → E)
    (b : {v // c v ≠ i} → E) (ζ : A → E) :
    fillOn (joinAt c i a b) (lift c i A) (ζ ∘ (liftEquiv c i A).symm) =
      joinAt c i (fillOn a A ζ) b := by
  funext v
  by_cases h : c v = i
  · by_cases hA : (⟨v, h⟩ : {v // c v = i}) ∈ A
    · have hv : v ∈ lift c i A := mem_lift.2 ⟨h, hA⟩
      simp [fillOn, joinAt, h, hA, hv, liftEquiv]
    · have hv : v ∉ lift c i A := fun hv => hA (by obtain ⟨_, h'⟩ := mem_lift.1 hv; exact h')
      simp [fillOn, joinAt, h, hA, hv]
  · have hv : v ∉ lift c i A := fun hv => h (mem_lift.1 hv).1
    simp [fillOn, joinAt, h, hv]

end Merge

namespace IsingGraph

variable {V ι : Type} [DecidableEq V] [DecidableEq ι] (G : IsingGraph V)

/-- `c : V → ι` labels unions of components of `G`: neighbours have the same label. -/
def IsComponentMap (c : V → ι) : Prop := ∀ u v, v ∈ G.nbr u → c u = c v

/-- The Ising model on the vertices with label `i` (the induced subgraph). -/
def restrict (c : V → ι) (i : ι) : IsingGraph {v // c v = i} where
  nbr u := (G.nbr u.1).subtype (fun v => c v = i)
  symm u v h := by
    rw [Finset.mem_subtype] at h ⊢
    exact G.symm _ _ h
  irrefl u := by
    rw [Finset.mem_subtype]; exact G.irrefl u.1
  J e := G.J (e.map Subtype.val)
  J_nonneg _ := G.J_nonneg _

/-- The edges meeting a set of labelled vertices are those of the induced subgraph. -/
theorem edgesMeeting_lift {c : V → ι} (hc : G.IsComponentMap c) (i : ι)
    (A : Finset {v // c v = i}) :
    G.edgesMeeting (lift c i A) = ((G.restrict c i).edgesMeeting A).map
      ⟨Sym2.map Subtype.val, Sym2.map.injective Subtype.val_injective⟩ := by
  ext e
  simp only [Finset.mem_map, Function.Embedding.coeFn_mk, mem_edgesMeeting]
  constructor
  · rintro ⟨u, hu, v, hv, rfl⟩
    obtain ⟨h, hA⟩ := mem_lift.1 hu
    have hvi : c v = i := (hc u v hv) ▸ h
    refine ⟨s(⟨u, h⟩, ⟨v, hvi⟩), ⟨⟨u, h⟩, hA, ⟨v, hvi⟩, ?_, rfl⟩, rfl⟩
    show ⟨v, hvi⟩ ∈ (G.nbr u).subtype (fun v => c v = i)
    rw [Finset.mem_subtype]; exact hv
  · rintro ⟨e', ⟨u, hu, v, hv, rfl⟩, rfl⟩
    refine ⟨u.1, mem_lift.2 ⟨u.2, hu⟩, v.1, ?_, rfl⟩
    have : v ∈ (G.nbr u.1).subtype (fun v => c v = i) := hv
    rwa [Finset.mem_subtype] at this

/-- The weight of a set of labelled vertices is that of the induced subgraph. -/
theorem weight_lift {c : V → ι} (hc : G.IsComponentMap c) (i : ι) (A : Finset {v // c v = i})
    (a : {v // c v = i} → Spin) (b : {v // c v ≠ i} → Spin) :
    G.weight (lift c i A) (joinAt c i a b) = (G.restrict c i).weight A a := by
  unfold weight energySum
  congr 1
  rw [G.edgesMeeting_lift hc, Finset.sum_map]
  refine Finset.sum_congr rfl fun e _ => ?_
  induction e using Sym2.ind with
  | h u v =>
    simp only [Function.Embedding.coeFn_mk, Sym2.map_mk, pairVal_mk, joinAt, u.2, v.2,
      dif_pos]
    rfl

/-- **The kernel of the induced subgraph is the kernel of the graph** on a set of labelled
vertices (`c` a component map): `γ^{G_i}_A(F(· ∪ b))(a) = γ^G_A F (a ∪ b)`. -/
theorem expect_lift {c : V → ι} (hc : G.IsComponentMap c) (i : ι) (A : Finset {v // c v = i})
    (a : {v // c v = i} → Spin) (b : {v // c v ≠ i} → Spin) (F : (V → Spin) → ℝ) :
    (G.restrict c i).toWeightSystem.expect A a (fun a' => F (joinAt c i a' b)) =
      G.toWeightSystem.expect (lift c i A) (joinAt c i a b) F := by
  let e : (A → Spin) ≃ (lift c i A → Spin) := Equiv.arrowCongr (liftEquiv c i A) (Equiv.refl _)
  have he : ∀ ζ : A → Spin, e ζ = ζ ∘ (liftEquiv c i A).symm := fun ζ => rfl
  have hZ : G.toWeightSystem.Z (lift c i A) (joinAt c i a b) =
      (G.restrict c i).toWeightSystem.Z A a := by
    simp only [WeightSystem.Z]
    rw [← Fintype.sum_equiv e (fun ζ => G.toWeightSystem.W (lift c i A)
      (fillOn (joinAt c i a b) (lift c i A) (e ζ))) _ (fun _ => rfl)]
    refine Finset.sum_congr rfl fun ζ _ => ?_
    rw [he, fillOn_joinAt, toWeightSystem_W, toWeightSystem_W, weight_lift G hc]
  simp only [WeightSystem.expect, WeightSystem.prob]
  rw [← Fintype.sum_equiv e (fun ζ => G.toWeightSystem.W (lift c i A)
      (fillOn (joinAt c i a b) (lift c i A) (e ζ)) / G.toWeightSystem.Z (lift c i A)
        (joinAt c i a b) * F (fillOn (joinAt c i a b) (lift c i A) (e ζ))) _ (fun _ => rfl)]
  refine Finset.sum_congr rfl fun ζ _ => ?_
  rw [he, fillOn_joinAt, hZ, toWeightSystem_W, toWeightSystem_W, weight_lift G hc]

end IsingGraph

/-! ## Products over components -/

section Split

variable {V ι E : Type} [DecidableEq V] [DecidableEq ι] [MeasurableSpace E]

/-- A configuration split into its values on the vertices with label `i` and on the others. -/
def splitAt (c : V → ι) (i : ι) (σ : V → E) : ({v // c v = i} → E) × ({v // c v ≠ i} → E) :=
  (fun v => σ v.1, fun v => σ v.1)

omit [DecidableEq V] [MeasurableSpace E] in
theorem joinAt_splitAt (c : V → ι) (i : ι) (σ : V → E) :
    joinAt c i (splitAt c i σ).1 (splitAt c i σ).2 = σ := by
  funext v
  by_cases h : c v = i <;> simp [joinAt, splitAt, h]

omit [DecidableEq V] [DecidableEq ι] in
theorem measurable_splitAt (c : V → ι) (i : ι) : Measurable (splitAt (E := E) c i) :=
  (Measurable.of_eval fun v => measurable_pi_apply v.1).prodMk
    (Measurable.of_eval fun v => measurable_pi_apply v.1)

omit [DecidableEq V] in
theorem measurable_joinAt (c : V → ι) (i : ι) :
    Measurable (fun p : ({v // c v = i} → E) × ({v // c v ≠ i} → E) => joinAt c i p.1 p.2) := by
  refine Measurable.of_eval fun v => ?_
  by_cases h : c v = i
  · simp only [joinAt, h, dif_pos]
    exact (measurable_pi_apply _).comp measurable_fst
  · simp only [joinAt, h, dif_neg, not_false_eq_true]
    exact (measurable_pi_apply _).comp measurable_snd

/-- The product of measures `ν_i` on the components: the configuration takes the values of a
sample of `ν_{c(v)}` at each vertex `v`. -/
def glue (c : V → ι) (x : ι → V → E) : V → E := fun v => x (c v) v

omit [DecidableEq V] [DecidableEq ι] in
theorem measurable_glue (c : V → ι) : Measurable (glue (E := E) c) :=
  Measurable.of_eval fun v => (measurable_pi_apply v).comp (measurable_pi_apply (c v))

omit [DecidableEq V] [DecidableEq ι] in
/-- **Independence of the components** under the product measure: the law of the split of the
glued configuration is the product of the law of the component `i` and the law of the rest. -/
theorem map_splitAt_glue (c : V → ι) (ν : ι → Measure (V → E)) [∀ i, IsProbabilityMeasure (ν i)]
    (i : ι) :
    ((Measure.infinitePi ν).map (glue c)).map (splitAt c i) =
      ((ν i).map (fun σ (v : {v // c v = i}) => σ v.1)).prod
        (((Measure.infinitePi ν).map (glue c)).map (fun σ (v : {v // c v ≠ i}) => σ v.1)) := by
  set P := Measure.infinitePi ν
  let X : (ι → V → E) → V → E := fun x => x i
  let Y : (ι → V → E) → ({j // j ≠ i} → V → E) := fun x j => x j.1
  let rF : (V → E) → ({v // c v = i} → E) := fun σ v => σ v.1
  let g : ({j // j ≠ i} → V → E) → ({v // c v ≠ i} → E) := fun y v => y ⟨c v.1, v.2⟩ v.1
  have hX : Measurable X := measurable_pi_apply i
  have hY : Measurable Y := Measurable.of_eval fun j => measurable_pi_apply j.1
  have hrF : Measurable rF := Measurable.of_eval fun v => measurable_pi_apply v.1
  have hg : Measurable g := Measurable.of_eval fun v =>
    (measurable_pi_apply v.1).comp (measurable_pi_apply (⟨c v.1, v.2⟩ : {j // j ≠ i}))
  have hsplit : splitAt c i ∘ glue c = Prod.map rF g ∘ (fun x => (X x, Y x)) := by
    funext x
    simp only [Function.comp_apply, splitAt, glue, Prod.map, X, Y, rF, g]
    congr 1
    funext v
    rw [v.2]
  have hrest : (fun σ (v : {v // c v ≠ i}) => σ v.1) ∘ glue c = g ∘ Y := rfl
  -- the coordinate `i` is independent of the others
  have hind : IndepFun X Y P := by
    have h0 : iIndepFun (fun j (x : ι → V → E) => x j) P := by
      have := iIndepFun_infinitePi (P := ν) (X := fun _ => id) (fun _ => measurable_id)
      simpa using this
    rw [iIndepFun_iff_iIndep] at h0
    have h1 := indep_iSup_of_disjoint (fun j => (measurable_pi_apply j).comap_le) h0
      (S := {i}) (T := {i}ᶜ) disjoint_compl_right
    have hle1 : MeasurableSpace.comap X inferInstance ≤
        ⨆ j ∈ ({i} : Set ι), MeasurableSpace.comap (fun x : ι → V → E => x j) inferInstance :=
      le_iSup₂ (f := fun j (_ : j ∈ ({i} : Set ι)) =>
        MeasurableSpace.comap (fun x : ι → V → E => x j) inferInstance) i rfl
    have hle2 : MeasurableSpace.comap Y inferInstance ≤
        ⨆ j ∈ ({i}ᶜ : Set ι), MeasurableSpace.comap (fun x : ι → V → E => x j) inferInstance := by
      refine Measurable.comap_le ?_
      refine @measurable_pi_lambda _ _ _ (⨆ j ∈ ({i}ᶜ : Set ι),
        MeasurableSpace.comap (fun x : ι → V → E => x j) inferInstance) _ _ fun j => ?_
      refine Measurable.of_comap_le ?_
      exact le_iSup₂ (f := fun j (_ : j ∈ ({i}ᶜ : Set ι)) =>
        MeasurableSpace.comap (fun x : ι → V → E => x j) inferInstance) j.1 j.2
    exact indep_of_indep_of_le_right (indep_of_indep_of_le_left h1 hle1) hle2
  have hjoint := (indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable).1 hind
  have hR : Measurable (fun σ : V → E => fun v : {v // c v ≠ i} => σ v.1) :=
    Measurable.of_eval fun v => measurable_pi_apply v.1
  rw [Measure.map_map (measurable_splitAt c i) (measurable_glue c), hsplit,
    ← Measure.map_map (hrF.prodMap hg) (hX.prodMk hY), hjoint,
    ← Measure.map_prod_map _ _ hrF hg]
  congr 1
  · show Measure.map rF (Measure.map (fun x => x i) (Measure.infinitePi ν)) = _
    rw [Measure.infinitePi_map_eval]
  · rw [Measure.map_map hg hY, Measure.map_map hR (measurable_glue c)]
    rfl

end Split

namespace IsingGraph

variable {V ι : Type} [DecidableEq V] [DecidableEq ι] (G : IsingGraph V)

omit [DecidableEq ι] in
/-- The weight of a union of sets in different components is the product of their weights. -/
theorem weight_union_of_label {c : V → ι} (hc : G.IsComponentMap c) {i : ι}
    {Λ₁ Λ₂ : Finset V} (h1 : ∀ v ∈ Λ₁, c v = i) (h2 : ∀ v ∈ Λ₂, c v ≠ i) (σ : V → Spin) :
    G.weight (Λ₁ ∪ Λ₂) σ = G.weight Λ₁ σ * G.weight Λ₂ σ := by
  unfold weight energySum edgesMeeting
  rw [Finset.union_biUnion, Finset.sum_union, Real.exp_add]
  rw [Finset.disjoint_left]
  intro e he1 he2
  have he1' : e ∈ G.edgesMeeting Λ₁ := he1
  have he2' : e ∈ G.edgesMeeting Λ₂ := he2
  rw [mem_edgesMeeting] at he1' he2'
  obtain ⟨u, hu, v, hv, rfl⟩ := he1'
  obtain ⟨u', hu', v', hv', he⟩ := he2'
  have hcu : c u = i := h1 u hu
  have hcv : c v = i := (hc u v hv) ▸ hcu
  have hcu' : c u' ≠ i := h2 u' hu'
  have hcv' : c v' ≠ i := (hc u' v' hv') ▸ hcu'
  rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hcu' hcu
  · exact hcu' hcv

omit [DecidableEq ι] in
/-- The neighbourhood range of a set with one label has that label. -/
theorem range_label {c : V → ι} (hc : G.IsComponentMap c) {Λ : Finset V} {P : ι → Prop}
    (h : ∀ v ∈ Λ, P (c v)) : ∀ v ∈ G.toWeightSystem.range Λ, P (c v) := by
  intro v hv
  simp only [toWeightSystem, Finset.mem_union, Finset.mem_biUnion] at hv
  rcases hv with hv | ⟨u, hu, hv⟩
  · exact h v hv
  · rw [← hc u v hv]; exact h u hu

/-- The kernel of a finite set is the composition of the kernels of its part with label `i` and
of the rest. -/
theorem expect_label {c : V → ι} (hc : G.IsComponentMap c) (i : ι) (Λ : Finset V) (ω : V → Spin)
    (F : (V → Spin) → ℝ) :
    G.toWeightSystem.expect Λ ω F =
      G.toWeightSystem.expect (Λ.filter (fun v => c v = i)) ω
        (fun ω' => G.toWeightSystem.expect (Λ.filter (fun v => ¬ c v = i)) ω' F) := by
  have h1 : ∀ v ∈ Λ.filter (fun v => c v = i), c v = i := fun v hv => (Finset.mem_filter.1 hv).2
  have h2 : ∀ v ∈ Λ.filter (fun v => ¬ c v = i), c v ≠ i := fun v hv => (Finset.mem_filter.1 hv).2
  conv_lhs => rw [← Finset.filter_union_filter_not_eq (fun v => c v = i) Λ]
  refine G.toWeightSystem.expect_union (Finset.disjoint_filter_filter_not _ _ _) ?_ ?_
    (fun σ => G.weight_union_of_label hc h1 h2 σ) ω F
  · rw [Finset.disjoint_left]
    intro v hv hv2
    exact h2 v hv2 (G.range_label hc (P := fun j => j = i) h1 v hv)
  · rw [Finset.disjoint_left]
    intro v hv hv1
    exact G.range_label hc (P := fun j => j ≠ i) h2 v hv (h1 v hv1)

/-- **DLR for a set inside one component**, for a measure whose split at the label `i` is a
product with a Gibbs measure of the induced subgraph as first factor (Fubini). -/
theorem dlr_component {c : V → ι} (hc : G.IsComponentMap c) (i : ι) {μ : Measure (V → Spin)}
    {μi : Measure ({v // c v = i} → Spin)} {μ' : Measure ({v // c v ≠ i} → Spin)}
    [IsProbabilityMeasure μ'] (hsplit : μ.map (splitAt c i) = μi.prod μ')
    (hμi : (G.restrict c i).toWeightSystem.IsDLR μi) (A : Finset {v // c v = i})
    {F : (V → Spin) → ℝ} (hF : Measurable F) (hb : ∃ C : ℝ, ∀ ω, |F ω| ≤ C) :
    ∫ ω, F ω ∂μ = ∫ ω, G.toWeightSystem.expect (lift c i A) ω F ∂μ := by
  obtain ⟨hμ, hdlr⟩ := hμi
  obtain ⟨C, hC⟩ := hb
  have hj := measurable_joinAt (E := Spin) c i
  have hH : Measurable (fun ω => G.toWeightSystem.expect (lift c i A) ω F) :=
    G.toWeightSystem.measurable_expect' _ hF
  have hHb : ∀ ω, |G.toWeightSystem.expect (lift c i A) ω F| ≤ C := fun ω =>
    G.toWeightSystem.abs_expect_le' _ _ hC
  have key : ∀ {H : (V → Spin) → ℝ}, Measurable H → (∀ ω, |H ω| ≤ C) →
      ∫ ω, H ω ∂μ = ∫ b, ∫ a, H (joinAt c i a b) ∂μi ∂μ' := by
    intro H hHm hHC
    have hint : Integrable (fun p : ({v // c v = i} → Spin) × ({v // c v ≠ i} → Spin) =>
        H (joinAt c i p.1 p.2)) (μi.prod μ') :=
      Integrable.of_bound (hHm.comp hj).aestronglyMeasurable C
        (ae_of_all _ fun p => by rw [Real.norm_eq_abs]; exact hHC _)
    calc ∫ ω, H ω ∂μ = ∫ ω, H (joinAt c i (splitAt c i ω).1 (splitAt c i ω).2) ∂μ := by
          simp only [joinAt_splitAt]
      _ = ∫ p, H (joinAt c i p.1 p.2) ∂(μ.map (splitAt c i)) :=
          (integral_map (measurable_splitAt c i).aemeasurable
            (hHm.comp hj).aestronglyMeasurable).symm
      _ = ∫ b, ∫ a, H (joinAt c i a b) ∂μi ∂μ' := by
          rw [hsplit, integral_prod_symm _ hint]
  rw [key hF hC, key hH hHb]
  refine integral_congr_ae (ae_of_all _ fun b => ?_)
  simp only
  rw [hdlr A (fun a => F (joinAt c i a b))
    (hF.comp (hj.comp (measurable_id.prodMk measurable_const))) ⟨C, fun _ => hC _⟩]
  refine integral_congr_ae (ae_of_all _ fun a => ?_)
  exact G.expect_lift hc i A a b F

/-- **A product of Gibbs measures on the components of a graph is a Gibbs measure on the graph**
(the proof of `thm:main`, Step 3: "the kernel of a finite set is the product of the kernels of its
intersections with the components"): if `μ` satisfies the DLR identity for every finite set inside
one component, it satisfies it for every finite set. -/
theorem isDLR_of_components {c : V → ι} (hc : G.IsComponentMap c) {μ : Measure (V → Spin)}
    [IsProbabilityMeasure μ]
    (hcomp : ∀ (i : ι) (A : Finset {v // c v = i}) (F : (V → Spin) → ℝ), Measurable F →
      (∃ C : ℝ, ∀ ω, |F ω| ≤ C) →
        ∫ ω, F ω ∂μ = ∫ ω, G.toWeightSystem.expect (lift c i A) ω F ∂μ) :
    G.toWeightSystem.IsDLR μ := by
  refine ⟨inferInstance, fun Λ => ?_⟩
  induction Λ using Finset.strongInduction with
  | H Λ ih =>
    intro F hF hb
    rcases Λ.eq_empty_or_nonempty with rfl | ⟨v, hv⟩
    · simp [WeightSystem.expect_empty]
    set i := c v
    have hsub : Λ.filter (fun w => ¬ c w = i) ⊂ Λ := by
      refine Finset.ssubset_iff_subset_ne.2 ⟨Finset.filter_subset _ _, fun h => ?_⟩
      have : v ∈ Λ.filter (fun w => ¬ c w = i) := by rw [h]; exact hv
      exact (Finset.mem_filter.1 this).2 rfl
    obtain ⟨C, hC⟩ := hb
    have hH : Measurable (fun ω => G.toWeightSystem.expect (Λ.filter (fun w => ¬ c w = i)) ω F) :=
      G.toWeightSystem.measurable_expect' _ hF
    have hl : lift c i (Λ.subtype (fun w => c w = i)) = Λ.filter (fun w => c w = i) :=
      Finset.subtype_map _
    have e1 := hcomp i (Λ.subtype (fun w => c w = i)) _ hH
      ⟨C, fun ω => G.toWeightSystem.abs_expect_le' _ _ hC⟩
    rw [hl] at e1
    simp only [G.expect_label hc i Λ]
    rw [← e1]
    exact (ih _ hsub F hF ⟨C, hC⟩)

/-- **The product of Gibbs measures of the components is a Gibbs measure**: for a component map
`c` and probability measures `ν_i` whose restrictions to the vertices with label `i` are Gibbs
measures of the induced subgraphs, the product measure (`glue`) is a Gibbs measure of `G`. -/
theorem isDLR_glue {c : V → ι} (hc : G.IsComponentMap c) (ν : ι → Measure (V → Spin))
    [∀ i, IsProbabilityMeasure (ν i)]
    (hν : ∀ i, (G.restrict c i).toWeightSystem.IsDLR
      ((ν i).map (fun σ (v : {v // c v = i}) => σ v.1))) :
    G.toWeightSystem.IsDLR ((Measure.infinitePi ν).map (glue c)) := by
  have : IsProbabilityMeasure ((Measure.infinitePi ν).map (glue c)) :=
    (Measure.isProbabilityMeasure_map_iff (measurable_glue c).aemeasurable).2 inferInstance
  refine G.isDLR_of_components hc fun i A F hF hb => ?_
  have : IsProbabilityMeasure (((Measure.infinitePi ν).map (glue c)).map
      (fun σ (v : {v // c v ≠ i}) => σ v.1)) :=
    (Measure.isProbabilityMeasure_map_iff (Measurable.of_eval fun v => measurable_pi_apply v.1).aemeasurable).2 inferInstance
  exact G.dlr_component hc i (map_splitAt_glue c ν i) (hν i) A hF hb

end IsingGraph

/-! ## Isomorphisms -/

namespace IsingGraph

variable {V W : Type} [DecidableEq V] [DecidableEq W] (G : IsingGraph V) (G' : IsingGraph W)

/-- An isomorphism of Ising models: a bijection of the vertices carrying neighbours to neighbours
and couplings to couplings. -/
structure Iso where
  /-- the bijection of the vertices -/
  e : V ≃ W
  nbr : ∀ u, G'.nbr (e u) = (G.nbr u).map e.toEmbedding
  J : ∀ u v, v ∈ G.nbr u → G'.J s(e u, e v) = G.J s(u, v)

variable {G G'}

/-- The image of a finite set under an isomorphism, as an equivalence of the elements. -/
def Iso.finsetEquiv (φ : Iso G G') (Λ : Finset V) : Λ ≃ Λ.map φ.e.toEmbedding where
  toFun x := ⟨φ.e x.1, Finset.mem_map_of_mem _ x.2⟩
  invFun y := ⟨φ.e.symm y.1, by
    obtain ⟨x, hx, h⟩ := Finset.mem_map.1 y.2
    rw [← h]; simpa using hx⟩
  left_inv x := by simp
  right_inv y := by simp

theorem Iso.fillOn_map (φ : Iso G G') (Λ : Finset V) (σ : V → Spin) (ζ : Λ → Spin) :
    fillOn (σ ∘ φ.e.symm) (Λ.map φ.e.toEmbedding) (ζ ∘ (φ.finsetEquiv Λ).symm) =
      fillOn σ Λ ζ ∘ φ.e.symm := by
  funext w
  by_cases h : φ.e.symm w ∈ Λ
  · have hw : w ∈ Λ.map φ.e.toEmbedding := Finset.mem_map.2 ⟨_, h, by simp⟩
    simp [fillOn, h, Iso.finsetEquiv]
  · have hw : w ∉ Λ.map φ.e.toEmbedding := fun hw => h (by
      obtain ⟨x, hx, hxw⟩ := Finset.mem_map.1 hw
      rw [← hxw]; simpa using hx)
    simp [fillOn, h]

theorem Iso.weight_map (φ : Iso G G') (Λ : Finset V) (σ : V → Spin) :
    G'.weight (Λ.map φ.e.toEmbedding) (σ ∘ φ.e.symm) = G.weight Λ σ := by
  unfold weight energySum
  congr 1
  have hE : G'.edgesMeeting (Λ.map φ.e.toEmbedding) =
      (G.edgesMeeting Λ).map ⟨Sym2.map φ.e, Sym2.map.injective φ.e.injective⟩ := by
    ext e
    simp only [Finset.mem_map, Function.Embedding.coeFn_mk, mem_edgesMeeting]
    constructor
    · rintro ⟨u', hu', v', hv', rfl⟩
      obtain ⟨u, hu, rfl⟩ := hu'
      rw [φ.nbr] at hv'
      obtain ⟨v, hv, rfl⟩ := Finset.mem_map.1 hv'
      exact ⟨s(u, v), ⟨u, hu, v, hv, rfl⟩, by simp⟩
    · rintro ⟨e', ⟨u, hu, v, hv, rfl⟩, rfl⟩
      refine ⟨φ.e u, ⟨u, hu, rfl⟩, φ.e v, ?_, by simp⟩
      rw [φ.nbr]; exact Finset.mem_map_of_mem _ hv
  rw [hE, Finset.sum_map]
  refine Finset.sum_congr rfl fun e he => ?_
  induction e using Sym2.ind with
  | h u v =>
    obtain ⟨a, _, b, hb, hab⟩ := G.mem_edgesMeeting.1 he
    simp only [Function.Embedding.coeFn_mk, Sym2.map_mk, pairVal_mk, Function.comp_apply,
      Equiv.symm_apply_apply]
    congr 1
    rcases Sym2.eq_iff.1 hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact φ.J _ _ hb
    · rw [Sym2.eq_swap, φ.J _ _ hb, Sym2.eq_swap]

theorem Iso.expect_map (φ : Iso G G') (Λ : Finset V) (σ : V → Spin) (F : (W → Spin) → ℝ) :
    G'.toWeightSystem.expect (Λ.map φ.e.toEmbedding) (σ ∘ φ.e.symm) F =
      G.toWeightSystem.expect Λ σ (fun σ' => F (σ' ∘ φ.e.symm)) := by
  let e : (Λ → Spin) ≃ (Λ.map φ.e.toEmbedding → Spin) :=
    Equiv.arrowCongr (φ.finsetEquiv Λ) (Equiv.refl _)
  have he : ∀ ζ : Λ → Spin, e ζ = ζ ∘ (φ.finsetEquiv Λ).symm := fun ζ => rfl
  have hZ : G'.toWeightSystem.Z (Λ.map φ.e.toEmbedding) (σ ∘ φ.e.symm) =
      G.toWeightSystem.Z Λ σ := by
    simp only [WeightSystem.Z]
    rw [← Fintype.sum_equiv e (fun ζ => G'.toWeightSystem.W (Λ.map φ.e.toEmbedding)
      (fillOn (σ ∘ φ.e.symm) (Λ.map φ.e.toEmbedding) (e ζ))) _ (fun _ => rfl)]
    refine Finset.sum_congr rfl fun ζ _ => ?_
    rw [he, φ.fillOn_map, toWeightSystem_W, toWeightSystem_W, φ.weight_map]
  simp only [WeightSystem.expect, WeightSystem.prob]
  rw [← Fintype.sum_equiv e (fun ζ => G'.toWeightSystem.W (Λ.map φ.e.toEmbedding)
      (fillOn (σ ∘ φ.e.symm) (Λ.map φ.e.toEmbedding) (e ζ)) /
        G'.toWeightSystem.Z (Λ.map φ.e.toEmbedding) (σ ∘ φ.e.symm) *
        F (fillOn (σ ∘ φ.e.symm) (Λ.map φ.e.toEmbedding) (e ζ))) _ (fun _ => rfl)]
  refine Finset.sum_congr rfl fun ζ _ => ?_
  rw [he, φ.fillOn_map, hZ, toWeightSystem_W, toWeightSystem_W, φ.weight_map]

/-- **Gibbs measures are carried by isomorphisms** (the image of the plus and minus states under
`m ↦ 𝐫_d(m)` in Step 3 of `thm:main`). -/
theorem Iso.isDLR_map (φ : Iso G G') {ν : Measure (V → Spin)} (h : G.toWeightSystem.IsDLR ν) :
    G'.toWeightSystem.IsDLR (ν.map (fun σ => σ ∘ φ.e.symm)) := by
  obtain ⟨hν, hdlr⟩ := h
  have hm : Measurable (fun σ : V → Spin => σ ∘ φ.e.symm) :=
    Measurable.of_eval fun w => measurable_pi_apply _
  refine ⟨(Measure.isProbabilityMeasure_map_iff hm.aemeasurable).2 inferInstance, fun Λ' F hF hb => ?_⟩
  have hΛ : (Λ'.map φ.e.symm.toEmbedding).map φ.e.toEmbedding = Λ' := by
    ext w; simp
  have hH : Measurable (fun σ' => G'.toWeightSystem.expect Λ' σ' F) :=
    G'.toWeightSystem.measurable_expect' _ hF
  rw [integral_map hm.aemeasurable hF.aestronglyMeasurable,
    integral_map hm.aemeasurable hH.aestronglyMeasurable]
  refine (hdlr (Λ'.map φ.e.symm.toEmbedding) (fun σ => F (σ ∘ φ.e.symm)) (hF.comp hm)
    (by obtain ⟨C, hC⟩ := hb; exact ⟨C, fun σ => hC _⟩)).trans ?_
  refine integral_congr_ae (ae_of_all _ fun σ => ?_)
  simp only
  rw [← φ.expect_map, hΛ]

end IsingGraph

end Gibbs

end UPD

/-
# Eliminating private coordinates (`pay:elim`)

New in this project (session 9). QB's G.5 ruling: `pay:elim` is proved for a general
hard-constraint weight system. The setting of `pay:elim`, generalized:
* spins: a type `V` of vertices, each with one coordinate; edges `Ed`, each with a tail and a head
  in `V` (equal ends allowed), every vertex in finitely many edges (`edgesAt`);
* private coordinates: the edge `e` owns the coordinates `Q e` (a finite type, possibly empty); the
  coordinates are `ECoord V Ed Q = V ⊕ Σ e, Q e`, all with values in one finite set `E` (spins too);
* factors `W_e(η_e, σ_u, σ_v) ≥ 0` (`Wf`) with `Z_e(σ_u, σ_v) = ∑_{η_e} W_e > 0` (`Zf_pos`), and
  vertex factors `κ_v(σ_v) ≥ 0` (a generalization: they carry the single-site constraints of a spin
  coordinate, e.g. its kind, and enter both specifications unchanged).
`gamma` is the factor specification of the `W_e` and `κ_v` on all coordinates, `gammaBar` that of
the `Z_e` and `κ_v` on the spins. `lift ν` is `L(ν)(dσ, dη) = ν(dσ) ∏_e K_e(η_e | σ_u, σ_v)`,
`K_e = W_e / Z_e`, constructed as the image of `ν ⊗ ⨂_{(e, a, b)} K_e(· | a, b)` (one independent
sample for every edge and every pair of end values) under the map that reads, for each `e`, the
sample of `(e, σ_u, σ_v)`.

This file (part 1): the data, `gamma`, `gammaBar` (`Gibbs/Factor.lean`), the closed sets
`closedSet T F` (the spins of `T` and the private coordinates of `F`) and their weights, the lift
and its cylinder masses `lift_cyl` (formula (L): `L(ν)(cyl J a) = ν(cyl T a) ∏_{e ∈ F} K_e(a)` for
closed `J`), and uniqueness on closed cylinders.
-/
import UndecidablePhaseDiagram.Gibbs.Factor
import UndecidablePhaseDiagram.Gibbs.Cylinder
import UndecidablePhaseDiagram.Gibbs.Transport
import Mathlib.Probability.ProductMeasure

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace UPD

namespace Gibbs

/-- The coordinates of `pay:elim`: one spin coordinate per vertex and the private coordinates
`Q e` of every edge. -/
abbrev ECoord (V Ed : Type) (Q : Ed → Type) := V ⊕ (Σ e : Ed, Q e)

/-- The data of `pay:elim` (generalized by vertex factors `κ_v`). -/
structure ElimData (V Ed : Type) (Q : Ed → Type) (E : Type) [Fintype E] [∀ e, Fintype (Q e)]
    [∀ e, DecidableEq (Q e)] where
  /-- The tail `u(e)`. -/
  tail : Ed → V
  /-- The head `v(e)`. -/
  head : Ed → V
  /-- The edges with an end at a vertex. -/
  edgesAt : V → Finset Ed
  mem_edgesAt : ∀ (v : V) (e : Ed), e ∈ edgesAt v ↔ tail e = v ∨ head e = v
  /-- The factor `W_e(η_e, σ_u, σ_v)`. -/
  Wf : (e : Ed) → (Q e → E) → E → E → ℝ
  Wf_nonneg : ∀ (e : Ed) (ζ : Q e → E) (a b : E), 0 ≤ Wf e ζ a b
  Zf_pos : ∀ (e : Ed) (a b : E), 0 < ∑ ζ : Q e → E, Wf e ζ a b
  /-- The vertex factor `κ_v(σ_v)`. -/
  κ : V → E → ℝ
  κ_nonneg : ∀ (v : V) (a : E), 0 ≤ κ v a

namespace ElimData

variable {V Ed : Type} [DecidableEq V] [DecidableEq Ed] {Q : Ed → Type} [∀ e, Fintype (Q e)]
  [∀ e, DecidableEq (Q e)] {E : Type} [Fintype E] [DecidableEq E] (D : ElimData V Ed Q E)

/-! ## The factors -/

/-- `Z_e(a, b) = ∑_η W_e(η, a, b)`. -/
def Zf (e : Ed) (a b : E) : ℝ := ∑ ζ : Q e → E, D.Wf e ζ a b

/-- `K_e(η | a, b) = W_e(η, a, b) / Z_e(a, b)`. -/
def Kf (e : Ed) (ζ : Q e → E) (a b : E) : ℝ := D.Wf e ζ a b / D.Zf e a b

theorem Zf_pos' (e : Ed) (a b : E) : 0 < D.Zf e a b := D.Zf_pos e a b

theorem Kf_nonneg (e : Ed) (ζ : Q e → E) (a b : E) : 0 ≤ D.Kf e ζ a b :=
  div_nonneg (D.Wf_nonneg _ _ _ _) (D.Zf_pos' _ _ _).le

theorem sum_Kf (e : Ed) (a b : E) : ∑ ζ : Q e → E, D.Kf e ζ a b = 1 := by
  simp only [Kf, ← Finset.sum_div]
  exact div_self (D.Zf_pos' e a b).ne'

/-- An edge without private coordinates has `K_e = 1`. -/
theorem Kf_of_isEmpty {e : Ed} (h : IsEmpty (Q e)) (ζ : Q e → E) (a b : E) :
    D.Kf e ζ a b = 1 := by
  have hu : ∀ ζ' : Q e → E, ζ' = ζ := fun ζ' => funext fun q => (h.false q).elim
  have hs := D.sum_Kf e a b
  rw [Finset.sum_eq_single ζ (fun ζ' _ hne => absurd (hu ζ') hne)
    (fun h' => absurd (Finset.mem_univ ζ) h')] at hs
  exact hs

/-- The private coordinates of `e` in a configuration. -/
def priv (x : ECoord V Ed Q → E) (e : Ed) : Q e → E := fun q => x (Sum.inr ⟨e, q⟩)

/-- The spins of a configuration. -/
def spins (x : ECoord V Ed Q → E) : V → E := fun v => x (Sum.inl v)

/-- The factor `W_e` as a function of the configuration. -/
def edgeW (e : Ed) (x : ECoord V Ed Q → E) : ℝ :=
  D.Wf e (priv x e) (x (Sum.inl (D.tail e))) (x (Sum.inl (D.head e)))

/-- The coordinates of the private coordinates of `e`. -/
def privSet (e : Ed) : Finset (ECoord V Ed Q) :=
  Finset.univ.map ⟨fun q => Sum.inr ⟨e, q⟩, fun q q' h => by simpa using h⟩

omit [DecidableEq V] in
theorem mem_privSet {e : Ed} {i : ECoord V Ed Q} : i ∈ privSet e ↔ ∃ q, i = Sum.inr ⟨e, q⟩ := by
  simp [privSet, eq_comm]
  exact Iff.rfl

/-- **The specification `γ` of `pay:elim`**: the factors `W_e` (`Sum.inl e`) and `κ_v`
(`Sum.inr v`) on all coordinates. -/
def gamma : FactorSystem (ECoord V Ed Q) E (Ed ⊕ V) where
  supp k := match k with
    | Sum.inl e => {Sum.inl (D.tail e), Sum.inl (D.head e)} ∪ privSet e
    | Sum.inr v => {Sum.inl v}
  φ k := match k with
    | Sum.inl e => D.edgeW e
    | Sum.inr v => fun x => D.κ v (x (Sum.inl v))
  nonneg k x := by
    cases k with
    | inl e => exact D.Wf_nonneg _ _ _ _
    | inr v => exact D.κ_nonneg _ _
  isLocal k x x' h := by
    cases k with
    | inl e =>
      have h1 := h (Sum.inl (D.tail e)) (by simp)
      have h2 := h (Sum.inl (D.head e)) (by simp)
      have h3 : priv x e = priv x' e :=
        funext fun q => h _ (Finset.mem_union_right _ (mem_privSet.2 ⟨q, rfl⟩))
      show D.Wf e (priv x e) (x (Sum.inl (D.tail e))) (x (Sum.inl (D.head e))) =
        D.Wf e (priv x' e) (x' (Sum.inl (D.tail e))) (x' (Sum.inl (D.head e)))
      rw [h1, h2, h3]
    | inr v => exact congrArg (D.κ v) (h _ (Finset.mem_singleton_self _))
  at_ i := match i with
    | Sum.inl v => (D.edgesAt v).map ⟨Sum.inl, Sum.inl_injective⟩ ∪ {Sum.inr v}
    | Sum.inr ⟨e, _⟩ => {Sum.inl e}
  mem_at i k := by
    rcases i with v | ⟨e, q⟩ <;> rcases k with e' | v'
    · simp only [Finset.mem_union, Finset.mem_map, Function.Embedding.coeFn_mk,
        Finset.mem_singleton, Sum.inl.injEq, reduceCtorEq, or_false, Finset.mem_insert,
        D.mem_edgesAt, exists_eq_right, mem_privSet, exists_false]
      constructor
      · rintro (h | h) <;> simp [h]
      · rintro (h | h) <;> simp [h]
    · simp [eq_comm]
    · show (Sum.inl e' ∈ ({Sum.inl e} : Finset (Ed ⊕ V))) ↔
        (Sum.inr ⟨e, q⟩ ∈ ({Sum.inl (D.tail e'), Sum.inl (D.head e')} ∪ privSet e' :
          Finset (ECoord V Ed Q)))
      constructor
      · intro h
        have h' : e' = e := Sum.inl.inj (Finset.mem_singleton.1 h)
        subst h'
        exact Finset.mem_union_right _ (mem_privSet.2 ⟨q, rfl⟩)
      · intro h
        rcases Finset.mem_union.1 h with h | h
        · simp at h
        · obtain ⟨q', hq'⟩ := mem_privSet.1 h
          have h' : e = e' := congrArg Sigma.fst (Sum.inr.inj hq')
          rw [h']
          exact Finset.mem_singleton_self _
    · simp

/-- **The specification `γ̄` of `pay:elim`**: the factors `Z_e` and `κ_v` on the spins. -/
def gammaBar : FactorSystem V E (Ed ⊕ V) where
  supp k := match k with
    | Sum.inl e => {D.tail e, D.head e}
    | Sum.inr v => {v}
  φ k := match k with
    | Sum.inl e => fun σ => D.Zf e (σ (D.tail e)) (σ (D.head e))
    | Sum.inr v => fun σ => D.κ v (σ v)
  nonneg k x := by
    cases k with
    | inl e => exact (D.Zf_pos' _ _ _).le
    | inr v => exact D.κ_nonneg _ _
  isLocal k x x' h := by
    cases k with
    | inl e =>
      show D.Zf e (x (D.tail e)) (x (D.head e)) = D.Zf e (x' (D.tail e)) (x' (D.head e))
      rw [h (D.tail e) (by simp), h (D.head e) (by simp)]
    | inr v => exact congrArg (D.κ v) (h _ (Finset.mem_singleton_self _))
  at_ v := (D.edgesAt v).map ⟨Sum.inl, Sum.inl_injective⟩ ∪ {Sum.inr v}
  mem_at v k := by
    rcases k with e | v'
    · simp only [Finset.mem_union, Finset.mem_map, Function.Embedding.coeFn_mk,
        Finset.mem_singleton, Sum.inl.injEq, reduceCtorEq, or_false, D.mem_edgesAt,
        exists_eq_right, Finset.mem_insert]
      constructor
      · rintro (h | h) <;> simp [h]
      · rintro (h | h) <;> simp [h]
    · simp [eq_comm]

/-! ## Closed sets and their weights -/

/-- The edges with an end in `T`. -/
def edgesOf (T : Finset V) : Finset Ed := T.biUnion D.edgesAt

theorem mem_edgesOf {T : Finset V} {e : Ed} :
    e ∈ D.edgesOf T ↔ D.tail e ∈ T ∨ D.head e ∈ T := by
  simp only [edgesOf, Finset.mem_biUnion, D.mem_edgesAt]
  constructor
  · rintro ⟨v, hv, h | h⟩
    · exact Or.inl (h ▸ hv)
    · exact Or.inr (h ▸ hv)
  · rintro (h | h)
    · exact ⟨_, h, Or.inl rfl⟩
    · exact ⟨_, h, Or.inr rfl⟩

/-- The closed set of the spins of `T` and the private coordinates of the edges of `F`. -/
def closedSet (T : Finset V) (F : Finset Ed) : Finset (ECoord V Ed Q) :=
  T.disjSum (F.sigma fun _ => Finset.univ)

omit [DecidableEq V] [DecidableEq Ed] [∀ e, DecidableEq (Q e)] in
theorem inl_mem_closedSet {T : Finset V} {F : Finset Ed} {v : V} :
    (Sum.inl v : ECoord V Ed Q) ∈ closedSet T F ↔ v ∈ T :=
  Finset.inl_mem_disjSum

omit [DecidableEq V] [DecidableEq Ed] [∀ e, DecidableEq (Q e)] in
theorem inr_mem_closedSet {T : Finset V} {F : Finset Ed} {e : Ed} {q : Q e} :
    (Sum.inr ⟨e, q⟩ : ECoord V Ed Q) ∈ closedSet T F ↔ e ∈ F := by
  simp [closedSet]

omit [DecidableEq V] [DecidableEq Ed] [∀ e, DecidableEq (Q e)] in
theorem closedSet_mono {T T' : Finset V} {F F' : Finset Ed} (hT : T ⊆ T') (hF : F ⊆ F') :
    (closedSet T F : Finset (ECoord V Ed Q)) ⊆ closedSet T' F' := by
  rintro (v | ⟨e, q⟩) h
  · exact inl_mem_closedSet.2 (hT (inl_mem_closedSet.1 h))
  · exact inr_mem_closedSet.2 (hF (inr_mem_closedSet.1 h))

/-- The factors of `γ` meeting the closed set of `T` and `F`, when `F` contains the edges at `T`
and every other edge of `F` has a private coordinate. -/
theorem gamma_meets {T : Finset V} {F : Finset Ed} (hT : D.edgesOf T ⊆ F)
    (hF : ∀ e ∈ F, e ∈ D.edgesOf T ∨ Nonempty (Q e)) :
    D.gamma.meets (closedSet T F) = F.disjSum T := by
  ext k
  rw [D.gamma.mem_meets]
  rcases k with e | v
  · rw [Finset.inl_mem_disjSum]
    constructor
    · rintro ⟨i, hi, hs⟩
      change i ∈ ({Sum.inl (D.tail e), Sum.inl (D.head e)} ∪ privSet e : Finset _) at hs
      rcases Finset.mem_union.1 hs with hs | hs
      · rcases Finset.mem_insert.1 hs with rfl | hs
        · exact hT (D.mem_edgesOf.2 (Or.inl (inl_mem_closedSet.1 hi)))
        · rw [Finset.mem_singleton] at hs
          subst hs
          exact hT (D.mem_edgesOf.2 (Or.inr (inl_mem_closedSet.1 hi)))
      · obtain ⟨q, rfl⟩ := mem_privSet.1 hs
        exact inr_mem_closedSet.1 hi
    · intro he
      rcases hF e he with h | hq
      · rcases D.mem_edgesOf.1 h with h | h
        · exact ⟨Sum.inl (D.tail e), inl_mem_closedSet.2 h,
            Finset.mem_union_left _ (Finset.mem_insert_self _ _)⟩
        · exact ⟨Sum.inl (D.head e), inl_mem_closedSet.2 h,
            Finset.mem_union_left _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))⟩
      · obtain ⟨q⟩ := hq
        exact ⟨Sum.inr ⟨e, q⟩, inr_mem_closedSet.2 he,
          Finset.mem_union_right _ (mem_privSet.2 ⟨q, rfl⟩)⟩
  · rw [Finset.inr_mem_disjSum]
    constructor
    · rintro ⟨i, hi, hs⟩
      change i ∈ ({Sum.inl v} : Finset _) at hs
      rw [Finset.mem_singleton] at hs
      subst hs
      exact inl_mem_closedSet.1 hi
    · intro hv
      exact ⟨Sum.inl v, inl_mem_closedSet.2 hv, Finset.mem_singleton_self _⟩

/-- The weight of `γ` for a closed set: `∏_{e ∈ F} W_e · ∏_{v ∈ T} κ_v`. -/
theorem gamma_W {T : Finset V} {F : Finset Ed} (hT : D.edgesOf T ⊆ F)
    (hF : ∀ e ∈ F, e ∈ D.edgesOf T ∨ Nonempty (Q e)) (x : ECoord V Ed Q → E) :
    D.gamma.toHard.W (closedSet T F) x =
      (∏ e ∈ F, D.edgeW e x) * ∏ v ∈ T, D.κ v (x (Sum.inl v)) := by
  rw [FactorSystem.toHard_W, D.gamma_meets hT hF, Finset.prod_disjSum]
  rfl

theorem gammaBar_meets (T : Finset V) : D.gammaBar.meets T = (D.edgesOf T).disjSum T := by
  ext k
  rw [D.gammaBar.mem_meets]
  rcases k with e | v
  · rw [Finset.inl_mem_disjSum, D.mem_edgesOf]
    constructor
    · rintro ⟨i, hi, hs⟩
      change i ∈ ({D.tail e, D.head e} : Finset V) at hs
      rcases Finset.mem_insert.1 hs with rfl | hs
      · exact Or.inl hi
      · rw [Finset.mem_singleton] at hs; subst hs; exact Or.inr hi
    · rintro (h | h)
      · exact ⟨_, h, Finset.mem_insert_self _ _⟩
      · exact ⟨_, h, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩
  · rw [Finset.inr_mem_disjSum]
    constructor
    · rintro ⟨i, hi, hs⟩
      change i ∈ ({v} : Finset V) at hs
      rw [Finset.mem_singleton] at hs; subst hs; exact hi
    · intro hv; exact ⟨v, hv, Finset.mem_singleton_self _⟩

/-- The weight of `γ̄`: `∏_{e at T} Z_e · ∏_{v ∈ T} κ_v`. -/
theorem gammaBar_W (T : Finset V) (σ : V → E) :
    D.gammaBar.toHard.W T σ =
      (∏ e ∈ D.edgesOf T, D.Zf e (σ (D.tail e)) (σ (D.head e))) * ∏ v ∈ T, D.κ v (σ v) := by
  rw [FactorSystem.toHard_W, D.gammaBar_meets, Finset.prod_disjSum]
  rfl

/-- The ends of the edges of `F`. -/
def endsOf (F : Finset Ed) : Finset V := F.image D.tail ∪ F.image D.head

theorem tail_mem_endsOf {F : Finset Ed} {e : Ed} (he : e ∈ F) : D.tail e ∈ D.endsOf F :=
  Finset.mem_union_left _ (Finset.mem_image_of_mem _ he)

theorem head_mem_endsOf {F : Finset Ed} {e : Ed} (he : e ∈ F) : D.head e ∈ D.endsOf F :=
  Finset.mem_union_right _ (Finset.mem_image_of_mem _ he)

/-- The range of `γ` at a closed set lies in every closed set containing its spins, edges and
their ends. -/
theorem gamma_range_subset {T T' : Finset V} {F F' : Finset Ed} (hT : D.edgesOf T ⊆ F)
    (hF : ∀ e ∈ F, e ∈ D.edgesOf T ∨ Nonempty (Q e)) (hTT : T ⊆ T') (hFF : F ⊆ F')
    (hends : D.endsOf F ⊆ T') :
    D.gamma.toHard.range (closedSet T F) ⊆ closedSet T' F' := by
  rw [FactorSystem.toHard_range, D.gamma_meets hT hF]
  intro i hi
  obtain ⟨k, hk, hs⟩ := Finset.mem_biUnion.1 hi
  rcases k with e | v
  · have he := Finset.inl_mem_disjSum.1 hk
    change i ∈ ({Sum.inl (D.tail e), Sum.inl (D.head e)} ∪ privSet e : Finset _) at hs
    rcases Finset.mem_union.1 hs with hs | hs
    · rcases Finset.mem_insert.1 hs with rfl | hs
      · exact inl_mem_closedSet.2 (hends (D.tail_mem_endsOf he))
      · rw [Finset.mem_singleton] at hs; subst hs
        exact inl_mem_closedSet.2 (hends (D.head_mem_endsOf he))
    · obtain ⟨q, rfl⟩ := mem_privSet.1 hs
      exact inr_mem_closedSet.2 (hFF he)
  · have hv := Finset.inr_mem_disjSum.1 hk
    change i ∈ ({Sum.inl v} : Finset _) at hs
    rw [Finset.mem_singleton] at hs; subst hs
    exact inl_mem_closedSet.2 (hTT hv)

theorem gammaBar_range_subset {T T' : Finset V} (hTT : T ⊆ T')
    (hends : D.endsOf (D.edgesOf T) ⊆ T') : D.gammaBar.toHard.range T ⊆ T' := by
  rw [FactorSystem.toHard_range, D.gammaBar_meets]
  intro i hi
  obtain ⟨k, hk, hs⟩ := Finset.mem_biUnion.1 hi
  rcases k with e | v
  · have he := Finset.inl_mem_disjSum.1 hk
    change i ∈ ({D.tail e, D.head e} : Finset V) at hs
    rcases Finset.mem_insert.1 hs with rfl | hs
    · exact hends (D.tail_mem_endsOf he)
    · rw [Finset.mem_singleton] at hs; subst hs; exact hends (D.head_mem_endsOf he)
  · have hv := Finset.inr_mem_disjSum.1 hk
    change i ∈ ({v} : Finset V) at hs
    rw [Finset.mem_singleton] at hs; subst hs; exact hTT hv

/-- The vertices whose spin coordinate lies in `J`. -/
def vertsIn (J : Finset (ECoord V Ed Q)) : Finset V :=
  J.biUnion fun i => match i with
    | Sum.inl v => {v}
    | Sum.inr _ => ∅

/-- The edges owning a private coordinate in `J`. -/
def edgesIn (J : Finset (ECoord V Ed Q)) : Finset Ed :=
  J.biUnion fun i => match i with
    | Sum.inl _ => ∅
    | Sum.inr p => {p.1}

theorem subset_closedSet (J : Finset (ECoord V Ed Q)) :
    J ⊆ closedSet (vertsIn J) (edgesIn J) := by
  rintro (v | ⟨e, q⟩) h
  · exact inl_mem_closedSet.2 (Finset.mem_biUnion.2 ⟨_, h, Finset.mem_singleton_self _⟩)
  · exact inr_mem_closedSet.2 (Finset.mem_biUnion.2 ⟨_, h, Finset.mem_singleton_self _⟩)

theorem edgesIn_nonempty {J : Finset (ECoord V Ed Q)} {e : Ed} (he : e ∈ edgesIn J) :
    Nonempty (Q e) := by
  obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.1 he
  rcases i with v | ⟨e', q⟩
  · simp at hi
  · rw [Finset.mem_singleton] at hi
    subst hi
    exact ⟨q⟩

/-! ## The lift `L(ν)` -/

section Lift

variable [MeasurableSpace E] [DiscreteMeasurableSpace E]

/-- The law `K_e(· | a, b)` of the private coordinates of `e`. -/
def kmeas (e : Ed) (a b : E) : Measure (Q e → E) :=
  ∑ ζ : Q e → E, ENNReal.ofReal (D.Kf e ζ a b) • Measure.dirac ζ

theorem kmeas_apply (e : Ed) (a b : E) (A : Set (Q e → E)) :
    D.kmeas e a b A = ∑ ζ : Q e → E, ENNReal.ofReal (D.Kf e ζ a b) * A.indicator 1 ζ := by
  simp only [kmeas, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    Measure.dirac_apply, smul_eq_mul]

theorem kmeas_singleton (e : Ed) (a b : E) (ζ₀ : Q e → E) :
    D.kmeas e a b {ζ₀} = ENNReal.ofReal (D.Kf e ζ₀ a b) := by
  rw [kmeas_apply, Finset.sum_eq_single ζ₀]
  · rw [Set.indicator_of_mem (Set.mem_singleton ζ₀), Pi.one_apply, mul_one]
  · intro ζ _ hne
    rw [Set.indicator_of_notMem (fun h => hne (Set.mem_singleton_iff.1 h)), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

instance (e : Ed) (a b : E) : IsProbabilityMeasure (D.kmeas e a b) := by
  constructor
  rw [kmeas_apply]
  simp only [Set.indicator_univ, Pi.one_apply, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg fun ζ _ => D.Kf_nonneg e ζ a b, D.sum_Kf,
    ENNReal.ofReal_one]

/-- One independent sample of `K_e(· | a, b)` for every edge `e` and every pair `(a, b)`. -/
def samples : Measure (∀ k : Ed × E × E, Q k.1 → E) :=
  Measure.infinitePi fun k : Ed × E × E => D.kmeas k.1 k.2.1 k.2.2

instance : IsProbabilityMeasure D.samples := by
  unfold samples
  infer_instance

/-- Spins and samples assembled into a configuration: the private coordinates of `e` are the
sample of `(e, σ_u, σ_v)`. -/
def assembleL (p : (V → E) × (∀ k : Ed × E × E, Q k.1 → E)) : ECoord V Ed Q → E := fun i =>
  match i with
  | Sum.inl v => p.1 v
  | Sum.inr ⟨e, q⟩ => p.2 (e, p.1 (D.tail e), p.1 (D.head e)) q

theorem measurable_assembleL : Measurable D.assembleL := by
  refine Measurable.of_eval fun i => ?_
  rcases i with v | ⟨e, q⟩
  · exact (measurable_pi_apply v).comp measurable_fst
  · have hg : Measurable fun r : (∀ k : Ed × E × E, Q k.1 → E) × (E × E) =>
        r.1 (e, r.2.1, r.2.2) q :=
      measurable_from_prod_countable_left fun ab =>
        (measurable_pi_apply q).comp (measurable_pi_apply (e, ab.1, ab.2))
    have hh : Measurable fun p : (V → E) × (∀ k : Ed × E × E, Q k.1 → E) =>
        (p.2, (p.1 (D.tail e), p.1 (D.head e))) :=
      measurable_snd.prodMk (((measurable_pi_apply _).comp measurable_fst).prodMk
        ((measurable_pi_apply _).comp measurable_fst))
    exact hg.comp hh

/-- **The lift** `L(ν)(dσ, dη) = ν(dσ) ∏_e K_e(η_e | σ_u, σ_v)` of `pay:elim`. -/
def lift (ν : Measure (V → E)) : Measure (ECoord V Ed Q → E) :=
  (ν.prod D.samples).map D.assembleL

instance (ν : Measure (V → E)) [IsProbabilityMeasure ν] : IsProbabilityMeasure (D.lift ν) :=
  (Measure.isProbabilityMeasure_map_iff D.measurable_assembleL.aemeasurable).2 inferInstance

omit [DecidableEq V] [DecidableEq Ed] [∀ e, Fintype (Q e)] [∀ e, DecidableEq (Q e)]
  [Fintype E] [DecidableEq E] [DiscreteMeasurableSpace E] in
theorem measurable_spins : Measurable (spins : (ECoord V Ed Q → E) → V → E) :=
  Measurable.of_eval fun _ => measurable_pi_apply _

/-- The spin marginal of `L(ν)` is `ν`. -/
theorem map_spins_lift (ν : Measure (V → E)) [IsProbabilityMeasure ν] :
    (D.lift ν).map spins = ν := by
  rw [lift, Measure.map_map measurable_spins D.measurable_assembleL]
  have e : (spins ∘ D.assembleL) = Prod.fst := rfl
  rw [e, Measure.map_fst_prod, measure_univ, one_smul]

/-- **Formula (L)**: on a closed cylinder whose edges have their ends in `T`,
`L(ν)(cyl J a) = ν(cyl T a) ∏_{e ∈ F} K_e(a)`. -/
theorem lift_cyl (ν : Measure (V → E)) [SFinite ν] {T : Finset V} {F : Finset Ed}
    (hends : D.endsOf F ⊆ T) (a : ECoord V Ed Q → E) :
    D.lift ν (cyl (closedSet T F) a) = ν (cyl T (spins a)) *
      ∏ e ∈ F, ENNReal.ofReal
        (D.Kf e (priv a e) (a (Sum.inl (D.tail e))) (a (Sum.inl (D.head e)))) := by
  set g : Ed → Ed × E × E := fun e => (e, a (Sum.inl (D.tail e)), a (Sum.inl (D.head e)))
    with hg
  have hpre : D.assembleL ⁻¹' cyl (closedSet T F) a =
      cyl T (spins a) ×ˢ Set.pi ↑(F.image g)
        (fun k : Ed × E × E => ({priv a k.1} : Set (Q k.1 → E))) := by
    ext p
    obtain ⟨σ, ζ⟩ := p
    rw [Set.mem_preimage, Set.mem_prod, Set.mem_pi]
    constructor
    · intro h
      have hσ : ∀ v ∈ T, σ v = a (Sum.inl v) := fun v hv =>
        h (Sum.inl v) (inl_mem_closedSet.2 hv)
      refine ⟨hσ, fun k hk => ?_⟩
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hk)
      show ζ (g e) = priv a e
      funext q
      have h1 := h (Sum.inr ⟨e, q⟩) (inr_mem_closedSet.2 he)
      change ζ (e, σ (D.tail e), σ (D.head e)) q = a (Sum.inr ⟨e, q⟩) at h1
      rw [hσ _ (hends (D.tail_mem_endsOf he)), hσ _ (hends (D.head_mem_endsOf he))] at h1
      exact h1
    · rintro ⟨hσ, hζ⟩ i hi
      have hσ : ∀ v ∈ T, σ v = a (Sum.inl v) := hσ
      rcases i with v | ⟨e, q⟩
      · exact hσ v (inl_mem_closedSet.1 hi)
      · have he := inr_mem_closedSet.1 hi
        have h1 : ζ (g e) = priv a e := hζ (g e) (Finset.mem_coe.2 (Finset.mem_image_of_mem g he))
        change ζ (e, σ (D.tail e), σ (D.head e)) q = a (Sum.inr ⟨e, q⟩)
        rw [hσ _ (hends (D.tail_mem_endsOf he)), hσ _ (hends (D.head_mem_endsOf he))]
        exact congrFun h1 q
  rw [lift, Measure.map_apply D.measurable_assembleL (measurableSet_cyl _ _), hpre,
    Measure.prod_prod, samples, Measure.infinitePi_pi _ (fun k _ => measurableSet_singleton _)]
  congr 1
  rw [Finset.prod_image (fun e _ e' _ h => congrArg Prod.fst h)]
  exact Finset.prod_congr rfl fun e _ => D.kmeas_singleton e _ _ _

/-- Formula (L) in real numbers. -/
theorem lift_cyl_real (ν : Measure (V → E)) [IsFiniteMeasure ν] {T : Finset V} {F : Finset Ed}
    (hends : D.endsOf F ⊆ T) (a : ECoord V Ed Q → E) :
    (D.lift ν).real (cyl (closedSet T F) a) = ν.real (cyl T (spins a)) *
      ∏ e ∈ F, D.Kf e (priv a e) (a (Sum.inl (D.tail e))) (a (Sum.inl (D.head e))) := by
  rw [measureReal_def, D.lift_cyl ν hends a, ENNReal.toReal_mul, ENNReal.toReal_prod,
    measureReal_def]
  congr 1
  exact Finset.prod_congr rfl fun e _ => ENNReal.toReal_ofReal (D.Kf_nonneg _ _ _ _)

/-- Two finite measures that agree on the closed cylinders (edges with their ends in `T`) are
equal. -/
theorem ext_closed {μ μ' : Measure (ECoord V Ed Q → E)} [IsFiniteMeasure μ] [IsFiniteMeasure μ']
    (h : ∀ (T : Finset V) (F : Finset Ed), D.endsOf F ⊆ T → ∀ a : ECoord V Ed Q → E,
      μ.real (cyl (closedSet T F) a) = μ'.real (cyl (closedSet T F) a)) : μ = μ' := by
  refine ext_cyl_cofinal (fun J => ∃ T F, D.endsOf F ⊆ T ∧ J = closedSet T F)
    (fun J₀ => ?_) ?_
  · exact ⟨closedSet (vertsIn J₀ ∪ D.endsOf (edgesIn J₀)) (edgesIn J₀),
      (subset_closedSet J₀).trans (closedSet_mono Finset.subset_union_left
        (Finset.Subset.refl _)), _, _, Finset.subset_union_right, rfl⟩
  · rintro J ⟨T, F, hTF, rfl⟩ a
    have h1 := h T F hTF a
    rw [measureReal_def, measureReal_def] at h1
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 h1

end Lift

/-! ## Sums over the private coordinates -/

section Sums

theorem endsOf_mono {F F' : Finset Ed} (h : F ⊆ F') : D.endsOf F ⊆ D.endsOf F' :=
  Finset.union_subset_union (Finset.image_subset_image h) (Finset.image_subset_image h)

/-- The fillings of the private coordinates of the edges of `F` are the families of fillings of
the `Q e`, `e ∈ F`. -/
def privEquiv (F : Finset Ed) :
    ((closedSet ∅ F : Finset (ECoord V Ed Q)) → E) ≃ (∀ e : F, Q e.1 → E) where
  toFun h e q := h ⟨Sum.inr ⟨e.1, q⟩, inr_mem_closedSet.2 e.2⟩
  invFun p i := match i with
    | ⟨Sum.inl v, hv⟩ => absurd (inl_mem_closedSet.1 hv) (Finset.notMem_empty v)
    | ⟨Sum.inr ⟨e, q⟩, he⟩ => p ⟨e, inr_mem_closedSet.1 he⟩ q
  left_inv h := by
    funext i
    obtain ⟨i, hi⟩ := i
    rcases i with v | ⟨e, q⟩
    · exact absurd (inl_mem_closedSet.1 hi) (Finset.notMem_empty v)
    · rfl
  right_inv p := by
    funext e q
    rfl

/-- Summing a product of functions of the private coordinates of the edges of `F` over their
fillings gives the product of the sums. -/
theorem sum_prod_priv (F : Finset Ed) (c : ECoord V Ed Q → E)
    (g : (e : Ed) → (Q e → E) → ℝ) :
    ∑ h : (closedSet ∅ F : Finset (ECoord V Ed Q)) → E,
        ∏ e ∈ F, g e (priv (fillOn c (closedSet ∅ F) h) e) =
      ∏ e ∈ F, ∑ ζ : Q e → E, g e ζ := by
  rw [Fintype.sum_equiv (privEquiv F) _ (fun p => ∏ e : F, g e.1 (p e)) (fun h => ?_)]
  · rw [← Finset.prod_coe_sort F (fun e => ∑ ζ : Q e → E, g e ζ),
      Finset.prod_univ_sum (fun _ => Finset.univ) (fun (e : F) (ζ : Q e.1 → E) => g e.1 ζ),
      Fintype.piFinset_univ]
  · rw [← Finset.prod_coe_sort F]
    refine Finset.prod_congr rfl fun e _ => ?_
    congr 1
    funext q
    exact fillOn_of_mem c h (inr_mem_closedSet.2 e.2)

theorem fillOn_privs_inl (F : Finset Ed) (c : ECoord V Ed Q → E)
    (h : (closedSet ∅ F : Finset (ECoord V Ed Q)) → E) (v : V) :
    fillOn c (closedSet ∅ F) h (Sum.inl v) = c (Sum.inl v) :=
  fillOn_of_not_mem c h fun hm => Finset.notMem_empty v (inl_mem_closedSet.1 hm)

/-- The weights of `γ` summed over the fillings of the private coordinates: the edge factors
become the `Z_e`. -/
theorem sum_gamma_W_fill {T : Finset V} {F : Finset Ed} (hT : D.edgesOf T ⊆ F)
    (hF : ∀ e ∈ F, e ∈ D.edgesOf T ∨ Nonempty (Q e)) (c : ECoord V Ed Q → E) :
    ∑ h : (closedSet ∅ F : Finset (ECoord V Ed Q)) → E,
        D.gamma.toHard.W (closedSet T F) (fillOn c (closedSet ∅ F) h) =
      (∏ e ∈ F, D.Zf e (c (Sum.inl (D.tail e))) (c (Sum.inl (D.head e)))) *
        ∏ v ∈ T, D.κ v (c (Sum.inl v)) := by
  simp only [D.gamma_W hT hF, edgeW, fillOn_privs_inl, ← Finset.sum_mul]
  congr 1
  exact sum_prod_priv F c fun e ζ => D.Wf e ζ (c (Sum.inl (D.tail e))) (c (Sum.inl (D.head e)))

theorem spins_preimage_cyl (T : Finset V) (a : ECoord V Ed Q → E) :
    spins ⁻¹' cyl T (spins a) = cyl (closedSet T ∅) a := by
  ext x
  simp only [Set.mem_preimage, mem_cyl]
  constructor
  · intro h i hi
    rcases i with v | ⟨e, q⟩
    · exact h v (inl_mem_closedSet.1 hi)
    · exact absurd (inr_mem_closedSet.1 hi) (Finset.notMem_empty e)
  · intro h v hv
    exact h (Sum.inl v) (inl_mem_closedSet.2 hv)

theorem closedSet_sdiff {T : Finset V} {F F' : Finset Ed}
    (h : ∀ e ∈ F, Nonempty (Q e) → e ∈ F') :
    (closedSet T F \ closedSet ∅ F' : Finset (ECoord V Ed Q)) = closedSet T ∅ := by
  ext i
  rcases i with v | ⟨e, q⟩
  · simp only [Finset.mem_sdiff, inl_mem_closedSet, Finset.notMem_empty, not_false_eq_true,
      and_true]
  · simp only [Finset.mem_sdiff, inr_mem_closedSet, Finset.notMem_empty, iff_false, not_and,
      not_not]
    exact fun he => h e he ⟨q⟩

end Sums

/-! ## `pay:elim` -/

section Theorems

variable [MeasurableSpace E] [DiscreteMeasurableSpace E]

theorem map_spins_real (μ : Measure (ECoord V Ed Q → E)) (T : Finset V)
    (a : ECoord V Ed Q → E) :
    (μ.map spins).real (cyl T (spins a)) = μ.real (cyl (closedSet T ∅) a) := by
  rw [measureReal_def, measureReal_def, Measure.map_apply measurable_spins (measurableSet_cyl _ _),
    spins_preimage_cyl]

theorem ae_kmeas_pos (e : Ed) (a b : E) : ∀ᵐ ζ ∂D.kmeas e a b, 0 < D.Wf e ζ a b := by
  rw [ae_iff, kmeas_apply]
  refine Finset.sum_eq_zero fun ζ _ => ?_
  by_cases h : 0 < D.Wf e ζ a b
  · rw [Set.indicator_of_notMem (by simpa using h), mul_zero]
  · have hK : D.Kf e ζ a b ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (not_lt.1 h) (D.Zf_pos' _ _ _).le
    rw [ENNReal.ofReal_of_nonpos hK, zero_mul]

/-- Under `L(ν)` every edge factor is positive almost surely. -/
theorem ae_edgeW_pos (ν : Measure (V → E)) [IsProbabilityMeasure ν] (e : Ed) :
    ∀ᵐ x ∂(D.lift ν), 0 < D.edgeW e x := by
  have hm : Measurable (D.edgeW e) :=
    measurable_of_dependsOn (D.gamma.supp (Sum.inl e)) _ (D.gamma.isLocal (Sum.inl e))
  rw [lift, ae_map_iff D.measurable_assembleL.aemeasurable (measurableSet_lt measurable_const hm)]
  have hs : ∀ᵐ ζ ∂D.samples, ∀ ab : E × E, 0 < D.Wf e (ζ (e, ab.1, ab.2)) ab.1 ab.2 := by
    refine ae_all_iff.2 fun ab => ?_
    have hk := D.ae_kmeas_pos e ab.1 ab.2
    have h2 : D.samples.map (fun ζ => ζ (e, ab.1, ab.2)) = D.kmeas e ab.1 ab.2 :=
      Measure.infinitePi_map_eval _ _
    rw [← h2] at hk
    exact ae_of_ae_map (measurable_pi_apply _).aemeasurable hk
  have hs' : ∀ᵐ p ∂(ν.prod D.samples), ∀ ab : E × E,
      0 < D.Wf e (p.2 (e, ab.1, ab.2)) ab.1 ab.2 := by
    have h3 : (ν.prod D.samples).map Prod.snd = D.samples := by
      rw [Measure.map_snd_prod, measure_univ, one_smul]
    rw [← h3] at hs
    exact ae_of_ae_map measurable_snd.aemeasurable hs
  filter_upwards [hs'] with p hp
  exact hp (p.1 (D.tail e), p.1 (D.head e))

/-- An identity of real numbers used in `lift_isGibbs`. -/
theorem db_alg {Na Na' R A A' H Zt Zt' k k' : ℝ} (h : Na * (Zt' * k') = Na' * (Zt * k)) :
    Na * (R * A) * (A' * (H * Zt') * k') = Na' * (R * A') * (A * (H * Zt) * k) := by
  linear_combination (R * A * A' * H) * h

/-- Closed sets containing a given closed set and a given finite set. -/
theorem closed_cofinal (T : Finset V) (F : Finset Ed) (J₀ : Finset (ECoord V Ed Q)) :
    J₀ ⊆ closedSet (T ∪ vertsIn J₀ ∪ D.endsOf (F ∪ edgesIn J₀)) (F ∪ edgesIn J₀) ∧
      T ⊆ T ∪ vertsIn J₀ ∪ D.endsOf (F ∪ edgesIn J₀) ∧ F ⊆ F ∪ edgesIn J₀ ∧
      D.endsOf (F ∪ edgesIn J₀) ⊆ T ∪ vertsIn J₀ ∪ D.endsOf (F ∪ edgesIn J₀) :=
  ⟨(subset_closedSet J₀).trans (closedSet_mono
      (fun _ hv => Finset.mem_union_left _ (Finset.mem_union_right _ hv))
      Finset.subset_union_right),
    fun _ hv => Finset.mem_union_left _ (Finset.mem_union_left _ hv), Finset.subset_union_left,
    Finset.subset_union_right⟩

/-- Detailed balance for `L(ν)` on the closed cylinders (the computation in the proof of
`pay:elim`: `Z_e` is constant for the edges not at `T`, and `K_e Z_e = W_e`). -/
theorem lift_db {ν : Measure (V → E)} (hν : D.gammaBar.toHard.IsGibbs ν) {T TJ : Finset V}
    {F FJ : Finset Ed} (hT : D.edgesOf T ⊆ F) (hF : ∀ e ∈ F, e ∈ D.edgesOf T ∨ Nonempty (Q e))
    (hTJ : T ⊆ TJ) (hFJ : F ⊆ FJ) (hends : D.endsOf FJ ⊆ TJ) :
    D.gamma.toHard.DB (D.lift ν) (closedSet T F) (closedSet TJ FJ) := by
  haveI := hν.1
  intro a a' haa'
  have hoffT : ∀ v, v ∉ T → a (Sum.inl v) = a' (Sum.inl v) := fun v hv =>
    haa' _ fun hm => hv (inl_mem_closedSet.1 hm)
  have hdbν := D.gammaBar.toHard.db_of_isGibbs hν hTJ
    (D.gammaBar_range_subset hTJ ((D.endsOf_mono hT).trans ((D.endsOf_mono hFJ).trans hends)))
    (spins a) (spins a') (fun v hv => hoffT v hv)
  rw [D.gammaBar_W, D.gammaBar_W] at hdbν
  rw [D.lift_cyl_real ν hends a, D.lift_cyl_real ν hends a', D.gamma_W hT hF,
    D.gamma_W hT hF]
  have hR : ∏ e ∈ FJ \ F, D.Kf e (priv a e) (a (Sum.inl (D.tail e))) (a (Sum.inl (D.head e))) =
      ∏ e ∈ FJ \ F, D.Kf e (priv a' e) (a' (Sum.inl (D.tail e))) (a' (Sum.inl (D.head e))) := by
    refine Finset.prod_congr rfl fun e he => ?_
    have heF : e ∉ F := (Finset.mem_sdiff.1 he).2
    have het : ¬(D.tail e ∈ T ∨ D.head e ∈ T) := fun h => heF (hT (D.mem_edgesOf.2 h))
    rw [not_or] at het
    have hp : priv a e = priv a' e :=
      funext fun q => haa' _ fun hm => heF (inr_mem_closedSet.1 hm)
    rw [hp, hoffT _ het.1, hoffT _ het.2]
  have hH : ∏ e ∈ F \ D.edgesOf T, D.Zf e (a (Sum.inl (D.tail e))) (a (Sum.inl (D.head e))) =
      ∏ e ∈ F \ D.edgesOf T, D.Zf e (a' (Sum.inl (D.tail e))) (a' (Sum.inl (D.head e))) := by
    refine Finset.prod_congr rfl fun e he => ?_
    have het : ¬(D.tail e ∈ T ∨ D.head e ∈ T) := fun h =>
      (Finset.mem_sdiff.1 he).2 (D.mem_edgesOf.2 h)
    rw [not_or] at het
    rw [hoffT _ het.1, hoffT _ het.2]
  have hW : ∀ c : ECoord V Ed Q → E, ∏ e ∈ F, D.edgeW e c =
      (∏ e ∈ F, D.Kf e (priv c e) (c (Sum.inl (D.tail e))) (c (Sum.inl (D.head e)))) *
        ((∏ e ∈ F \ D.edgesOf T, D.Zf e (c (Sum.inl (D.tail e))) (c (Sum.inl (D.head e)))) *
          ∏ e ∈ D.edgesOf T, D.Zf e (c (Sum.inl (D.tail e))) (c (Sum.inl (D.head e)))) := by
    intro c
    rw [Finset.prod_sdiff hT, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun e _ => ?_
    unfold edgeW Kf
    rw [div_mul_cancel₀ _ (D.Zf_pos' _ _ _).ne']
  have hK : ∀ c : ECoord V Ed Q → E,
      ∏ e ∈ FJ, D.Kf e (priv c e) (c (Sum.inl (D.tail e))) (c (Sum.inl (D.head e))) =
        (∏ e ∈ FJ \ F, D.Kf e (priv c e) (c (Sum.inl (D.tail e))) (c (Sum.inl (D.head e)))) *
          ∏ e ∈ F, D.Kf e (priv c e) (c (Sum.inl (D.tail e))) (c (Sum.inl (D.head e))) :=
    fun c => (Finset.prod_sdiff hFJ).symm
  rw [hK a, hK a', hW a, hW a', hR, hH]
  exact db_alg hdbν

/-- **`pay:elim`, first half**: the lift `L(ν)` of a Gibbs measure `ν` of `γ̄` is a Gibbs measure
of `γ`. -/
theorem lift_isGibbs [Countable V] [Countable Ed] {ν : Measure (V → E)}
    (hν : D.gammaBar.toHard.IsGibbs ν) : D.gamma.toHard.IsGibbs (D.lift ν) := by
  haveI := hν.1
  refine D.gamma.toHard.isGibbs_of_db ?_ fun S₀ => ?_
  · have hk : ∀ k : Ed ⊕ V, ∀ᵐ x ∂(D.lift ν), 0 < D.gamma.φ k x := by
      intro k
      rcases k with e | v
      · exact D.ae_edgeW_pos ν e
      · have h1 : ∀ᵐ σ ∂ν, 0 < D.κ v (σ v) := hν.2.1.mono fun σ hσ =>
          D.gammaBar.φ_pos_of_W_pos hσ (k := Sum.inr v) (i := v) (Finset.mem_singleton_self _)
        have h2 : ∀ᵐ σ ∂((D.lift ν).map spins), 0 < D.κ v (σ v) := by
          rw [D.map_spins_lift ν]; exact h1
        exact ae_of_ae_map measurable_spins.aemeasurable h2
    filter_upwards [ae_all_iff.2 hk] with x hx
    exact D.gamma.W_pos_of_φ_pos hx
  · have hT : D.edgesOf (vertsIn S₀) ⊆ D.edgesOf (vertsIn S₀) ∪ edgesIn S₀ :=
      Finset.subset_union_left
    have hF : ∀ e ∈ D.edgesOf (vertsIn S₀) ∪ edgesIn S₀,
        e ∈ D.edgesOf (vertsIn S₀) ∨ Nonempty (Q e) := fun e he =>
      (Finset.mem_union.1 he).imp id edgesIn_nonempty
    refine ⟨closedSet (vertsIn S₀) (D.edgesOf (vertsIn S₀) ∪ edgesIn S₀),
      (subset_closedSet S₀).trans (closedSet_mono (Finset.Subset.refl _)
        Finset.subset_union_right), fun J₀ => ?_⟩
    obtain ⟨h1, h2, h3, h4⟩ := D.closed_cofinal (vertsIn S₀)
      (D.edgesOf (vertsIn S₀) ∪ edgesIn S₀) J₀
    exact ⟨_, h1, closedSet_mono h2 h3,
      D.gamma_range_subset hT hF h2 h3 ((D.endsOf_mono h3).trans h4),
      D.lift_db hν hT hF h2 h3 h4⟩

/-- **`pay:elim`, second half (the spins)**: the spin marginal of a Gibbs measure of `γ` is a
Gibbs measure of `γ̄`. -/
theorem isGibbs_map_spins [Nonempty E] [Countable V] {μ : Measure (ECoord V Ed Q → E)}
    (hμ : D.gamma.toHard.IsGibbs μ) : D.gammaBar.toHard.IsGibbs (μ.map spins) := by
  haveI := hμ.1
  haveI : IsProbabilityMeasure (μ.map spins) :=
    (Measure.isProbabilityMeasure_map_iff measurable_spins.aemeasurable).2 inferInstance
  refine D.gammaBar.toHard.isGibbs_of_db ?_ fun T => ⟨T, Finset.Subset.refl _, fun J₀ => ?_⟩
  · rw [ae_map_iff measurable_spins.aemeasurable D.gammaBar.toHard.measurableSet_pos]
    filter_upwards [hμ.2.1] with x hx
    refine D.gammaBar.W_pos_of_φ_pos fun k => ?_
    rcases k with e | v
    · exact D.Zf_pos' _ _ _
    · exact D.gamma.φ_pos_of_W_pos hx (k := Sum.inr v) (i := Sum.inl v)
        (Finset.mem_singleton_self _)
  · have hTJ : T ⊆ J₀ ∪ T ∪ D.endsOf (D.edgesOf T) := fun v hv =>
      Finset.mem_union_left _ (Finset.mem_union_right _ hv)
    have hE : D.endsOf (D.edgesOf T) ⊆ J₀ ∪ T ∪ D.endsOf (D.edgesOf T) :=
      Finset.subset_union_right
    refine ⟨J₀ ∪ T ∪ D.endsOf (D.edgesOf T),
      fun v hv => Finset.mem_union_left _ (Finset.mem_union_left _ hv), hTJ,
      D.gammaBar_range_subset hTJ hE, ?_⟩
    intro s s' hss'
    generalize J₀ ∪ T ∪ D.endsOf (D.edgesOf T) = TJ at hTJ hE ⊢
    have hT : D.edgesOf T ⊆ D.edgesOf T := Finset.Subset.refl _
    have hF : ∀ e ∈ D.edgesOf T, e ∈ D.edgesOf T ∨ Nonempty (Q e) := fun e he => Or.inl he
    let c₀ : ECoord V Ed Q → E := fun _ => Classical.arbitrary E
    let a : ECoord V Ed Q → E := fun i => match i with
      | Sum.inl v => s v
      | Sum.inr p => c₀ (Sum.inr p)
    let a' : ECoord V Ed Q → E := fun i => match i with
      | Sum.inl v => s' v
      | Sum.inr p => c₀ (Sum.inr p)
    have hP : (closedSet ∅ (D.edgesOf T) : Finset (ECoord V Ed Q)) ⊆
        closedSet TJ (D.edgesOf T) :=
      closedSet_mono (Finset.empty_subset _) (Finset.Subset.refl _)
    have hdb := D.gamma.toHard.db_of_isGibbs hμ (closedSet_mono hTJ (Finset.Subset.refl _))
      (D.gamma_range_subset hT hF hTJ (Finset.Subset.refl _) hE)
    have hν : ∀ c : ECoord V Ed Q → E, (μ.map spins).real (cyl TJ (spins c)) =
        ∑ h : (closedSet ∅ (D.edgesOf T) : Finset (ECoord V Ed Q)) → E,
          μ.real (cyl (closedSet TJ (D.edgesOf T)) (fillOn c (closedSet ∅ (D.edgesOf T)) h)) := by
      intro c
      rw [map_spins_real, ← closedSet_sdiff (T := TJ) (F := D.edgesOf T) (F' := D.edgesOf T)
        (fun e he _ => he)]
      exact measureReal_cyl_sdiff μ hP c
    have hWb : ∀ c : ECoord V Ed Q → E, D.gammaBar.toHard.W T (spins c) =
        ∑ h : (closedSet ∅ (D.edgesOf T) : Finset (ECoord V Ed Q)) → E,
          D.gamma.toHard.W (closedSet T (D.edgesOf T)) (fillOn c (closedSet ∅ (D.edgesOf T)) h) := by
      intro c
      rw [D.sum_gamma_W_fill hT hF c, D.gammaBar_W]
      rfl
    have hpair : ∀ h h' : (closedSet ∅ (D.edgesOf T) : Finset (ECoord V Ed Q)) → E,
        μ.real (cyl (closedSet TJ (D.edgesOf T)) (fillOn a (closedSet ∅ (D.edgesOf T)) h)) *
            D.gamma.toHard.W (closedSet T (D.edgesOf T))
              (fillOn a' (closedSet ∅ (D.edgesOf T)) h') =
          μ.real (cyl (closedSet TJ (D.edgesOf T)) (fillOn a' (closedSet ∅ (D.edgesOf T)) h')) *
            D.gamma.toHard.W (closedSet T (D.edgesOf T))
              (fillOn a (closedSet ∅ (D.edgesOf T)) h) := by
      intro h h'
      refine hdb _ _ fun i hi => ?_
      rcases i with v | ⟨e, q⟩
      · rw [fillOn_privs_inl, fillOn_privs_inl]
        exact hss' v fun hv => hi (inl_mem_closedSet.2 hv)
      · have he : e ∉ D.edgesOf T := fun he => hi (inr_mem_closedSet.2 he)
        rw [fillOn_of_not_mem _ _ (fun hm => he (inr_mem_closedSet.1 hm)),
          fillOn_of_not_mem _ _ (fun hm => he (inr_mem_closedSet.1 hm))]
    show (μ.map spins).real (cyl TJ (spins a)) * D.gammaBar.toHard.W T (spins a') =
      (μ.map spins).real (cyl TJ (spins a')) * D.gammaBar.toHard.W T (spins a)
    rw [hν a, hν a', hWb a, hWb a', Finset.sum_mul_sum, Finset.sum_mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun h' _ => hpair h h'

/-- **`pay:elim`, second half (the private coordinates)**: a Gibbs measure of `γ` is the lift of its
spin marginal, `μ = L(μ ∘ σ⁻¹)`: given the spins, the private coordinates of the edges are
independent with laws `K_e`. -/
theorem eq_lift {μ : Measure (ECoord V Ed Q → E)} (hμ : D.gamma.toHard.IsGibbs μ) :
    μ = D.lift (μ.map spins) := by
  classical
  haveI := hμ.1
  haveI : IsProbabilityMeasure (μ.map spins) :=
    (Measure.isProbabilityMeasure_map_iff measurable_spins.aemeasurable).2 inferInstance
  refine D.ext_closed fun T F hTF a => ?_
  rw [D.lift_cyl_real _ hTF a, map_spins_real]
  obtain ⟨Fp, hFp⟩ : ∃ Fp : Finset Ed, Fp = F.filter fun e => Nonempty (Q e) := ⟨_, rfl⟩
  have hFpF : Fp ⊆ F := by rw [hFp]; exact Finset.filter_subset _ _
  have hT : D.edgesOf (∅ : Finset V) ⊆ Fp := by simp [edgesOf]
  have hF : ∀ e ∈ Fp, e ∈ D.edgesOf ∅ ∨ Nonempty (Q e) := by
    intro e he
    rw [hFp] at he
    exact Or.inr (Finset.mem_filter.1 he).2
  have hS : (closedSet ∅ Fp : Finset (ECoord V Ed Q)) ⊆ closedSet T F :=
    closedSet_mono (Finset.empty_subset _) hFpF
  have hdb := D.gamma.toHard.db_of_isGibbs hμ hS
    (D.gamma_range_subset hT hF (Finset.empty_subset _) hFpF ((D.endsOf_mono hFpF).trans hTF))
  have hsumμ : μ.real (cyl (closedSet T ∅) a) =
      ∑ h : (closedSet ∅ Fp : Finset (ECoord V Ed Q)) → E,
        μ.real (cyl (closedSet T F) (fillOn a (closedSet ∅ Fp) h)) := by
    have hsub : ∀ e ∈ F, Nonempty (Q e) → e ∈ Fp := by
      intro e he hq
      rw [hFp]
      exact Finset.mem_filter.2 ⟨he, hq⟩
    rw [← closedSet_sdiff (T := T) (F := F) (F' := Fp) hsub]
    exact measureReal_cyl_sdiff μ hS a
  have hbal : μ.real (cyl (closedSet T F) a) *
      ∑ h : (closedSet ∅ Fp : Finset (ECoord V Ed Q)) → E,
        D.gamma.toHard.W (closedSet ∅ Fp) (fillOn a (closedSet ∅ Fp) h) =
      D.gamma.toHard.W (closedSet ∅ Fp) a * μ.real (cyl (closedSet T ∅) a) := by
    rw [hsumμ, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    have h1 := hdb a (fillOn a (closedSet ∅ Fp) h) fun i hi => (fillOn_of_not_mem a h hi).symm
    linarith
  rw [D.sum_gamma_W_fill hT hF a, D.gamma_W hT hF, Finset.prod_empty, mul_one, mul_one] at hbal
  have hZpos : 0 < ∏ e ∈ Fp, D.Zf e (a (Sum.inl (D.tail e))) (a (Sum.inl (D.head e))) :=
    Finset.prod_pos fun e _ => D.Zf_pos' _ _ _
  have hKZ : ∏ e ∈ Fp, D.edgeW e a =
      (∏ e ∈ Fp, D.Kf e (priv a e) (a (Sum.inl (D.tail e))) (a (Sum.inl (D.head e)))) *
        ∏ e ∈ Fp, D.Zf e (a (Sum.inl (D.tail e))) (a (Sum.inl (D.head e))) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun e _ => ?_
    unfold edgeW Kf
    rw [div_mul_cancel₀ _ (D.Zf_pos' _ _ _).ne']
  have hKF : ∏ e ∈ F, D.Kf e (priv a e) (a (Sum.inl (D.tail e))) (a (Sum.inl (D.head e))) =
      ∏ e ∈ Fp, D.Kf e (priv a e) (a (Sum.inl (D.tail e))) (a (Sum.inl (D.head e))) := by
    rw [hFp, Finset.prod_filter_of_ne]
    intro e _ hne
    by_contra hq
    exact hne (D.Kf_of_isEmpty (not_nonempty_iff.1 hq) _ _ _)
  rw [hKF]
  apply mul_right_cancel₀ hZpos.ne'
  rw [hKZ] at hbal
  linear_combination hbal

/-- **`pay:elim`** (generalized by vertex factors): `L` is a bijection from the Gibbs measures of
`γ̄` onto the Gibbs measures of `γ`, and its inverse is the spin marginal. -/
theorem elim [Nonempty E] [Countable V] [Countable Ed] (μ : Measure (ECoord V Ed Q → E)) :
    D.gamma.toHard.IsGibbs μ ↔
      ∃ ν : Measure (V → E), D.gammaBar.toHard.IsGibbs ν ∧ μ = D.lift ν := by
  constructor
  · intro hμ
    exact ⟨μ.map spins, D.isGibbs_map_spins hμ, D.eq_lift hμ⟩
  · rintro ⟨ν, hν, rfl⟩
    exact D.lift_isGibbs hν

/-- `L` is injective (its inverse is the spin marginal). -/
theorem lift_injective {ν ν' : Measure (V → E)} [IsProbabilityMeasure ν]
    [IsProbabilityMeasure ν'] (h : D.lift ν = D.lift ν') : ν = ν' :=
  calc ν = (D.lift ν).map spins := (D.map_spins_lift ν).symm
    _ = (D.lift ν').map spins := by rw [h]
    _ = ν' := D.map_spins_lift ν'

end Theorems

end ElimData

end Gibbs

end UPD

/-
# Ising models on graphs and `set:dobrushin` (uniqueness) from `H1`

`set:sub-ising`: a countable graph `G = (V, E)` in which every vertex has at most four neighbours,
couplings `J : E → [0, ∞)`, spins `σ ∈ {±1}^V`, one factor `exp(J_uv σ_u σ_v)` for each edge `uv`.
Here a graph is given by finite neighbour sets (`IsingGraph`), symmetric and irreflexive, and the
couplings by a function on unordered pairs `Sym2 V`. The weight of a finite set `Λ` is the product
of the factors of the edges meeting `Λ`; it is a `WeightSystem`, so its kernels form a quasilocal
specification (`Gibbs/Weights.lean`).

Main result: `IsingGraph.dobrushin_unique` — `set:dobrushin`, uniqueness half: if every vertex has
at most four neighbours and `J ≤ J̄` with `4 tanh J̄ < 1`, then, given `H1`, any two measures that
satisfy the DLR identity of the Ising model on `G` are equal. The computation of the paper's proof
(`P(σ_u = +1) = ½(1 + tanh h)`, a change of one neighbour moves this by at most `tanh J̄`) is
`IsingGraph.dobrushinCoeff_le`; the specialisation of `H1` is proved, not assumed (QB, D8).
Existence of a Gibbs measure is a separate statement (compactness), not proved here.
-/
import UndecidablePhaseDiagram.Gibbs.Weights
import Mathlib.Analysis.SpecialFunctions.Exp

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace UPD

namespace Gibbs

/-! ## Two real-analysis facts -/

/-- The logistic function `L(x) = e^x / (e^x + e^{-x}) = ½(1 + tanh x)`. -/
def logistic (x : ℝ) : ℝ := Real.exp x / (Real.exp x + Real.exp (-x))

theorem logistic_eq (x : ℝ) : logistic x = Real.exp (2 * x) / (Real.exp (2 * x) + 1) := by
  have h1 : Real.exp (2 * x) = Real.exp x * Real.exp x := by rw [← Real.exp_add]; ring_nf
  have h2 : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
  have hx := Real.exp_pos x
  have hmx := Real.exp_pos (-x)
  unfold logistic
  rw [h1, div_eq_div_iff (by positivity) (by positivity)]
  nlinarith [h2]

theorem logistic_mono {a b : ℝ} (h : b ≤ a) : logistic b ≤ logistic a := by
  rw [logistic_eq, logistic_eq]
  have ha := Real.exp_pos (2 * a)
  have hb := Real.exp_pos (2 * b)
  have hab : Real.exp (2 * b) ≤ Real.exp (2 * a) := Real.exp_le_exp.2 (by linarith)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

theorem tanh_eq' (D : ℝ) : Real.tanh D = (Real.exp (2 * D) - 1) / (Real.exp (2 * D) + 1) := by
  have h1 : Real.exp (2 * D) = Real.exp D * Real.exp D := by rw [← Real.exp_add]; ring_nf
  have h2 : Real.exp D * Real.exp (-D) = 1 := by rw [← Real.exp_add]; simp
  have hx := Real.exp_pos D
  have hmx := Real.exp_pos (-D)
  rw [Real.tanh_eq, h1, div_eq_div_iff (by positivity) (by positivity)]
  nlinarith [h2]

/-- `set:dobrushin`, the computation: if the field changes by at most `2D`, the probability of
`+1` changes by at most `tanh D`. -/
theorem abs_logistic_sub_le {a b D : ℝ} (hab : |a - b| ≤ 2 * D) :
    |logistic a - logistic b| ≤ Real.tanh D := by
  -- reduce to `b ≤ a`
  wlog h : b ≤ a generalizing a b
  · rw [abs_sub_comm]; exact this (by rwa [abs_sub_comm]) (le_of_not_ge h)
  have hD : 0 ≤ D := by linarith [abs_nonneg (a - b)]
  have h2D : a ≤ b + 2 * D := by linarith [le_abs_self (a - b)]
  rw [abs_of_nonneg (sub_nonneg.2 (logistic_mono h))]
  calc logistic a - logistic b ≤ logistic (b + 2 * D) - logistic b := by
        linarith [logistic_mono h2D]
    _ ≤ Real.tanh D := by
        rw [logistic_eq, logistic_eq, tanh_eq']
        set y := Real.exp (2 * b) with hy
        set q := Real.exp (2 * D) with hq
        have hy0 : 0 < y := Real.exp_pos _
        have hq1 : 1 ≤ q := by rw [hq]; exact Real.one_le_exp (by linarith)
        have hyq : Real.exp (2 * (b + 2 * D)) = y * q * q := by
          rw [hy, hq, ← Real.exp_add, ← Real.exp_add]; ring_nf
        rw [hyq, div_sub_div _ _ (by positivity) (by positivity),
          div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [sq_nonneg (1 - y * q), mul_nonneg (sub_nonneg.2 hq1) hy0.le,
          mul_nonneg (mul_nonneg (sub_nonneg.2 hq1) hy0.le) (sq_nonneg (1 - y * q))]

/-! ## Single-site kernels of a weight system -/

/-- The fillings of a single site `i` are its values. -/
def singletonEquiv {I E : Type} (i : I) : (({i} : Finset I) → E) ≃ E where
  toFun ζ := ζ ⟨i, Finset.mem_singleton_self i⟩
  invFun s := fun _ => s
  left_inv ζ := by
    funext x
    have : x = ⟨i, Finset.mem_singleton_self i⟩ := Subtype.ext (Finset.mem_singleton.1 x.2)
    subst this; rfl
  right_inv _ := rfl

theorem fillOn_singleton {I E : Type} [DecidableEq I] (ω : I → E) (i : I) (ζ : ({i} : Finset I) → E) :
    fillOn ω {i} ζ = Function.update ω i (singletonEquiv i ζ) := by
  funext k
  by_cases hk : k = i
  · subst hk; simp [fillOn, singletonEquiv]
  · simp [fillOn, hk]

namespace WeightSystem

variable {I E : Type} [DecidableEq I] [Fintype E] (ws : WeightSystem I E)

/-- The kernel of a single site: a weighted average over the values at `i`. -/
theorem expect_singleton (i : I) (ω : I → E) (F : (I → E) → ℝ) :
    ws.expect {i} ω F = (∑ s : E, ws.W {i} (Function.update ω i s) * F (Function.update ω i s)) /
      ∑ s : E, ws.W {i} (Function.update ω i s) := by
  simp only [expect, prob, Z, div_mul_eq_mul_div, ← Finset.sum_div]
  congr 1
  · exact Fintype.sum_equiv (singletonEquiv i) _ _ (fun ζ => by rw [fillOn_singleton])
  · exact Fintype.sum_equiv (singletonEquiv i) _ _ (fun ζ => by rw [fillOn_singleton])

end WeightSystem

/-! ## Ising models on graphs -/

/-- `set:sub-ising`: a countable graph given by finite neighbour sets (symmetric, irreflexive)
and couplings `J_e ≥ 0` on unordered pairs (only the pairs that are edges matter). -/
structure IsingGraph (V : Type) [DecidableEq V] where
  /-- The neighbours of a vertex. -/
  nbr : V → Finset V
  symm : ∀ u v, v ∈ nbr u → u ∈ nbr v
  irrefl : ∀ u, u ∉ nbr u
  /-- The coupling of an edge. -/
  J : Sym2 V → ℝ
  J_nonneg : ∀ e, 0 ≤ J e

namespace IsingGraph

variable {V : Type} [DecidableEq V] (G : IsingGraph V)

/-- The edges `{u, v}` with an endpoint `u ∈ Λ`. -/
def edgesMeeting (Λ : Finset V) : Finset (Sym2 V) :=
  Λ.biUnion fun u => (G.nbr u).image fun v => s(u, v)

/-- `σ_u σ_v` for the edge `{u, v}`. -/
def pairVal (σ : V → Spin) : Sym2 V → ℝ :=
  Sym2.lift ⟨fun u v => Ising.val (σ u) * Ising.val (σ v), fun _ _ => mul_comm _ _⟩

theorem pairVal_mk (σ : V → Spin) (u v : V) :
    pairVal σ s(u, v) = Ising.val (σ u) * Ising.val (σ v) := rfl

/-- `∑_{e meets Λ} J_e σ_u σ_v`. -/
def energySum (Λ : Finset V) (σ : V → Spin) : ℝ :=
  ∑ e ∈ G.edgesMeeting Λ, G.J e * pairVal σ e

/-- The Ising weight of `Λ`: the product of the factors `exp(J_e σ_u σ_v)` of the edges meeting
`Λ`. -/
def weight (Λ : Finset V) (σ : V → Spin) : ℝ := Real.exp (G.energySum Λ σ)

theorem mem_edgesMeeting {Λ : Finset V} {e : Sym2 V} :
    e ∈ G.edgesMeeting Λ ↔ ∃ u ∈ Λ, ∃ v ∈ G.nbr u, s(u, v) = e := by
  simp [edgesMeeting]

theorem edgesMeeting_mono {Λ Δ : Finset V} (h : Λ ⊆ Δ) : G.edgesMeeting Λ ⊆ G.edgesMeeting Δ :=
  Finset.biUnion_subset_biUnion_of_subset_left _ h

/-- An edge meeting `Δ` but not `Λ` has no endpoint in `Λ`. -/
theorem endpoints_of_mem_sdiff {Λ Δ : Finset V} {u v : V}
    (h : s(u, v) ∈ G.edgesMeeting Δ \ G.edgesMeeting Λ) : u ∉ Λ ∧ v ∉ Λ := by
  rw [Finset.mem_sdiff, G.mem_edgesMeeting, G.mem_edgesMeeting] at h
  obtain ⟨⟨a, -, b, hb, hab⟩, hnot⟩ := h
  rcases Sym2.eq_iff.1 hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨fun hu => hnot ⟨a, hu, b, hb, rfl⟩,
      fun hv => hnot ⟨b, hv, a, G.symm _ _ hb, Sym2.eq_swap⟩⟩
  · exact ⟨fun hu => hnot ⟨b, hu, a, G.symm _ _ hb, rfl⟩,
      fun hv => hnot ⟨a, hv, b, hb, Sym2.eq_swap⟩⟩

/-- The Ising model on `G` as a weight system. -/
def toWeightSystem : WeightSystem V Spin where
  W := G.weight
  pos _ _ := Real.exp_pos _
  range Λ := Λ ∪ Λ.biUnion G.nbr
  isLocal Λ ω ω' h := by
    unfold weight energySum
    congr 1
    refine Finset.sum_congr rfl fun e he => ?_
    obtain ⟨u, hu, v, hv, rfl⟩ := G.mem_edgesMeeting.1 he
    rw [pairVal_mk, pairVal_mk, h u (Finset.mem_union_left _ hu),
      h v (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨u, hu, hv⟩))]
  ratio Λ Δ hΛΔ ω ω' h := by
    unfold weight energySum
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    rw [← Finset.sum_sdiff (G.edgesMeeting_mono hΛΔ), ← Finset.sum_sdiff (G.edgesMeeting_mono hΛΔ)]
    have hR : ∑ e ∈ G.edgesMeeting Δ \ G.edgesMeeting Λ, G.J e * pairVal ω e =
        ∑ e ∈ G.edgesMeeting Δ \ G.edgesMeeting Λ, G.J e * pairVal ω' e := by
      refine Finset.sum_congr rfl fun e he => ?_
      induction e using Sym2.ind with
      | h u v =>
        obtain ⟨hu, hv⟩ := G.endpoints_of_mem_sdiff he
        rw [pairVal_mk, pairVal_mk, h u hu, h v hv]
    rw [hR]; ring

theorem toWeightSystem_W : G.toWeightSystem.W = G.weight := rfl

/-- The local field `h_i(ω) = ∑_{v ∼ i} J_{iv} σ_v` at a vertex. -/
def field (i : V) (ω : V → Spin) : ℝ := ∑ v ∈ G.nbr i, G.J s(i, v) * Ising.val (ω v)

theorem edgesMeeting_singleton (i : V) :
    G.edgesMeeting {i} = (G.nbr i).image fun v => s(i, v) := by
  simp [edgesMeeting]

/-- The single-site weight: `exp(σ_i h_i(ω))`. -/
theorem weight_update (i : V) (ω : V → Spin) (s : Spin) :
    G.weight {i} (Function.update ω i s) = Real.exp (Ising.val s * G.field i ω) := by
  unfold weight energySum field
  congr 1
  rw [G.edgesMeeting_singleton, Finset.sum_image (fun v _ w _ h => Sym2.congr_right.1 h),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun v hv => ?_
  have hvi : v ≠ i := fun h => G.irrefl i (h ▸ hv)
  rw [pairVal_mk, Function.update_self, Function.update_of_ne hvi]
  ring

theorem sum_spin (f : Spin → ℝ) : ∑ s : Spin, f s = f .plus + f .minus :=
  Fintype.sum_eq_add _ _ (by decide) (fun x hx => by cases x <;> simp at hx)

/-- `P(σ_i = +1 | ω) = L(h_i(ω))`, and `P(σ_i = -1 | ω) = 1 - L(h_i(ω))`: the kernel of a single
site applied to a function of `σ_i`. -/
theorem expect_singleton_of_site (i : V) (ω : V → Spin) (g : Spin → ℝ) :
    G.toWeightSystem.expect {i} ω (fun η => g (η i)) =
      logistic (G.field i ω) * g .plus + (1 - logistic (G.field i ω)) * g .minus := by
  rw [WeightSystem.expect_singleton]
  simp only [toWeightSystem_W, weight_update, Function.update_self, sum_spin, Ising.val,
    one_mul, neg_one_mul]
  unfold logistic
  have h1 := Real.exp_pos (G.field i ω)
  have h2 := Real.exp_pos (-G.field i ω)
  field_simp
  ring

/-- The field depends only on the neighbours. -/
theorem field_congr (i : V) {ω η : V → Spin} (h : ∀ v ∈ G.nbr i, ω v = η v) :
    G.field i ω = G.field i η := by
  unfold field
  exact Finset.sum_congr rfl fun v hv => by rw [h v hv]

/-- Changing the spin at one neighbour `j` moves the field by at most `2 J_{ij}`. -/
theorem abs_field_sub_le (i j : V) {ω η : V → Spin} (h : ∀ k, k ≠ j → ω k = η k) :
    |G.field i ω - G.field i η| ≤ 2 * G.J s(i, j) := by
  unfold field
  rw [← Finset.sum_sub_distrib]
  by_cases hj : j ∈ G.nbr i
  · rw [← Finset.add_sum_erase _ _ hj, Finset.sum_eq_zero (fun v hv => by
      rw [h v (Finset.ne_of_mem_erase hv), sub_self]), add_zero, ← mul_sub]
    have hJ := G.J_nonneg s(i, j)
    rw [abs_mul, abs_of_nonneg hJ]
    have : |Ising.val (ω j) - Ising.val (η j)| ≤ 2 := by
      cases ω j <;> cases η j <;> norm_num [Ising.val]
    nlinarith
  · rw [Finset.sum_eq_zero (fun v hv => by
      rw [h v (fun hvj => hj (hvj ▸ hv)), sub_self]), abs_zero]
    linarith [G.J_nonneg s(i, j)]

section Measure

variable [Countable V]

omit [DecidableEq V] in
/-- A change of the field by `δ` changes the law of `σ_i` on any set by at most
`|L(h) - L(h')|`. -/
theorem abs_sitePart_le (p q : Prop) [Decidable p] [Decidable q] (a b : ℝ) :
    |(if p then a else 0) + (if q then 1 - a else 0) -
      ((if p then b else 0) + (if q then 1 - b else 0))| ≤ |a - b| := by
  split_ifs <;> refine abs_le.2 ⟨?_, ?_⟩ <;>
    linarith [le_abs_self (a - b), neg_abs_le (a - b), abs_nonneg (a - b)]

open Classical in
/-- The one-site law at `i` of a set `A` of spin values. -/
theorem siteLaw_apply (i : V) (ω : V → Spin) (A : Set Spin) :
    (G.toWeightSystem.toSpecification.siteLaw i ω A).toReal =
      (if Spin.plus ∈ A then logistic (G.field i ω) else 0) +
        (if Spin.minus ∈ A then 1 - logistic (G.field i ω) else 0) := by
  have hm : Measurable (fun η : V → Spin => η i) := measurable_pi_apply i
  have hA : MeasurableSet A := DiscreteMeasurableSpace.forall_measurableSet A
  rw [Specification.siteLaw, Measure.map_apply hm hA, WeightSystem.toSpecification_kernel,
    WeightSystem.kernel_apply _ _ _ (hm hA)]
  have hind : ((fun η : V → Spin => η i) ⁻¹' A).indicator (1 : (V → Spin) → ℝ) =
      fun η => (fun s : Spin => if s ∈ A then (1 : ℝ) else 0) (η i) := by
    funext η; by_cases h : η i ∈ A <;> simp [h]
  have hL0 : 0 ≤ logistic (G.field i ω) := by
    unfold logistic; positivity
  have hL1 : logistic (G.field i ω) ≤ 1 := by
    unfold logistic
    rw [div_le_one (by positivity)]
    linarith [Real.exp_pos (-G.field i ω)]
  rw [hind, G.expect_singleton_of_site i ω (fun s => if s ∈ A then (1 : ℝ) else 0),
    ENNReal.toReal_ofReal]
  · split_ifs <;> ring
  · split_ifs <;> nlinarith

open Classical in
/-- **`set:dobrushin`, the computation.** Dobrushin's coefficient `c_ij` is at most `tanh J̄` for a
neighbour `j` of `i` and `0` otherwise. -/
theorem dobrushinCoeff_le (Jbar : ℝ) (hJ : ∀ e, G.J e ≤ Jbar) (i j : V) :
    G.toWeightSystem.toSpecification.dobrushinCoeff i j ≤
      if j ∈ G.nbr i then ENNReal.ofReal (Real.tanh Jbar) else 0 := by
  refine iSup_le fun ω => iSup_le fun η => iSup_le fun h => iSup_le fun A => ?_
  rw [G.siteLaw_apply, G.siteLaw_apply]
  by_cases hj : j ∈ G.nbr i
  · rw [if_pos hj]
    refine ENNReal.ofReal_le_ofReal ?_
    have hL := abs_logistic_sub_le (D := Jbar)
      ((G.abs_field_sub_le i j h).trans (by linarith [hJ s(i, j)]))
    exact (abs_sitePart_le _ _ _ _).trans hL
  · rw [if_neg hj]
    have hf : G.field i ω = G.field i η :=
      G.field_congr i fun v hv => h v (fun hvj => hj (hvj ▸ hv))
    simp [hf]

/-- **`set:dobrushin`, the condition.** With at most four neighbours per vertex and
`4 tanh J̄ < 1`, Dobrushin's constant is `< 1`. -/
theorem dobrushinConstant_lt_one (Jbar : ℝ) (hJ : ∀ e, G.J e ≤ Jbar)
    (hdeg : ∀ i, (G.nbr i).card ≤ 4) (htanh : 4 * Real.tanh Jbar < 1) :
    G.toWeightSystem.toSpecification.dobrushinConstant < 1 := by
  have hrow : ∀ i, ∑' j, G.toWeightSystem.toSpecification.dobrushinCoeff i j ≤
      ENNReal.ofReal (4 * Real.tanh Jbar) := by
    intro i
    calc ∑' j, G.toWeightSystem.toSpecification.dobrushinCoeff i j
        ≤ ∑' j, (if j ∈ G.nbr i then ENNReal.ofReal (Real.tanh Jbar) else 0) :=
          ENNReal.tsum_le_tsum fun j => G.dobrushinCoeff_le Jbar hJ i j
      _ = ∑ j ∈ G.nbr i, ENNReal.ofReal (Real.tanh Jbar) := by
          rw [tsum_eq_sum (s := G.nbr i) (fun j hj => if_neg hj)]
          exact Finset.sum_congr rfl fun j hj => if_pos hj
      _ = ((G.nbr i).card : ℝ≥0∞) * ENNReal.ofReal (Real.tanh Jbar) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 4 * ENNReal.ofReal (Real.tanh Jbar) := by
          gcongr
          exact_mod_cast hdeg i
      _ = ENNReal.ofReal (4 * Real.tanh Jbar) := by
          rw [ENNReal.ofReal_mul (by norm_num)]; norm_num
  exact lt_of_le_of_lt (iSup_le hrow) (ENNReal.ofReal_lt_one.2 htanh)

/-- **`set:dobrushin`** (uniqueness), proved from `H1`: on a countable graph with at most four
neighbours per vertex and couplings `0 ≤ J ≤ J̄` with `4 tanh J̄ < 1`, any two measures satisfying
the DLR identity of the Ising model (`∫ F dμ = ∫ γ_Λ F dμ`, bounded measurable `F`) are equal. -/
theorem dobrushin_unique (h1 : H1) (Jbar : ℝ) (hJ : ∀ e, G.J e ≤ Jbar)
    (hdeg : ∀ i, (G.nbr i).card ≤ 4) (htanh : 4 * Real.tanh Jbar < 1)
    {μ ν : Measure (V → Spin)} (hμ : G.toWeightSystem.IsDLR μ)
    (hν : G.toWeightSystem.IsDLR ν) : μ = ν :=
  h1 V Spin G.toWeightSystem.toSpecification G.toWeightSystem.isQuasilocal
    (G.dobrushinConstant_lt_one Jbar hJ hdeg htanh) μ ν
    (G.toWeightSystem.isGibbsMeasure_of_isDLR hμ) (G.toWeightSystem.isGibbsMeasure_of_isDLR hν)

end Measure

end IsingGraph

end Gibbs

end UPD

/-
# Contours and their count (`set:peierls`)

The paper: "in a box with plus boundary condition the event `σ₀ = -1` forces a closed contour of
the dual lattice around the origin, made of edges between disagreeing spins; [...] A contour of
length `k` around the origin crosses the positive horizontal axis within distance `k/2` of the
origin, and starting from that crossing it is a closed walk of `k` steps [...]".

Here the dual lattice has the unit squares (plaquettes, named by their lower-left corner `p`) as
vertices and the bonds as edges: the bond `(x, false) = {x, x + e₁}` joins the plaquettes `x - e₂`
and `x`, the bond `(x, true) = {x, x + e₂}` joins `x - e₁` and `x`. A *walk* is a start plaquette
and a list of unit steps; a *closed trail* is a closed walk that uses no bond twice; a *contour*
(`IsCircuit`) is the bond set of a closed trail.
* `plaq_toFinset_walk`: the degree lemma (a trail from `p` to `q` has odd degree exactly at `p`
  and `q` when `p ≠ q`); so the bond set of a closed trail is even.
* `exists_circuit_subset`: a nonempty even set contains a contour (extend a trail until it closes).
* `exists_circuit_par`: an even set `D` with `par D 0 = 1` contains a contour `γ` with
  `par γ 0 = 1` ([gap] 2 of `STATUS.md`: the paper's "the contour" is a single closed trail).
* `circuit_code`: such a contour of size `k` is the bond set of a closed walk of `k` steps from a
  plaquette `(j, 0)` with `2 (j + 1) ≤ k` ([gap] 3: it crosses the positive and the negative
  horizontal half-axis), and `k` is even.
* `card_contours_le`: at most `m · 4^{2m}` contours of size `2m` inside a box.
* `plus_prob_minus_le`: under the plus measure in the box `B(n)`, `P(σ₀ = -1) ≤ 1296/4225 < 1/3`
  if `e^J ≥ 3`.

**[choice] (proof side).** The count differs from the printed one ("at most `k 3^k`", `k ≥ 4`,
total `1/12`): we count closed walks with `4` choices per step from one of `k/2` start plaquettes
and use that `k` is even, which gives `∑_{m ≥ 1} m (16/81)^m = 1296/4225 ≤ 1/3`. The conclusion
used by the paper (`ν⁺(σ₀ = -1) ≤ 1/3` when `e^J ≥ 3`) is the printed one.
-/
import UndecidablePhaseDiagram.Peierls.Flip
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Topology.Algebra.InfiniteSum.Order

set_option autoImplicit false

noncomputable section

namespace UPD

namespace Peierls

open Ising

/-! ## Walks on the dual lattice -/

set_option backward.isDefEq.respectTransparency false in
/-- A unit step of the dual lattice. -/
inductive Dir where
  | R | L | U | D
  deriving DecidableEq, Fintype

namespace Dir

/-- The displacement of a step. -/
def vec : Dir → Plane
  | R => e1
  | L => -e1
  | U => e2
  | D => -e2

end Dir

/-- The bond crossed by the step from the plaquette `p` in direction `d`. -/
def stepBond (p : Plane) : Dir → Bond
  | .R => (p + e1, true)
  | .L => (p, true)
  | .U => (p + e2, false)
  | .D => (p, false)

/-- The bonds crossed by the walk from `p` along `ds`, in order. -/
def walk : Plane → List Dir → List Bond
  | _, [] => []
  | p, d :: ds => stepBond p d :: walk (p + d.vec) ds

/-- The end plaquette of the walk from `p` along `ds`. -/
def walkEnd : Plane → List Dir → Plane
  | p, [] => p
  | p, d :: ds => walkEnd (p + d.vec) ds

@[simp] theorem walk_nil (p : Plane) : walk p [] = [] := rfl

@[simp] theorem walk_cons (p : Plane) (d : Dir) (ds : List Dir) :
    walk p (d :: ds) = stepBond p d :: walk (p + d.vec) ds := rfl

@[simp] theorem walkEnd_nil (p : Plane) : walkEnd p [] = p := rfl

@[simp] theorem walkEnd_cons (p : Plane) (d : Dir) (ds : List Dir) :
    walkEnd p (d :: ds) = walkEnd (p + d.vec) ds := rfl

theorem walk_append (p : Plane) (ds ds' : List Dir) :
    walk p (ds ++ ds') = walk p ds ++ walk (walkEnd p ds) ds' := by
  induction ds generalizing p with
  | nil => rfl
  | cons d ds ih => simp [ih]

theorem walkEnd_append (p : Plane) (ds ds' : List Dir) :
    walkEnd p (ds ++ ds') = walkEnd (walkEnd p ds) ds' := by
  induction ds generalizing p with
  | nil => rfl
  | cons d ds ih => simp [ih]

@[simp] theorem length_walk (p : Plane) (ds : List Dir) : (walk p ds).length = ds.length := by
  induction ds generalizing p with
  | nil => rfl
  | cons d ds ih => simp [ih]

/-! ## Incidence and the degree lemma -/

/-- `δ(r, p) = [r = p]` in `ZMod 2`. -/
def dlt (r p : Plane) : ZMod 2 := if r = p then 1 else 0

/-- Incidence of a bond and a plaquette, in `ZMod 2`: the bond `(x, false)` is a side of the
plaquettes `x` and `x - e₂`, the bond `(x, true)` of `x` and `x - e₁`. -/
def inc : Bond → Plane → ZMod 2
  | (x, false), r => dlt r x + dlt r (x - e2)
  | (x, true), r => dlt r x + dlt r (x - e1)

theorem inc_stepBond (p : Plane) (d : Dir) (r : Plane) :
    inc (stepBond p d) r = dlt r p + dlt r (p + d.vec) := by
  cases d <;> simp only [stepBond, inc, Dir.vec, add_sub_cancel_right, ← sub_eq_add_neg] <;>
    ring

/-- `plaq` is the sum of the incidences. -/
theorem plaq_eq_sum (γ : Finset Bond) (r : Plane) : plaq γ r = ∑ b ∈ γ, inc b r := by
  have h : ∀ b : Bond, inc b r = (if b = (r, false) then 1 else 0) +
      (if b = (r + e2, false) then 1 else 0) + (if b = (r, true) then 1 else 0) +
      (if b = (r + e1, true) then 1 else 0) := by
    rintro ⟨x, k⟩
    cases k <;> simp only [inc, dlt, Prod.mk.injEq, and_true, and_false, if_false, add_zero,
      zero_add, Bool.false_eq_true, Bool.true_eq_false, eq_sub_iff_add_eq, eq_comm (a := x)]
  simp only [h, Finset.sum_add_distrib, Finset.sum_ite_eq', plaq, ind]

/-- **The degree lemma**: along a walk from `p` to `q`, the incidences with `r` add up to
`[r = p] + [r = q]`. -/
theorem sum_inc_walk (p : Plane) (ds : List Dir) (r : Plane) :
    ((walk p ds).map (fun b => inc b r)).sum = dlt r p + dlt r (walkEnd p ds) := by
  induction ds generalizing p with
  | nil => simp only [walk_nil, List.map_nil, List.sum_nil, walkEnd_nil]; unfold dlt
           split_ifs <;> decide
  | cons d ds ih =>
    simp only [walk_cons, List.map_cons, List.sum_cons, ih, inc_stepBond, walkEnd_cons]
    linear_combination (dlt r (p + d.vec)) * two_eq_zero

/-- The degree lemma for trails (walks that use no bond twice). -/
theorem plaq_toFinset_walk {p : Plane} {ds : List Dir} (h : (walk p ds).Nodup) (r : Plane) :
    plaq (walk p ds).toFinset r = dlt r p + dlt r (walkEnd p ds) := by
  classical
  rw [plaq_eq_sum, List.sum_toFinset _ h, sum_inc_walk]

/-- The bond set of a closed trail is even. -/
theorem isEven_of_closed {p : Plane} {ds : List Dir} (h : (walk p ds).Nodup)
    (hc : walkEnd p ds = p) : IsEven (walk p ds).toFinset := by
  intro r
  rw [plaq_toFinset_walk h, hc]
  linear_combination (dlt r p) * two_eq_zero

/-- A bond incident to `q` is crossed by a step from `q`. -/
theorem exists_stepBond_of_inc {b : Bond} {q : Plane} (h : inc b q = 1) :
    ∃ d, stepBond q d = b := by
  obtain ⟨x, k⟩ := b
  cases k
  · simp only [inc, dlt] at h
    by_cases h1 : q = x
    · exact ⟨.D, by simp [stepBond, h1]⟩
    by_cases h2 : q = x - e2
    · exact ⟨.U, by simp [stepBond, h2]⟩
    simp [h1, h2] at h
  · simp only [inc, dlt] at h
    by_cases h1 : q = x
    · exact ⟨.L, by simp [stepBond, h1]⟩
    by_cases h2 : q = x - e1
    · exact ⟨.R, by simp [stepBond, h2]⟩
    simp [h1, h2] at h

/-- Every plaquette incident to a crossed bond is visited: the walk splits there. -/
theorem exists_split_of_inc {p : Plane} {ds : List Dir} {b : Bond} (hb : b ∈ walk p ds)
    {r : Plane} (hr : inc b r = 1) : ∃ A B : List Dir, ds = A ++ B ∧ walkEnd p A = r := by
  induction ds generalizing p with
  | nil => simp at hb
  | cons d ds ih =>
    rw [walk_cons, List.mem_cons] at hb
    rcases hb with rfl | hb
    · rw [inc_stepBond] at hr
      by_cases h1 : r = p
      · exact ⟨[], d :: ds, rfl, h1.symm⟩
      · have h2 : r = p + d.vec := by
          by_contra h2
          simp [dlt, h1, h2] at hr
        exact ⟨[d], ds, rfl, h2.symm⟩
    · obtain ⟨A, B, h, hA⟩ := ih hb
      exact ⟨d :: A, B, by simp [h], hA⟩

/-! ## Closed trails inside even sets -/

/-- **A trail in an even set extends to a closed trail** (by induction on the number of unused
bonds): at the end `q ≠ p` of a trail the trail has odd degree and the even set has even degree,
so an unused bond of the set leaves `q`. -/
theorem exists_closed_extension {γ : Finset Bond} (hγ : IsEven γ) :
    ∀ (t : ℕ) (p : Plane) (ds : List Dir), γ.card - ds.length = t → (walk p ds).Nodup →
      (∀ b ∈ walk p ds, b ∈ γ) → ∃ ds' : List Dir, ds.length ≤ ds'.length ∧
        (walk p ds').Nodup ∧ (∀ b ∈ walk p ds', b ∈ γ) ∧ walkEnd p ds' = p := by
  classical
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
  intro p ds ht hnd hsub
  by_cases hc : walkEnd p ds = p
  · exact ⟨ds, le_rfl, hnd, hsub, hc⟩
  set q := walkEnd p ds with hq
  have hT : plaq (walk p ds).toFinset q = 1 := by
    rw [plaq_toFinset_walk hnd, dlt, dlt, if_neg hc, if_pos hq, zero_add]
  have hsubF : (walk p ds).toFinset ⊆ γ := fun b hb => hsub b (List.mem_toFinset.1 hb)
  have hdiff : ∑ b ∈ γ \ (walk p ds).toFinset, inc b q ≠ 0 := by
    have h0 := hγ q
    rw [plaq_eq_sum] at h0 hT
    rw [Finset.sum_sdiff_eq_sub hsubF, h0, hT]
    decide
  obtain ⟨b, hb, hbq⟩ := Finset.exists_ne_zero_of_sum_ne_zero hdiff
  have hbq1 : inc b q = 1 := by
    have key : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
    exact key _ hbq
  obtain ⟨d, hd⟩ := exists_stepBond_of_inc hbq1
  rw [Finset.mem_sdiff, List.mem_toFinset] at hb
  have hw : walk p (ds ++ [d]) = walk p ds ++ [b] := by
    rw [walk_append, ← hq]; simp [hd]
  have hnd' : (walk p (ds ++ [d])).Nodup := by
    rw [hw, List.nodup_append]
    refine ⟨hnd, List.nodup_singleton _, fun a ha c hc' => ?_⟩
    rw [List.mem_singleton] at hc'
    rintro rfl
    exact hb.2 (hc' ▸ ha)
  have hsub' : ∀ b' ∈ walk p (ds ++ [d]), b' ∈ γ := by
    rw [hw]
    intro b' hb'
    rcases List.mem_append.1 hb' with h | h
    · exact hsub b' h
    · rw [List.mem_singleton] at h; exact h ▸ hb.1
  have hlen : (ds ++ [d]).length ≤ γ.card := by
    have h1 := List.toFinset_card_of_nodup hnd'
    rw [length_walk] at h1
    rw [← h1]
    exact Finset.card_le_card fun b' hb' => hsub' b' (List.mem_toFinset.1 hb')
  simp only [List.length_append, List.length_singleton] at hlen
  obtain ⟨ds', hl, h1, h2, h3⟩ := ih (γ.card - (ds ++ [d]).length)
    (by simp only [List.length_append, List.length_singleton]; omega) p (ds ++ [d]) rfl hnd' hsub'
  exact ⟨ds', by simp only [List.length_append, List.length_singleton] at hl; omega, h1, h2, h3⟩

/-- `γ` is a contour: the bond set of a closed trail. -/
def IsCircuit (γ : Finset Bond) : Prop :=
  ∃ (p : Plane) (ds : List Dir), walkEnd p ds = p ∧ (walk p ds).Nodup ∧ (walk p ds).toFinset = γ

theorem IsCircuit.isEven {γ : Finset Bond} (h : IsCircuit γ) : IsEven γ := by
  obtain ⟨p, ds, hc, hnd, rfl⟩ := h
  exact isEven_of_closed hnd hc

/-- A bond is a side of the plaquette named by its first point. -/
theorem inc_self (b : Bond) : inc b b.1 = 1 := by
  obtain ⟨x, k⟩ := b
  have h1 : x ≠ x - e2 := by
    intro h
    have h' := congrArg Prod.snd h
    simp only [e2, Prod.snd_sub] at h'
    omega
  have h2 : x ≠ x - e1 := by
    intro h
    have h' := congrArg Prod.fst h
    simp only [e1, Prod.fst_sub] at h'
    omega
  cases k <;> simp [inc, dlt, h1, h2]

/-- **A nonempty even set contains a contour.** -/
theorem exists_circuit_subset {γ : Finset Bond} (hγ : IsEven γ) (hne : γ.Nonempty) :
    ∃ T : Finset Bond, T.Nonempty ∧ T ⊆ γ ∧ IsCircuit T := by
  obtain ⟨b, hb⟩ := hne
  obtain ⟨d, hd⟩ := exists_stepBond_of_inc (inc_self b)
  obtain ⟨ds', hl, hnd, hsub, hc⟩ := exists_closed_extension hγ _ b.1 [d] rfl
    (by simp) (by simp [hd, hb])
  refine ⟨(walk b.1 ds').toFinset, ?_, fun b' hb' => hsub b' (List.mem_toFinset.1 hb'),
    b.1, ds', hc, hnd, rfl⟩
  obtain ⟨d', ds'', rfl⟩ : ∃ d' ds'', ds' = d' :: ds'' := by
    cases ds' with
    | nil => simp at hl
    | cons d' ds'' => exact ⟨d', ds'', rfl⟩
  exact ⟨stepBond b.1 d', by simp⟩

theorem par_sdiff {γ T : Finset Bond} (h : T ⊆ γ) (x : Plane) :
    par (γ \ T) x = par γ x - par T x := by
  unfold par
  exact Finset.sum_sdiff_eq_sub h

theorem isEven_sdiff {γ T : Finset Bond} (hγ : IsEven γ) (hT : IsEven T) (h : T ⊆ γ) :
    IsEven (γ \ T) := by
  intro r
  rw [plaq_eq_sum, Finset.sum_sdiff_eq_sub h, ← plaq_eq_sum, ← plaq_eq_sum, hγ r, hT r, sub_zero]

theorem par_empty (x : Plane) : par ∅ x = 0 := by simp [par]

/-- **An even set with `par D 0 = 1` contains a contour `γ` with `par γ 0 = 1`** (strong induction
on `|D|`: remove a contour of parity `0`). -/
theorem exists_circuit_par : ∀ (t : ℕ) (D : Finset Bond), D.card = t → IsEven D →
    par D 0 = 1 → ∃ γ ⊆ D, IsCircuit γ ∧ par γ 0 = 1 := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
  intro D ht hD hpar
  have hne : D.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    rw [par_empty] at hpar
    exact absurd hpar (by decide)
  obtain ⟨T, hTne, hTD, hT⟩ := exists_circuit_subset hD hne
  by_cases hTp : par T 0 = 1
  · exact ⟨T, hTD, hT, hTp⟩
  have hT0 : par T 0 = 0 := by
    have key : ∀ a : ZMod 2, a ≠ 1 → a = 0 := by decide
    exact key _ hTp
  have hcard : (D \ T).card < t := by
    rw [Finset.card_sdiff_of_subset hTD, ← ht]
    have := Finset.card_le_card hTD
    have := hTne.card_pos
    omega
  obtain ⟨γ, hγ, h1, h2⟩ := ih _ hcard (D \ T) rfl (isEven_sdiff hD hT.isEven hTD)
    (by rw [par_sdiff hTD, hpar, hT0, sub_zero])
  exact ⟨γ, hγ.trans Finset.sdiff_subset, h1, h2⟩

/-! ## Where a contour around the origin lies -/

/-- A set with `par γ 0 = 1` has a bond crossing the positive horizontal half-axis. -/
theorem exists_right_crossing {γ : Finset Bond} (h : par γ 0 = 1) :
    ∃ j : ℤ, 0 ≤ j ∧ ((j, 0), false) ∈ γ := by
  unfold par at h
  obtain ⟨b, hb, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by rw [h]; decide)
  obtain ⟨⟨a, c⟩, k⟩ := b
  by_cases hcond : k = false ∧ c = (0 : Plane).2 ∧ (0 : Plane).1 ≤ a
  · obtain ⟨rfl, rfl, ha⟩ := hcond
    exact ⟨a, ha, hb⟩
  · exact absurd (if_neg hcond) hne

/-- An even `γ` with `par γ 0 = 1` also crosses the negative horizontal half-axis (the total
crossing number of a row is even). -/
theorem exists_left_crossing {γ : Finset Bond} (hγ : IsEven γ) (h : par γ 0 = 1) :
    ∃ i : ℤ, i < 0 ∧ ((i, 0), false) ∈ γ := by
  set x₀ : Plane := (-bound γ - 1, 0) with hx₀
  have h0 : par γ x₀ = 0 := par_eq_zero_of_left hγ (by simp [x₀])
  have hsum : ∑ b ∈ γ, ((if b.2 = false ∧ b.1.2 = x₀.2 ∧ x₀.1 ≤ b.1.1 then 1 else 0) -
      (if b.2 = false ∧ b.1.2 = (0 : Plane).2 ∧ (0 : Plane).1 ≤ b.1.1 then 1 else 0) : ZMod 2) ≠
      0 := by
    rw [Finset.sum_sub_distrib]
    change par γ x₀ - par γ 0 ≠ 0
    rw [h0, h]
    decide
  obtain ⟨⟨⟨a, c⟩, k⟩, hb, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  simp only [x₀, Prod.fst_zero, Prod.snd_zero] at hne
  by_cases ha : 0 ≤ a
  · have hx : -bound γ - 1 ≤ a := by
      have : 0 ≤ bound γ := Finset.sum_nonneg fun b _ => by positivity
      omega
    simp [ha, hx] at hne
  · by_cases hcond : k = false ∧ c = 0
    · obtain ⟨rfl, rfl⟩ := hcond
      exact ⟨a, by omega, hb⟩
    · have h1 : ¬ (k = false ∧ c = 0 ∧ -bound γ - 1 ≤ a) := fun h' => hcond ⟨h'.1, h'.2.1⟩
      have h2 : ¬ (k = false ∧ c = 0 ∧ 0 ≤ a) := fun h' => ha h'.2.2
      simp only [h1, h2, if_false, sub_self, ne_eq, not_true_eq_false] at hne

theorem vec_fst (d : Dir) : -1 ≤ d.vec.1 ∧ d.vec.1 ≤ 1 := by
  cases d <;> simp [Dir.vec, e1, e2]

/-- Steps move the first coordinate by at most one. -/
theorem walkEnd_fst_le (p : Plane) (ds : List Dir) :
    p.1 - ds.length ≤ (walkEnd p ds).1 ∧ (walkEnd p ds).1 ≤ p.1 + ds.length := by
  induction ds generalizing p with
  | nil => simp
  | cons d ds ih =>
    have := ih (p + d.vec)
    have hv := vec_fst d
    simp only [walkEnd_cons, List.length_cons, Nat.cast_add, Nat.cast_one, Prod.fst_add] at this ⊢
    omega

theorem vec_sum (d : Dir) : d.vec.1 + d.vec.2 = 1 ∨ d.vec.1 + d.vec.2 = -1 := by
  cases d <;> simp [Dir.vec, e1, e2]

/-- Steps change the parity of `x₁ + x₂`. -/
theorem walkEnd_parity (p : Plane) (ds : List Dir) :
    ((walkEnd p ds).1 + (walkEnd p ds).2 + ds.length) % 2 = (p.1 + p.2) % 2 := by
  induction ds generalizing p with
  | nil => simp
  | cons d ds ih =>
    have := ih (p + d.vec)
    have hv := vec_sum d
    simp only [walkEnd_cons, List.length_cons, Nat.cast_add, Nat.cast_one, Prod.fst_add,
      Prod.snd_add] at this ⊢
    omega

/-- **The code of a contour around the origin**: a contour `γ` with `par γ 0 = 1` has an even
number `k` of bonds and is the bond set of a closed walk of `k` steps from a plaquette `(j, 0)`
with `2 (j + 1) ≤ k`. -/
theorem circuit_code {γ : Finset Bond} (hγ : IsCircuit γ) (h : par γ 0 = 1) :
    Even γ.card ∧ ∃ j : ℕ, 2 * (j + 1) ≤ γ.card ∧ ∃ ds : List Dir, ds.length = γ.card ∧
      (walk ((j : ℤ), 0) ds).toFinset = γ := by
  classical
  have hev := hγ.isEven
  obtain ⟨p, ds, hc, hnd, rfl⟩ := hγ
  have hcard : (walk p ds).toFinset.card = ds.length := by
    rw [List.toFinset_card_of_nodup hnd, length_walk]
  rw [hcard]
  refine ⟨?_, ?_⟩
  · have := walkEnd_parity p ds
    rw [hc] at this
    exact Nat.even_iff.2 (by omega)
  -- rotate the closed walk to start at the plaquette `(j, 0)` above the right crossing
  obtain ⟨j, hj, hjγ⟩ := exists_right_crossing h
  obtain ⟨A, B, hAB, hA⟩ := exists_split_of_inc (List.mem_toFinset.1 hjγ)
    (inc_self ((j, 0), false))
  set r : Plane := (j, 0) with hr
  replace hA : walkEnd p A = r := hA
  have hrB : walkEnd r B = p := by rw [← hA, ← walkEnd_append, ← hAB, hc]
  have hperm : (walk r (B ++ A)).Perm (walk p ds) := by
    rw [walk_append, hrB, hAB, walk_append, hA]
    exact List.perm_append_comm
  have hfin : (walk r (B ++ A)).toFinset = (walk p ds).toFinset := by
    rw [hAB, walk_append, walk_append, hrB, hA, List.toFinset_append, List.toFinset_append,
      Finset.union_comm]
  have hc' : walkEnd r (B ++ A) = r := by rw [walkEnd_append, hrB, hA]
  -- the left crossing is visited too: `2 (j - i) ≤ k`
  obtain ⟨i, hi, hiγ⟩ := exists_left_crossing hev h
  rw [← hfin] at hiγ
  obtain ⟨A', B', hAB', hA'⟩ := exists_split_of_inc (List.mem_toFinset.1 hiγ)
    (inc_self ((i, 0), false))
  replace hA' : walkEnd r A' = ((i, 0) : Plane) := hA'
  have hB' : walkEnd ((i, 0) : Plane) B' = r := by
    rw [← hA', ← walkEnd_append, ← hAB', hc']
  have d1 := walkEnd_fst_le r A'
  have d2 := walkEnd_fst_le ((i, 0) : Plane) B'
  rw [hA'] at d1
  rw [hB'] at d2
  have hlen : (B ++ A).length = ds.length := by
    rw [hAB]; simp [Nat.add_comm]
  have hlen' : (A' ++ B').length = ds.length := by rw [← hAB', hlen]
  simp only [hr, List.length_append] at d1 d2 hlen'
  refine ⟨j.toNat, by omega, B ++ A, hlen, ?_⟩
  rw [Int.toNat_of_nonneg hj, ← hr, hfin]

/-! ## The count of contours and the union bound -/

open Classical in
/-- The contours around the origin inside the box `B(n)`: contours `γ ⊆ ℰ^b_{B(n)}` with
`par γ 0 = 1`. -/
def contours (n : ℕ) : Finset (Finset Bond) :=
  (bonds (box n)).powerset.filter fun γ => IsCircuit γ ∧ par γ 0 = 1

theorem mem_contours {n : ℕ} {γ : Finset Bond} :
    γ ∈ contours n ↔ γ ⊆ bonds (box n) ∧ IsCircuit γ ∧ par γ 0 = 1 := by
  simp only [contours, Finset.mem_filter, Finset.mem_powerset]

theorem card_dir : Fintype.card Dir = 4 := rfl

/-- **The count**: at most `m · 4^{2m}` contours around the origin with `2m` bonds in a box (a
start plaquette `(j, 0)` with `j < m` and a walk of `2m` steps). -/
theorem card_contours_le (n m : ℕ) :
    ((contours n).filter fun γ => γ.card = 2 * m).card ≤ m * 4 ^ (2 * m) := by
  classical
  let f : ℕ × List.Vector Dir (2 * m) → Finset Bond :=
    fun c => (walk ((c.1 : ℤ), 0) c.2.toList).toFinset
  calc ((contours n).filter fun γ => γ.card = 2 * m).card
      ≤ ((Finset.range m ×ˢ (Finset.univ : Finset (List.Vector Dir (2 * m)))).image f).card := by
        apply Finset.card_le_card
        intro γ hγ
        rw [Finset.mem_filter, mem_contours] at hγ
        obtain ⟨⟨-, hc, hp⟩, hcard⟩ := hγ
        obtain ⟨-, j, hj, ds, hds, hγ'⟩ := circuit_code hc hp
        rw [Finset.mem_image]
        refine ⟨(j, ⟨ds, hds.trans hcard⟩), ?_, hγ'⟩
        simp only [Finset.mem_product, Finset.mem_range, Finset.mem_univ, and_true]
        exact ⟨by omega, Finset.mem_univ _⟩
    _ ≤ (Finset.range m ×ˢ (Finset.univ : Finset (List.Vector Dir (2 * m)))).card :=
        Finset.card_image_le
    _ = m * 4 ^ (2 * m) := by
        rw [Finset.card_product, Finset.card_range, Finset.card_univ, card_vector, card_dir]

/-- `∑_{m ≥ 0} m (16/81)^m = (16/81) / (1 - 16/81)² = 1296/4225`. -/
theorem hasSum_series : HasSum (fun m : ℕ => (m : ℝ) * (16 / 81) ^ m) (1296 / 4225) := by
  have h := hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) (r := 16 / 81)
    (by rw [Real.norm_eq_abs, abs_of_pos (by norm_num)]; norm_num)
  convert h using 1
  norm_num

/-- **The sum over contours**: `∑_γ 9^{-|γ|} ≤ 1296/4225`, uniformly in the box. -/
theorem sum_contours_le (n : ℕ) :
    ∑ γ ∈ contours n, ((1 : ℝ) / 9) ^ γ.card ≤ 1296 / 4225 := by
  classical
  set C := contours n
  set M := (bonds (box n)).card + 1
  have hmaps : ∀ γ ∈ C, γ.card / 2 ∈ Finset.range M := by
    intro γ hγ
    rw [mem_contours] at hγ
    have := Finset.card_le_card hγ.1
    rw [Finset.mem_range]
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  calc ∑ m ∈ Finset.range M, ∑ γ ∈ C with γ.card / 2 = m, ((1 : ℝ) / 9) ^ γ.card
      ≤ ∑ m ∈ Finset.range M, (m : ℝ) * (16 / 81) ^ m := by
        refine Finset.sum_le_sum fun m _ => ?_
        have hfib : ∀ γ ∈ C.filter (fun γ => γ.card / 2 = m), γ.card = 2 * m := by
          intro γ hγ
          rw [Finset.mem_filter, mem_contours] at hγ
          obtain ⟨⟨-, hc, hp⟩, hm⟩ := hγ
          obtain ⟨⟨r, hr⟩, -⟩ := circuit_code hc hp
          omega
        rw [Finset.sum_congr rfl fun γ hγ =>
          show ((1 : ℝ) / 9) ^ γ.card = ((1 : ℝ) / 9) ^ (2 * m) by rw [hfib γ hγ],
          Finset.sum_const, nsmul_eq_mul]
        have hcardle : (C.filter fun γ => γ.card / 2 = m).card ≤ m * 4 ^ (2 * m) := by
          calc _ ≤ (C.filter fun γ => γ.card = 2 * m).card :=
                Finset.card_le_card fun γ hγ => by
                  rw [Finset.mem_filter] at hγ ⊢
                  exact ⟨hγ.1, hfib γ (Finset.mem_filter.2 hγ)⟩
            _ ≤ _ := card_contours_le n m
        calc ((C.filter fun γ => γ.card / 2 = m).card : ℝ) * ((1 : ℝ) / 9) ^ (2 * m)
            ≤ ((m * 4 ^ (2 * m) : ℕ) : ℝ) * ((1 : ℝ) / 9) ^ (2 * m) := by
              gcongr
          _ = (m : ℝ) * (16 / 81) ^ m := by
              push_cast
              rw [pow_mul, pow_mul, mul_assoc, ← mul_pow]
              norm_num
    _ ≤ 1296 / 4225 := sum_le_hasSum _ (fun m _ => by positivity) hasSum_series

/-- `e^J ≥ 3` gives `e^{-2Jk} ≤ 9^{-k}`. -/
theorem exp_le_ninth {J : ℝ} (hJ : 3 ≤ Real.exp J) (k : ℕ) :
    Real.exp (-(2 * J) * k) ≤ ((1 : ℝ) / 9) ^ k := by
  have h1 : Real.exp (-(2 * J)) ≤ 1 / 9 := by
    have h : Real.exp (-(2 * J)) = 1 / (Real.exp J * Real.exp J) := by
      rw [← Real.exp_add, one_div, ← Real.exp_neg]
      congr 1
      ring
    rw [h]
    apply one_div_le_one_div_of_le (by norm_num)
    nlinarith
  rw [show -(2 * J) * (k : ℝ) = k * (-(2 * J)) by ring, Real.exp_nat_mul]
  exact pow_le_pow_left₀ (Real.exp_pos _).le h1 k

theorem weight_pos (J : ℝ) (Λ : Finset Plane) (σ : Config Spin) : 0 < weight J Λ σ :=
  Real.exp_pos _

/-- The finite-volume expectation is monotone. -/
theorem expect_mono {J : ℝ} {Λ : Finset Plane} {η : Config Spin} {f g : Config Spin → ℝ}
    (h : ∀ ζ : Λ → Spin, f (fill η Λ ζ) ≤ g (fill η Λ ζ)) :
    expect J Λ η f ≤ expect J Λ η g := by
  unfold expect
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun ζ _ =>
    mul_le_mul_of_nonneg_left (h ζ) (weight_pos _ _ _).le)
    (Finset.sum_nonneg fun ζ _ => (weight_pos _ _ _).le)

/-- The finite-volume expectation is additive. -/
theorem expect_sum {ι : Type} (s : Finset ι) (J : ℝ) (Λ : Finset Plane) (η : Config Spin)
    (f : ι → Config Spin → ℝ) :
    expect J Λ η (fun σ => ∑ i ∈ s, f i σ) = ∑ i ∈ s, expect J Λ η (f i) := by
  unfold expect
  rw [← Finset.sum_div]
  congr 1
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

/-- **Peierls' bound in a box** (`set:peierls`, finite volume): if `e^J ≥ 3`, then under the plus
measure in `B(n)`, `P(σ₀ = -1) ≤ 1296/4225`. The paper's sharper count (`k 3^k` contours of length
`k`, total `1/12`) is not needed: only `≤ 1/3` is used (QB ruling on P-2, session 4). -/
theorem plus_prob_minus_le {J : ℝ} (hJ : 3 ≤ Real.exp J) (n : ℕ) :
    expect J (box n) plusConfig ({σ : Config Spin | σ 0 = .minus}.indicator 1) ≤
      1296 / 4225 := by
  classical
  set C := contours n
  have hsplit : expect J (box n) plusConfig ({σ : Config Spin | σ 0 = .minus}.indicator 1) ≤
      expect J (box n) plusConfig (fun σ => ∑ γ ∈ C,
        (fun γ σ => {σ : Config Spin | γ ⊆ disagree (box n) σ}.indicator 1 σ) γ σ) := by
    apply expect_mono
    intro ζ
    set σ := fill plusConfig (box n) ζ with hσdef
    have hnn : ∀ γ ∈ C, (0 : ℝ) ≤ {σ : Config Spin | γ ⊆ disagree (box n) σ}.indicator 1 σ :=
      fun γ _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _
    by_cases h0 : σ 0 = .minus
    · have hσ : ∀ x, x ∉ box n → σ x = .plus := fun x hx => by
        simp [hσdef, fill, hx, plusConfig]
      obtain ⟨γ, hγD, hc, hp⟩ := exists_circuit_par _ _ rfl (disagree_isEven hσ)
        (by rw [par_disagree hσ, h0]; rfl)
      have hγC : γ ∈ C := mem_contours.2 ⟨hγD.trans (Finset.filter_subset _ _), hc, hp⟩
      calc {σ : Config Spin | σ 0 = .minus}.indicator 1 σ = (1 : ℝ) :=
            Set.indicator_of_mem (show σ ∈ {σ : Config Spin | σ 0 = .minus} from h0) _
        _ = {σ : Config Spin | γ ⊆ disagree (box n) σ}.indicator 1 σ :=
            (Set.indicator_of_mem (show σ ∈ {σ : Config Spin | γ ⊆ disagree (box n) σ} from
              hγD) (1 : Config Spin → ℝ)).symm
        _ ≤ ∑ γ ∈ C, {σ : Config Spin | γ ⊆ disagree (box n) σ}.indicator 1 σ :=
            Finset.single_le_sum hnn hγC
    · rw [Set.indicator_of_notMem (show σ ∉ {σ : Config Spin | σ 0 = .minus} from h0)]
      exact Finset.sum_nonneg hnn
  rw [expect_sum] at hsplit
  refine hsplit.trans ?_
  calc ∑ γ ∈ C, expect J (box n) plusConfig
        (fun σ => {σ : Config Spin | γ ⊆ disagree (box n) σ}.indicator 1 σ)
      ≤ ∑ γ ∈ C, ((1 : ℝ) / 9) ^ γ.card := by
        refine Finset.sum_le_sum fun γ hγ => ?_
        rw [mem_contours] at hγ
        exact (plus_prob_contour_le J n hγ.2.1.isEven hγ.1).trans (exp_le_ninth hJ γ.card)
    _ ≤ 1296 / 4225 := sum_contours_le n

end Peierls

end UPD

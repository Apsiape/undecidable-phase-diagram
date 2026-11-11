/-
# The planar step of Peierls' argument, without the Jordan curve theorem (`set:peierls`)

The paper's proof of `set:peierls` uses that, in a box with plus boundary condition, `σ₀ = -1`
forces a closed contour of the dual lattice around the origin, and that flipping the spins inside
a contour removes exactly that contour. This file replaces "inside" by a parity: a set `γ` of bonds
(= dual edges) is *even* if every unit square (= dual vertex) has an even number of its four bonds
in `γ`, and a site `x` is inside `γ` if the ray from `x` to the right crosses `γ` an odd number of
times (`par γ x = 1` in `ZMod 2`). Everything is then algebra in `ZMod 2`:
* `par_eq`: moving one step right changes the parity by the crossed bond;
* `par_add_e2` (even `γ`): moving one step up changes the parity by the crossed bond — the only
  planar input, proved by sliding the vertical step to the far right, one plaquette at a time;
* `par_add_bondDir`: for every bond `b = {x, x + e_k}`, `par x + par (x + e_k) = [b ∈ γ]`;
* `disagree_isEven`, `par_disagree`: the set `D(σ)` of disagreeing bonds of a configuration that is
  plus off a finite set is even, and `par_{D(σ)}(x) = [σ_x = -1]`;
* `disagree_flip`: flipping the spins inside an even `γ` changes `D(σ)` exactly on `γ`.
The probabilistic half (the weight identity, the injection, the count of contours, the limit via
`H2`) is planned in `BLUEPRINT.md`, Part A.1.
-/
import UndecidablePhaseDiagram.Gibbs.Site
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false

noncomputable section

namespace UPD

namespace Peierls

open Ising

/-- A bond `(x, k)`: the edge `{x, x + e_k}` of `ℤ²` (`k = false`: horizontal, `true`:
vertical). Bonds are in bijection with the edges of the dual lattice. -/
abbrev Bond := Plane × Bool

/-- `[b ∈ γ]` in `ZMod 2`. -/
def ind (γ : Finset Bond) (b : Bond) : ZMod 2 := if b ∈ γ then 1 else 0

/-- The number, mod 2, of bonds of `γ` on the boundary of the unit square with lower-left corner
`p` (= the degree of the dual vertex `p + (½, ½)`). -/
def plaq (γ : Finset Bond) (p : Plane) : ZMod 2 :=
  ind γ (p, false) + ind γ (p + e2, false) + ind γ (p, true) + ind γ (p + e1, true)

/-- `γ` is even: every dual vertex has even degree. -/
def IsEven (γ : Finset Bond) : Prop := ∀ p, plaq γ p = 0

/-- The parity of the number of bonds of `γ` crossed by the ray from `x` to the right: the
horizontal bonds `(z, false)` with `z₂ = x₂` and `z₁ ≥ x₁`. -/
def par (γ : Finset Bond) (x : Plane) : ZMod 2 :=
  ∑ b ∈ γ, if b.2 = false ∧ b.1.2 = x.2 ∧ x.1 ≤ b.1.1 then 1 else 0

theorem two_eq_zero : (2 : ZMod 2) = 0 := rfl

theorem neg_eq_self (a : ZMod 2) : -a = a := by
  fin_cases a <;> rfl

/-- **One step right.** -/
theorem par_eq (γ : Finset Bond) (x : Plane) : par γ x = ind γ (x, false) + par γ (x + e1) := by
  unfold par ind
  rw [← Finset.sum_ite_eq' γ (x, false) (fun _ => (1 : ZMod 2)), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  obtain ⟨⟨a, c⟩, k⟩ := b
  obtain ⟨x1, x2⟩ := x
  simp only [e1, Prod.mk_add_mk, add_zero, Prod.mk.injEq]
  by_cases hk : k = false <;> by_cases hc : c = x2 <;> by_cases ha : a = x1 <;>
    simp [hk, hc, ha] <;> (try omega) <;> (by_cases h : x1 ≤ a <;> simp [h] <;> omega)

/-- The vertical-step defect `Q(x) = par x + par (x + e₂) + [(x, true) ∈ γ]` is invariant under
a step right, up to the plaquette at `x`. -/
theorem defect_eq (γ : Finset Bond) (x : Plane) :
    par γ x + par γ (x + e2) + ind γ (x, true) =
      par γ (x + e1) + par γ (x + e1 + e2) + ind γ (x + e1, true) + plaq γ x := by
  rw [par_eq γ x, par_eq γ (x + e2), show x + e2 + e1 = x + e1 + e2 by abel]
  unfold plaq
  linear_combination (-(ind γ (x + e1, true))) * two_eq_zero

/-- A crude bound on the coordinates of the bonds of `γ`. -/
def bound (γ : Finset Bond) : ℤ := ∑ b ∈ γ, (|b.1.1| + |b.1.2|)

theorem abs_le_bound {γ : Finset Bond} {b : Bond} (hb : b ∈ γ) :
    |b.1.1| ≤ bound γ ∧ |b.1.2| ≤ bound γ := by
  have h : |b.1.1| + |b.1.2| ≤ bound γ :=
    Finset.single_le_sum (f := fun b : Bond => |b.1.1| + |b.1.2|) (fun b _ => by positivity) hb
  exact ⟨by linarith [abs_nonneg b.1.2], by linarith [abs_nonneg b.1.1]⟩

theorem ind_eq_zero_of_far {γ : Finset Bond} {x : Plane} (k : Bool)
    (h : bound γ < |x.1| ∨ bound γ < |x.2|) : ind γ (x, k) = 0 := by
  unfold ind
  rw [if_neg]
  intro hx
  have := abs_le_bound hx
  rcases h with h | h <;> linarith [this.1, this.2]

theorem par_eq_zero_of_right {γ : Finset Bond} {x : Plane} (h : bound γ < x.1) :
    par γ x = 0 := by
  unfold par
  refine Finset.sum_eq_zero fun b hb => if_neg ?_
  rintro ⟨-, -, hle⟩
  have := (abs_le_bound hb).1
  linarith [le_abs_self b.1.1]

theorem par_eq_zero_of_row {γ : Finset Bond} {x : Plane} (h : bound γ < |x.2|) :
    par γ x = 0 := by
  unfold par
  refine Finset.sum_eq_zero fun b hb => if_neg ?_
  rintro ⟨-, heq, -⟩
  have := (abs_le_bound hb).2
  rw [heq] at this
  linarith

theorem shift_succ (x : Plane) (n : ℕ) :
    x + (((n + 1 : ℕ) : ℤ), (0 : ℤ)) = x + ((n : ℤ), 0) + e1 := by
  ext <;> simp [e1] <;> ring

theorem shift_zero (x : Plane) : x + (((0 : ℕ) : ℤ), (0 : ℤ)) = x := by
  simp [Prod.mk_zero_zero]

/-- **The vertical step** (the planar input): for even `γ`, `par (x + e₂) = par x + [(x, true) ∈ γ]`.
The defect `Q` is invariant under steps right (`defect_eq`) and vanishes far right. -/
theorem par_add_e2 {γ : Finset Bond} (hγ : IsEven γ) (x : Plane) :
    par γ (x + e2) = par γ x + ind γ (x, true) := by
  -- `Q(x) = Q(x + n e₁)` for all `n`
  have hinv : ∀ n : ℕ, par γ x + par γ (x + e2) + ind γ (x, true) =
      par γ (x + ((n : ℤ), 0)) + par γ (x + ((n : ℤ), 0) + e2) +
        ind γ (x + ((n : ℤ), 0), true) := by
    intro n
    induction n with
    | zero => rw [shift_zero]
    | succ n ih =>
      rw [ih, defect_eq γ (x + ((n : ℤ), 0)), hγ, add_zero, shift_succ]
  -- far right everything vanishes
  obtain ⟨n, hn⟩ : ∃ n : ℕ, bound γ < x.1 + n := ⟨(bound γ - x.1 + 1).toNat, by omega⟩
  have h0 := hinv n
  rw [par_eq_zero_of_right (x := x + ((n : ℤ), 0)) (by simpa using hn),
    par_eq_zero_of_right (x := x + ((n : ℤ), 0) + e2) (by simpa [e2] using hn),
    ind_eq_zero_of_far (x := x + ((n : ℤ), 0)) true (Or.inl (by
      simp only [Prod.fst_add]; exact lt_of_lt_of_le hn (le_abs_self _))), add_zero,
    add_zero] at h0
  -- `a + b + c = 0` gives `b = a + c` in `ZMod 2`
  linear_combination h0 - (par γ x + ind γ (x, true)) * two_eq_zero

/-- **Both steps**: for every bond `b = {x, x + e_k}` of an even `γ`,
`par x + par (x + e_k) = [b ∈ γ]`. -/
theorem par_add_bondDir {γ : Finset Bond} (hγ : IsEven γ) (x : Plane) (k : Bool) :
    par γ x + par γ (x + bondDir k) = ind γ (x, k) := by
  cases k
  · simp only [bondDir]
    rw [par_eq γ x]
    linear_combination (par γ (x + e1)) * two_eq_zero
  · simp only [bondDir]
    rw [par_add_e2 hγ x]
    linear_combination (par γ x) * two_eq_zero

/-- Far to the left, the parity vanishes too (the total crossing number of a row is even). -/
theorem par_eq_zero_of_left {γ : Finset Bond} (hγ : IsEven γ) {x : Plane} (h : x.1 < -bound γ) :
    par γ x = 0 := by
  have hup : ∀ m : ℕ, par γ x = par γ (x + (0, (m : ℤ))) := by
    intro m
    induction m with
    | zero => simp [Prod.mk_zero_zero]
    | succ m ih =>
      rw [ih, show x + ((0 : ℤ), ((m + 1 : ℕ) : ℤ)) = x + (0, (m : ℤ)) + e2 by
        simp [e2, add_assoc], par_add_e2 hγ, ind_eq_zero_of_far true (Or.inl (by
          simp only [Prod.fst_add, add_zero]
          exact lt_of_lt_of_le (by linarith) (neg_le_abs x.1))), add_zero]
  obtain ⟨m, hm⟩ : ∃ m : ℕ, bound γ < x.2 + m := ⟨(bound γ - x.2 + 1).toNat, by omega⟩
  rw [hup m]
  exact par_eq_zero_of_row (by simp only [Prod.snd_add]; exact lt_of_lt_of_le hm (le_abs_self _))

/-! ## Disagreement sets and spin flips -/

/-- A spin as an element of `ZMod 2` (`+1 ↦ 0`, `-1 ↦ 1`). -/
def sgn : Spin → ZMod 2
  | .plus => 0
  | .minus => 1

/-- The global spin flip of one spin. -/
def flipSpin : Spin → Spin
  | .plus => .minus
  | .minus => .plus

theorem sgn_flipSpin (s : Spin) : sgn (flipSpin s) = sgn s + 1 := by
  cases s <;> rfl

theorem sgn_add_sgn (s t : Spin) : sgn s + sgn t = if s = t then 0 else 1 := by
  cases s <;> cases t <;> rfl

/-- The disagreeing bonds of `σ` meeting `Λ`: the set `D(σ)` of the paper's proof (the dual edges
between disagreeing spins), when `σ` is plus off `Λ`. -/
def disagree (Λ : Finset Plane) (σ : Config Spin) : Finset Bond :=
  (bonds Λ).filter fun b => σ b.1 ≠ σ (b.1 + bondDir b.2)

/-- For `σ` plus off `Λ`: `[b ∈ D(σ)] = sgn σ_x + sgn σ_{x + e_k}` for every bond. -/
theorem ind_disagree {Λ : Finset Plane} {σ : Config Spin} (hσ : ∀ x, x ∉ Λ → σ x = .plus)
    (b : Bond) : ind (disagree Λ σ) b = sgn (σ b.1) + sgn (σ (b.1 + bondDir b.2)) := by
  rw [sgn_add_sgn]
  unfold ind disagree
  by_cases hb : b ∈ bonds Λ
  · by_cases he : σ b.1 = σ (b.1 + bondDir b.2) <;> simp [hb, he]
  · obtain ⟨x, k⟩ := b
    rw [mem_bonds] at hb
    push_neg at hb
    have he : σ x = σ (x + bondDir k) := by rw [hσ x hb.1, hσ _ hb.2]
    simp [he]

/-- **`D(σ)` is even**: around a unit square the number of sign changes is even. -/
theorem disagree_isEven {Λ : Finset Plane} {σ : Config Spin} (hσ : ∀ x, x ∉ Λ → σ x = .plus) :
    IsEven (disagree Λ σ) := by
  intro p
  unfold plaq
  simp only [ind_disagree hσ, bondDir]
  rw [show p + e2 + e1 = p + e1 + e2 by abel]
  linear_combination (sgn (σ p) + sgn (σ (p + e1)) + sgn (σ (p + e2)) +
    sgn (σ (p + e1 + e2))) * two_eq_zero

/-- **`par_{D(σ)}(x) = [σ_x = -1]`** for `σ` plus off a finite set: the number of sign changes on
the ray from `x` is odd exactly when `σ_x = -1`. -/
theorem par_disagree {Λ : Finset Plane} {σ : Config Spin} (hσ : ∀ x, x ∉ Λ → σ x = .plus)
    (x : Plane) : par (disagree Λ σ) x = sgn (σ x) := by
  set γ := disagree Λ σ
  -- `par x + sgn σ_x` is invariant under steps right
  have hstep : ∀ y : Plane, par γ y + sgn (σ y) = par γ (y + e1) + sgn (σ (y + e1)) := by
    intro y
    rw [par_eq γ y, ind_disagree hσ]
    simp only [bondDir]
    linear_combination (sgn (σ y)) * two_eq_zero
  have hinv : ∀ n : ℕ, par γ x + sgn (σ x) =
      par γ (x + ((n : ℤ), 0)) + sgn (σ (x + ((n : ℤ), 0))) := by
    intro n
    induction n with
    | zero => rw [shift_zero]
    | succ n ih => rw [ih, hstep, shift_succ]
  -- far right: no bond of `γ`, and `σ` is plus (off the finite set `Λ`)
  obtain ⟨n, hn, hn'⟩ : ∃ n : ℕ, bound γ < x.1 + n ∧ x + ((n : ℤ), 0) ∉ Λ := by
    have hS : 0 ≤ ∑ y ∈ Λ, |y.1| := Finset.sum_nonneg fun y _ => abs_nonneg _
    refine ⟨(bound γ + ∑ y ∈ Λ, |y.1| - x.1 + 1).toNat, by omega, fun hmem => ?_⟩
    have h1 : |(x + (((bound γ + ∑ y ∈ Λ, |y.1| - x.1 + 1).toNat : ℤ), (0 : ℤ))).1| ≤
        ∑ y ∈ Λ, |y.1| := Finset.single_le_sum (f := fun y : Plane => |y.1|)
          (fun y _ => abs_nonneg _) hmem
    have h2 := le_abs_self (x + (((bound γ + ∑ y ∈ Λ, |y.1| - x.1 + 1).toNat : ℤ), (0 : ℤ))).1
    simp only [Prod.fst_add] at h1 h2
    have hb : 0 ≤ bound γ := Finset.sum_nonneg fun b _ => by positivity
    omega
  have h0 := hinv n
  rw [par_eq_zero_of_right (x := x + ((n : ℤ), 0)) (by simpa using hn), hσ _ hn'] at h0
  rw [show sgn Spin.plus = 0 from rfl, add_zero] at h0
  linear_combination h0 - (sgn (σ x)) * two_eq_zero

/-- Flip the spins inside `γ` (where `par γ = 1`). -/
def flipInside (γ : Finset Bond) (σ : Config Spin) : Config Spin :=
  fun x => if par γ x = 1 then flipSpin (σ x) else σ x

theorem sgn_flipInside (γ : Finset Bond) (σ : Config Spin) (x : Plane) :
    sgn (flipInside γ σ x) = sgn (σ x) + par γ x := by
  unfold flipInside
  by_cases h : par γ x = 1
  · rw [if_pos h, sgn_flipSpin, h]
  · have h0 : par γ x = 0 := by
      have key : ∀ a : ZMod 2, a ≠ 1 → a = 0 := by decide
      exact key _ h
    rw [if_neg h, h0, add_zero]

/-- **Flipping inside an even `γ` changes the disagreement exactly on `γ`**: for every bond,
`[b ∈ D(F_γ σ)] = [b ∈ D(σ)] + [b ∈ γ]`, provided `σ` and `F_γ σ` are plus off `Λ`. -/
theorem disagree_flip {Λ : Finset Plane} {γ : Finset Bond} (hγ : IsEven γ) {σ : Config Spin}
    (hσ : ∀ x, x ∉ Λ → σ x = .plus) (hFσ : ∀ x, x ∉ Λ → flipInside γ σ x = .plus) (b : Bond) :
    ind (disagree Λ (flipInside γ σ)) b = ind (disagree Λ σ) b + ind γ b := by
  obtain ⟨x, k⟩ := b
  rw [ind_disagree hFσ, ind_disagree hσ, sgn_flipInside, sgn_flipInside,
    ← par_add_bondDir hγ x k]
  ring

end Peierls

end UPD

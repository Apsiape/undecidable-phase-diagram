/-
# Peierls' flip bound in a box (`set:peierls`)

The paper: "a given contour of length `k` has probability at most `e^{-2Jk}`, because flipping the
spins inside it is injective and raises the weight by `e^{2Jk}`". Here, for the box
`B(n) = [-n, n]²` with plus boundary condition and any even set of bonds `γ` inside the box
(`Peierls/Parity.lean`):
* `weight_eq`: `exp(J ∑_{ℰ^b_Λ} σ_x σ_y) = exp(J |ℰ^b_Λ|) exp(-2J |D(σ)|)`;
* `par_eq_zero_off_box`: the inside of `γ` lies in the box, so flipping it keeps the boundary
  condition;
* `disagree_flipInside`: if `γ ⊆ D(σ)`, flipping inside `γ` gives `D(σ) \ γ`;
* `plus_prob_contour_le`: under the finite-volume plus measure, `P(γ ⊆ D(σ)) ≤ e^{-2J|γ|}`.
-/
import UndecidablePhaseDiagram.Peierls.Parity

set_option autoImplicit false

noncomputable section

namespace UPD

namespace Peierls

open Ising

/-- The box `B(n) = [-n, n]²`. -/
def box (n : ℕ) : Finset Plane := Finset.Icc (-(n : ℤ)) n ×ˢ Finset.Icc (-(n : ℤ)) n

theorem mem_box {n : ℕ} {x : Plane} : x ∈ box n ↔ |x.1| ≤ n ∧ |x.2| ≤ n := by
  simp [box, abs_le]

theorem val_mul_val (s t : Spin) : val s * val t = 1 - 2 * (if s ≠ t then 1 else 0) := by
  cases s <;> cases t <;> simp [val] <;> norm_num

/-- **The weight in terms of the disagreements** (any `σ`). -/
theorem weight_eq (J : ℝ) (Λ : Finset Plane) (σ : Config Spin) :
    weight J Λ σ =
      Real.exp (J * (bonds Λ).card) * Real.exp (-(2 * J) * (disagree Λ σ).card) := by
  unfold weight
  rw [← Real.exp_add]
  congr 1
  simp only [val_mul_val, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one,
    ← Finset.mul_sum, Finset.sum_boole, disagree]
  ring

theorem ind_eq_one_iff {γ : Finset Bond} {b : Bond} : ind γ b = 1 ↔ b ∈ γ := by
  unfold ind; split_ifs with h <;> simp [h]

/-- **Flipping inside `γ ⊆ D(σ)` removes exactly `γ`.** -/
theorem disagree_flipInside {Λ : Finset Plane} {γ : Finset Bond} (hγ : IsEven γ)
    {σ : Config Spin} (hσ : ∀ x, x ∉ Λ → σ x = .plus)
    (hFσ : ∀ x, x ∉ Λ → flipInside γ σ x = .plus) (hsub : γ ⊆ disagree Λ σ) :
    disagree Λ (flipInside γ σ) = disagree Λ σ \ γ := by
  ext b
  have h := disagree_flip hγ hσ hFσ b
  rw [Finset.mem_sdiff, ← ind_eq_one_iff, h]
  by_cases hb : b ∈ γ
  · have hD : ind (disagree Λ σ) b = 1 := ind_eq_one_iff.2 (hsub hb)
    rw [hD, ind_eq_one_iff.2 hb]
    simp only [hb, not_true_eq_false, and_false, iff_false]
    decide
  · have h0 : ind γ b = 0 := by unfold ind; simp [hb]
    rw [h0, add_zero, ind_eq_one_iff]
    simp [hb]

/-- The inside of an even `γ` made of bonds meeting the box lies in the box. -/
theorem par_eq_zero_off_box {n : ℕ} {γ : Finset Bond} (hγ : IsEven γ) (hsub : γ ⊆ bonds (box n))
    {x : Plane} (hx : x ∉ box n) : par γ x = 0 := by
  -- the bonds of `γ` have their first point in the box or just below/left of it
  have hrow : ∀ b ∈ γ, |b.1.2| ≤ n + 1 ∧ -((n : ℤ) + 1) ≤ b.1.1 ∧ b.1.1 ≤ n := by
    rintro ⟨y, k⟩ hb
    have hm := (mem_bonds _ y k).1 (hsub hb)
    simp only
    rcases hm with h | h
    · rw [mem_box] at h
      obtain ⟨h1, h2⟩ := h
      rw [abs_le] at h1 h2 ⊢
      omega
    · rw [mem_box] at h
      obtain ⟨h1, h2⟩ := h
      cases k <;> simp only [bondDir, e1, e2, Prod.fst_add, Prod.snd_add, add_zero] at h1 h2 <;>
        rw [abs_le] at h1 h2 ⊢ <;> omega
  -- a site of a row without bonds of `γ`, or right of the box, has parity `0`
  have hzero : ∀ y : Plane, (n : ℤ) < y.1 ∨ (n : ℤ) + 1 < |y.2| → par γ y = 0 := by
    intro y hy
    unfold par
    refine Finset.sum_eq_zero fun b hb => if_neg ?_
    rintro ⟨-, h2, h3⟩
    have := hrow b hb
    rw [h2] at this
    rcases hy with hy | hy <;> linarith [this.2.2, this.1]
  rw [mem_box] at hx
  by_cases h1 : (n : ℤ) < x.1
  · exact hzero x (Or.inl h1)
  by_cases h2 : (n : ℤ) < |x.2|
  · -- rows `n + 1` and `-(n + 1)` can still carry bonds of `γ` (vertical ones do not count)
    by_cases h3 : (n : ℤ) + 1 < |x.2|
    · exact hzero x (Or.inr h3)
    · -- `|x₂| = n + 1`: horizontal bonds of `γ` have both ends' rows in `[-n, n]`
      unfold par
      refine Finset.sum_eq_zero ?_
      rintro ⟨y, k⟩ hb
      refine if_neg ?_
      rintro ⟨hk, h2', -⟩
      dsimp only at hk h2'
      subst hk
      have hy : |y.2| ≤ n := by
        rcases (mem_bonds _ y false).1 (hsub hb) with h | h
        · exact (mem_box.1 h).2
        · have := (mem_box.1 h).2
          simpa [bondDir, e1] using this
      rw [h2'] at hy
      linarith
  · -- left of the box: move up, crossing no vertical bond of `γ`, to a row above the box
    push Not at h1 h2
    have hleft : x.1 < -(n : ℤ) := by
      by_contra hc
      push Not at hc
      exact hx ⟨abs_le.2 ⟨hc, h1⟩, h2⟩
    have hup : ∀ m : ℕ, par γ x = par γ (x + (0, (m : ℤ))) := by
      intro m
      induction m with
      | zero => simp [Prod.mk_zero_zero]
      | succ m ih =>
        have hv : ind γ (x + (0, (m : ℤ)), true) = 0 := by
          unfold ind
          rw [if_neg]
          intro hb
          have hfst : ∀ y : Plane, y ∈ box n → y.1 = x.1 → False := fun y hy hy1 => by
            have := (mem_box.1 hy).1
            rw [hy1, abs_le] at this
            linarith [this.1]
          rcases (mem_bonds _ _ true).1 (hsub hb) with h | h
          · exact hfst _ h (by simp)
          · exact hfst _ h (by simp [bondDir, e2])
        rw [ih, show x + ((0 : ℤ), ((m + 1 : ℕ) : ℤ)) = x + (0, (m : ℤ)) + e2 by
          ext <;> simp [e2]; ring, par_add_e2 hγ, hv, add_zero]
    rw [hup (2 * n + 2)]
    refine hzero _ (Or.inr ?_)
    simp only [Prod.snd_add]
    rw [abs_le] at h2
    rw [lt_abs]
    left
    push_cast
    linarith [h2.1]

/-- Flipping twice is the identity. -/
theorem flipInside_flipInside (γ : Finset Bond) (σ : Config Spin) :
    flipInside γ (flipInside γ σ) = σ := by
  funext x
  unfold flipInside
  by_cases h : par γ x = 1 <;> simp only [h, if_true, if_false]
  cases σ x <;> rfl

/-- **Peierls' flip bound.** Under the finite-volume plus measure in `B(n)`, an even set `γ` of
bonds meeting the box is contained in the disagreement set with probability at most
`e^{-2J|γ|}`. -/
theorem plus_prob_contour_le (J : ℝ) (n : ℕ) {γ : Finset Bond} (hγ : IsEven γ)
    (hsub : γ ⊆ bonds (box n)) :
    expect J (box n) plusConfig ({σ | γ ⊆ disagree (box n) σ}.indicator 1) ≤
      Real.exp (-(2 * J) * γ.card) := by
  set Λ := box n
  have hplus : ∀ ζ : Λ → Spin, ∀ x, x ∉ Λ → fill plusConfig Λ ζ x = .plus := fun ζ x hx => by
    simp [fill, hx, plusConfig]
  have hFplus : ∀ ζ : Λ → Spin, ∀ x, x ∉ Λ → flipInside γ (fill plusConfig Λ ζ) x = .plus :=
    fun ζ x hx => by
      unfold flipInside
      rw [par_eq_zero_off_box hγ hsub hx]
      simp [hplus ζ x hx]
  -- the flipped configuration is again a filling of the box
  let φ : (Λ → Spin) → (Λ → Spin) := fun ζ y => flipInside γ (fill plusConfig Λ ζ) y.1
  have hφ : ∀ ζ, fill plusConfig Λ (φ ζ) = flipInside γ (fill plusConfig Λ ζ) := fun ζ => by
    funext x
    by_cases hx : x ∈ Λ
    · simp [fill, hx, φ]
    · simp only [fill, hx, dif_neg, not_false_eq_true]
      rw [hFplus ζ x hx]; rfl
  have hfinj : Function.Injective (fill plusConfig Λ) := fun ζ ζ' h => by
    funext x
    have := congrFun h x.1
    simpa [fill, x.2] using this
  have hφinj : Function.Injective φ := fun ζ ζ' h => by
    apply hfinj
    have := congrArg (flipInside γ) ((hφ ζ).symm.trans ((congrArg _ h).trans (hφ ζ')))
    rwa [flipInside_flipInside, flipInside_flipInside] at this
  set w : (Λ → Spin) → ℝ := fun ζ => weight J Λ (fill plusConfig Λ ζ) with hw
  have hw0 : ∀ ζ, 0 ≤ w ζ := fun ζ => (Real.exp_pos _).le
  set S := Finset.univ.filter fun ζ : Λ → Spin => γ ⊆ disagree Λ (fill plusConfig Λ ζ)
  -- the weight goes up by `e^{2J|γ|}` under the flip
  have hratio : ∀ ζ ∈ S, w ζ = Real.exp (-(2 * J) * γ.card) * w (φ ζ) := by
    intro ζ hζ
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hζ
    have hD := disagree_flipInside hγ (hplus ζ) (hFplus ζ) hζ
    have hc : ((disagree Λ (flipInside γ (fill plusConfig Λ ζ))).card : ℝ) =
        (disagree Λ (fill plusConfig Λ ζ)).card - γ.card := by
      rw [hD, Finset.card_sdiff_of_subset hζ, Nat.cast_sub (Finset.card_le_card hζ)]
    show weight J Λ (fill plusConfig Λ ζ) =
      Real.exp (-(2 * J) * γ.card) * weight J Λ (fill plusConfig Λ (φ ζ))
    rw [hφ, weight_eq, weight_eq, hc]
    simp only [← Real.exp_add]
    congr 1
    ring
  have hZ : 0 < ∑ ζ : Λ → Spin, w ζ :=
    Finset.sum_pos (fun ζ _ => Real.exp_pos _) ⟨fun _ => .plus, Finset.mem_univ _⟩
  unfold expect
  rw [div_le_iff₀ hZ]
  calc ∑ ζ : Λ → Spin, weight J Λ (fill plusConfig Λ ζ) *
        {σ | γ ⊆ disagree Λ σ}.indicator 1 (fill plusConfig Λ ζ)
      = ∑ ζ ∈ S, w ζ := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun ζ _ => ?_
        by_cases h : γ ⊆ disagree Λ (fill plusConfig Λ ζ) <;> simp [h, hw]
    _ = Real.exp (-(2 * J) * γ.card) * ∑ ζ ∈ S, w (φ ζ) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl hratio
    _ = Real.exp (-(2 * J) * γ.card) * ∑ ζ ∈ S.image φ, w ζ := by
        rw [Finset.sum_image (fun ζ _ ζ' _ h => hφinj h)]
    _ ≤ Real.exp (-(2 * J) * γ.card) * ∑ ζ : Λ → Spin, w ζ := by
        exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.subset_univ _) (fun ζ _ _ => hw0 ζ)) (Real.exp_pos _).le

end Peierls

end UPD

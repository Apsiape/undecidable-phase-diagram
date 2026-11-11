/-
# `pay:sum` (the combinatorial half): the sensor sum

New in this project (session 9). The paper's `pay:sum` sums the factor `W_e` of `pay:factor`(b)
over the private coordinates of an edge. The coefficients `G_n`, `H_n`, `b_n`, `J_n` and their
closed forms are in `Proof/Thermal.lean`; here is the sum itself, for the sensor part of `W_e`,
and the conversion of the result to an Ising coupling.

The sensor is modelled abstractly: two switches `x⁻`, `x⁺` (a map `Fin 2 → Bool`, `0` is `x⁻`,
`1` is `x⁺`), copies indexed by a finite type `C` with a labelling `lab : C → Fin 2` saying which
switch each copy copies, and candidate free bits `y^±(j)`, `j < N` (`Cfg`). A configuration is
consistent (`Consistent`) when every copy equals its switch and a bit `y^±(j)` is `1` only if
`x^± = 1` and `j < L_±`. The identification of the switches, copies and bits with the coordinates
of a ready grid (the components of the cell records and of `ℓ^S`, `ℓ^N` along the first column,
with `L_± = 20n ± 5`) belongs to `pay:factor` and is not here; nor is the arm factor
`1[arm ≡ σ_u]` (one admissible value).

* `weight`: the sensor part of `W_e`,
  `1[sensor consistent] 1[(x⁻,x⁺) = (0,1) ⇒ σ_v = σ_u] e^{-20β(x⁻+x⁺)}`.
* **`sum_weight`**: if `L_± ≤ N`, the sum of `weight` over all configurations is
  `1 + 2^{L₋} e^{-20β} + 2^{L₊} e^{-20β} 1[σ_u = σ_v] + 2^{L₋+L₊} e^{-40β}` (as in the paper:
  split over the four switch values; given the switches, the copies are determined and `y^±` is
  free exactly on `{j < L_±}` when `x^± = 1`, and zero otherwise).
* **`pay_sum`**: with `L = (20n - 5, 20n + 5)`, `n ≥ 1` and `20n + 5 ≤ N`, the sum is
  `H_n + G_n 1[σ_u = σ_v]` (`Hc`, `Gc`).
* **`coupling`**: `H_n + G_n 1[σ_u = σ_v] = C_n exp(J_n σ_u σ_v)` with
  `C_n = sqrt(H_n (H_n + G_n))` and `J_n = Jc (bc n β)` (`e^{2J_n} = 1 + 1/b_n = (H_n+G_n)/H_n`).
* `weight_nonneg`, `sum_weight_pos`.

Steps: `weight_eq` (split off the switch part `switchW`), `sum_bits` (`2^l` choices for the bits
of a switch that is on, one for a switch that is off), `sum_copies` (one choice for the copies),
`sum_free`, `sum_fiber` (the count given the switches), `switchW_ff`, ..., `switchW_tt` (the four
switch values).
-/
import UndecidablePhaseDiagram.Proof.Thermal
import UndecidablePhaseDiagram.Hypotheses

set_option autoImplicit false

noncomputable section

namespace UPD

namespace Sensor

open Real

variable {C : Type} [Fintype C] [DecidableEq C]

/-! ## The abstract sensor -/

/-- A sensor configuration: the switches `x` (`0` is `x⁻`, `1` is `x⁺`), the copies (indexed by
`C`), and the candidate free bits `y k j`, `j < N`. -/
abbrev Cfg (C : Type) (N : ℕ) := (Fin 2 → Bool) × (C → Bool) × (Fin 2 → Fin N → Bool)

/-- The sensor is consistent: every copy equals the switch it copies, and a bit `y^±(j)` is `1`
only if the switch `x^±` is `1` and `j < L_±`. -/
def Consistent {N : ℕ} (lab : C → Fin 2) (L : Fin 2 → ℕ) (s : Cfg C N) : Prop :=
  (∀ c, s.2.1 c = s.1 (lab c)) ∧
    ∀ (k : Fin 2) (j : Fin N), s.2.2 k j = true → s.1 k = true ∧ (j : ℕ) < L k

instance {N : ℕ} (lab : C → Fin 2) (L : Fin 2 → ℕ) (s : Cfg C N) :
    Decidable (Consistent lab L s) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- A bit as a real number. -/
def bitR (b : Bool) : ℝ := if b then 1 else 0

/-- `pay:factor`(b), the sensor part of `W_e`:
`1[sensor consistent] 1[(x⁻,x⁺) = (0,1) ⇒ σ_v = σ_u] e^{-20β(x⁻+x⁺)}`. -/
def weight {N : ℕ} (lab : C → Fin 2) (L : Fin 2 → ℕ) (β : ℝ) (σu σv : Spin) (s : Cfg C N) : ℝ :=
  (if Consistent lab L s then 1 else 0) *
    (if (s.1 0 = false ∧ s.1 1 = true) → σu = σv then 1 else 0) *
    Real.exp (-20 * β * (bitR (s.1 0) + bitR (s.1 1)))

/-- The part of `weight` that depends on the switches only. -/
def switchW (β : ℝ) (σu σv : Spin) (x : Fin 2 → Bool) : ℝ :=
  (if (x 0 = false ∧ x 1 = true) → σu = σv then 1 else 0) *
    Real.exp (-20 * β * (bitR (x 0) + bitR (x 1)))

omit [DecidableEq C] in
/-- `weight` splits into the consistency indicator and the switch part. -/
theorem weight_eq {N : ℕ} (lab : C → Fin 2) (L : Fin 2 → ℕ) (β : ℝ) (σu σv : Spin)
    (s : Cfg C N) :
    weight lab L β σu σv s = (if Consistent lab L s then 1 else 0) * switchW β σu σv s.1 := by
  unfold weight switchW; ring

/-! ## Counting the consistent configurations -/

/-- Two decidability instances give the same indicator. -/
theorem ite_inst {P : Prop} (i₁ i₂ : Decidable P) : @ite ℝ P i₁ 1 0 = @ite ℝ P i₂ 1 0 := by
  rw [Subsingleton.elim i₁ i₂]

/-- The bits of one switch: `2^l` choices if the switch is on, one if it is off. -/
theorem sum_bits (b : Bool) {l N : ℕ} (hl : l ≤ N) :
    ∑ f : Fin N → Bool,
        (if ∀ j : Fin N, f j = true → b = true ∧ (j : ℕ) < l then (1 : ℝ) else 0) =
      if b then 2 ^ l else 1 := by
  have h : ∀ f : Fin N → Bool,
      (if ∀ j : Fin N, f j = true → b = true ∧ (j : ℕ) < l then (1 : ℝ) else 0) =
        ∏ j : Fin N, (if f j = true → b = true ∧ (j : ℕ) < l then (1 : ℝ) else 0) :=
    fun f => by rw [Fintype.prod_boole]; exact ite_inst _ _
  rw [Finset.sum_congr rfl (fun f _ => h f),
    ← Fintype.prod_sum (fun (j : Fin N) (c : Bool) =>
      if c = true → b = true ∧ (j : ℕ) < l then (1 : ℝ) else 0)]
  simp only [Fintype.sum_bool]
  cases b
  · simp
  · simp only [true_and, forall_const, Bool.false_eq_true, IsEmpty.forall_iff, ↓reduceIte]
    rw [Fin.prod_univ_eq_prod_range (fun j => (if j < l then (1 : ℝ) else 0) + 1) N,
      ← Finset.prod_range_mul_prod_Ico _ hl]
    have e1 : ∏ j ∈ Finset.range l, ((if j < l then (1 : ℝ) else 0) + 1) = 2 ^ l := by
      rw [Finset.prod_congr rfl (g := fun _ => (2 : ℝ)), Finset.prod_const, Finset.card_range]
      intro j hj; rw [if_pos (Finset.mem_range.1 hj)]; norm_num
    have e2 : ∏ j ∈ Finset.Ico l N, ((if j < l then (1 : ℝ) else 0) + 1) = 1 := by
      refine Finset.prod_eq_one (fun j hj => ?_)
      rw [if_neg (by simp only [Finset.mem_Ico] at hj; omega)]; norm_num
    rw [e1, e2, mul_one]

/-- The copies: one choice. -/
theorem sum_copies (lab : C → Fin 2) (x : Fin 2 → Bool) :
    ∑ c : C → Bool, (if ∀ c', c c' = x (lab c') then (1 : ℝ) else 0) = 1 := by
  have h : ∀ c : C → Bool, (if ∀ c', c c' = x (lab c') then (1 : ℝ) else 0) =
      if c = fun c' => x (lab c') then 1 else 0 := by
    intro c
    by_cases hc : c = fun c' => x (lab c')
    · subst hc; simp
    · rw [if_neg hc, if_neg]; intro h'; exact hc (funext h')
  rw [Finset.sum_congr rfl (fun c _ => h c)]
  simp

/-- The free bits of both switches. -/
theorem sum_free {N : ℕ} {L : Fin 2 → ℕ} (hL : ∀ k, L k ≤ N) (x : Fin 2 → Bool) :
    ∑ y : Fin 2 → Fin N → Bool,
        (if ∀ (k : Fin 2) (j : Fin N), y k j = true → x k = true ∧ (j : ℕ) < L k
          then (1 : ℝ) else 0) =
      (if x 0 then 2 ^ L 0 else 1) * (if x 1 then 2 ^ L 1 else 1) := by
  have h : ∀ y : Fin 2 → Fin N → Bool,
      (if ∀ (k : Fin 2) (j : Fin N), y k j = true → x k = true ∧ (j : ℕ) < L k
        then (1 : ℝ) else 0) =
      ∏ k : Fin 2,
        (if ∀ j : Fin N, y k j = true → x k = true ∧ (j : ℕ) < L k then (1 : ℝ) else 0) :=
    fun y => by rw [Fintype.prod_boole]; exact ite_inst _ _
  rw [Finset.sum_congr rfl (fun y _ => h y),
    ← Fintype.prod_sum (fun (k : Fin 2) (f : Fin N → Bool) =>
      if ∀ j : Fin N, f j = true → x k = true ∧ (j : ℕ) < L k then (1 : ℝ) else 0),
    Fin.prod_univ_two, sum_bits _ (hL 0), sum_bits _ (hL 1)]

/-- Given the switches, the number of consistent configurations is `∏_± (x^± ? 2^{L_±} : 1)`. -/
theorem sum_fiber (lab : C → Fin 2) {N : ℕ} {L : Fin 2 → ℕ} (hL : ∀ k, L k ≤ N)
    (x : Fin 2 → Bool) :
    ∑ p : (C → Bool) × (Fin 2 → Fin N → Bool),
        (if Consistent lab L (x, p) then (1 : ℝ) else 0) =
      (if x 0 then 2 ^ L 0 else 1) * (if x 1 then 2 ^ L 1 else 1) := by
  have h : ∀ (c : C → Bool) (y : Fin 2 → Fin N → Bool),
      (if Consistent lab L (x, c, y) then (1 : ℝ) else 0) =
        (if ∀ c', c c' = x (lab c') then (1 : ℝ) else 0) *
        (if ∀ (k : Fin 2) (j : Fin N), y k j = true → x k = true ∧ (j : ℕ) < L k
          then (1 : ℝ) else 0) := by
    intro c y
    by_cases h1 : ∀ c', c c' = x (lab c') <;>
      by_cases h2 : ∀ (k : Fin 2) (j : Fin N), y k j = true → x k = true ∧ (j : ℕ) < L k
    · rw [if_pos (show Consistent lab L (x, c, y) from And.intro h1 h2), if_pos h1, if_pos h2,
        one_mul]
    · rw [if_neg (show ¬ Consistent lab L (x, c, y) from fun h => h2 (And.right h)), if_neg h2,
        mul_zero]
    · rw [if_neg (show ¬ Consistent lab L (x, c, y) from fun h => h1 (And.left h)), if_neg h1,
        zero_mul]
    · rw [if_neg (show ¬ Consistent lab L (x, c, y) from fun h => h1 (And.left h)), if_neg h1,
        zero_mul]
  rw [Fintype.sum_prod_type]
  simp only [h]
  rw [← Finset.sum_mul_sum, sum_copies, sum_free hL, one_mul]

/-! ## The sensor sum -/

/-- The four values of `switchW`: `(x⁻,x⁺) = (0,0)`. -/
theorem switchW_ff (β : ℝ) (σu σv : Spin) : switchW β σu σv ![false, false] = 1 := by
  simp [switchW, bitR]

/-- `(x⁻,x⁺) = (1,0)`. -/
theorem switchW_tf (β : ℝ) (σu σv : Spin) :
    switchW β σu σv ![true, false] = Real.exp (-20 * β) := by
  simp [switchW, bitR]

/-- `(x⁻,x⁺) = (0,1)`: the switch that copies `σ_u` into `σ_v`. -/
theorem switchW_ft (β : ℝ) (σu σv : Spin) :
    switchW β σu σv ![false, true] = Real.exp (-20 * β) * (if σu = σv then 1 else 0) := by
  simp [switchW, bitR]

/-- `(x⁻,x⁺) = (1,1)`. -/
theorem switchW_tt (β : ℝ) (σu σv : Spin) :
    switchW β σu σv ![true, true] = Real.exp (-40 * β) := by
  simp [switchW, bitR]
  ring

/-- `pay:sum`, the combinatorial half: the sum of the sensor weight over all configurations is
`1 + 2^{L₋} e^{-20β} + 2^{L₊} e^{-20β} 1[σ_u = σ_v] + 2^{L₋+L₊} e^{-40β}`. -/
theorem sum_weight (lab : C → Fin 2) {N : ℕ} {L : Fin 2 → ℕ} (hL : ∀ k, L k ≤ N) (β : ℝ)
    (σu σv : Spin) :
    ∑ s : Cfg C N, weight lab L β σu σv s =
      1 + 2 ^ L 0 * Real.exp (-20 * β) +
        2 ^ L 1 * Real.exp (-20 * β) * (if σu = σv then 1 else 0) +
        2 ^ (L 0 + L 1) * Real.exp (-40 * β) := by
  simp only [weight_eq]
  rw [Fintype.sum_prod_type]
  simp only [← Finset.sum_mul, sum_fiber lab hL]
  rw [← (finTwoArrowEquiv Bool).symm.sum_comp, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, finTwoArrowEquiv_symm_apply, switchW_ff, switchW_tf, switchW_ft,
    switchW_tt, Matrix.cons_val_zero, Matrix.cons_val_one, ite_true,
    Bool.false_eq_true, ite_false]
  rw [pow_add]; ring

/-- `pay:sum` for a ready edge: with `L₋ = 20n - 5` and `L₊ = 20n + 5`, the sensor sum is
`H_n + G_n 1[σ_u = σ_v]`. -/
theorem pay_sum (lab : C → Fin 2) {n N : ℕ} (hn : 1 ≤ n) (hN : 20 * n + 5 ≤ N) (β : ℝ)
    (σu σv : Spin) :
    ∑ s : Cfg C N, weight lab ![20 * n - 5, 20 * n + 5] β σu σv s =
      Hc n β + Gc n β * (if σu = σv then 1 else 0) := by
  have hL : ∀ k, (![20 * n - 5, 20 * n + 5] : Fin 2 → ℕ) k ≤ N := by
    intro k; fin_cases k <;> simp <;> omega
  rw [sum_weight lab hL]
  have h1 : (2 : ℝ) ^ ((20 * n - 5 : ℝ)) = (2 : ℝ) ^ (20 * n - 5) := by
    rw [← Real.rpow_natCast]; congr 1; rw [Nat.cast_sub (by omega)]; push_cast; ring
  have h2 : (2 : ℝ) ^ ((20 * n + 5 : ℝ)) = (2 : ℝ) ^ (20 * n + 5) := by
    rw [← Real.rpow_natCast]; push_cast; ring_nf
  have h3 : (2 : ℝ) ^ ((40 * n : ℝ)) = (2 : ℝ) ^ ((20 * n - 5) + (20 * n + 5)) := by
    rw [← Real.rpow_natCast, show (20 * n - 5) + (20 * n + 5) = 40 * n by omega]; push_cast
    ring_nf
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  unfold Hc Gc
  rw [h1, h2, h3]
  ring

/-- `pay:sum`: `H_n + G_n 1[σ_u = σ_v] = C_n e^{J_n σ_u σ_v}` with `C_n = sqrt(H_n (H_n + G_n))`
and `J_n = Jc (b_n)`, `b_n = H_n / G_n` (so `e^{2J_n} = 1 + 1/b_n = (H_n + G_n)/H_n`). -/
theorem coupling (n : ℕ) (β : ℝ) (σu σv : Spin) :
    Hc n β + Gc n β * (if σu = σv then 1 else 0) =
      Real.sqrt (Hc n β * (Hc n β + Gc n β)) *
        Real.exp (Jc (bc n β) * Ising.val σu * Ising.val σv) := by
  have hH := Hc_pos n β
  have hG := Gc_pos n β
  have hb := bc_pos n β
  have hE := Real.exp_pos (Jc (bc n β))
  have hE2 : Real.exp (Jc (bc n β)) ^ 2 = (Hc n β + Gc n β) / Hc n β := by
    rw [← Real.exp_nat_mul]; push_cast
    rw [exp_two_Jc hb]; unfold bc; field_simp
  have hSE : Real.sqrt (Hc n β * (Hc n β + Gc n β)) * Real.exp (Jc (bc n β)) =
      Hc n β + Gc n β := by
    have e : Real.exp (Jc (bc n β)) = Real.sqrt ((Hc n β + Gc n β) / Hc n β) := by
      rw [← hE2, Real.sqrt_sq hE.le]
    rw [e, ← Real.sqrt_mul (mul_pos hH (add_pos hH hG)).le,
      show Hc n β * (Hc n β + Gc n β) * ((Hc n β + Gc n β) / Hc n β) =
        (Hc n β + Gc n β) ^ 2 by field_simp]
    exact Real.sqrt_sq (add_pos hH hG).le
  have hS : Real.sqrt (Hc n β * (Hc n β + Gc n β)) =
      (Hc n β + Gc n β) / Real.exp (Jc (bc n β)) := by
    rw [eq_div_iff hE.ne']; exact hSE
  have hminus : Hc n β = Real.sqrt (Hc n β * (Hc n β + Gc n β)) * Real.exp (-Jc (bc n β)) := by
    rw [hS, Real.exp_neg]
    calc Hc n β = (Hc n β + Gc n β) / ((Hc n β + Gc n β) / Hc n β) := by field_simp
      _ = (Hc n β + Gc n β) / Real.exp (Jc (bc n β)) ^ 2 := by rw [hE2]
      _ = _ := by ring
  have v1 : Ising.val .plus = 1 := rfl
  have v2 : Ising.val .minus = -1 := rfl
  cases σu <;> cases σv
  · rw [if_pos rfl, v1, mul_one, show Jc (bc n β) * 1 * 1 = Jc (bc n β) by ring]
    exact hSE.symm
  · rw [if_neg (by decide), v1, v2, mul_zero, add_zero,
      show Jc (bc n β) * 1 * -1 = -Jc (bc n β) by ring]
    exact hminus
  · rw [if_neg (by decide), v1, v2, mul_zero, add_zero,
      show Jc (bc n β) * -1 * 1 = -Jc (bc n β) by ring]
    exact hminus
  · rw [if_pos rfl, v2, mul_one, show Jc (bc n β) * -1 * -1 = Jc (bc n β) by ring]
    exact hSE.symm

/-! ## Positivity -/

omit [DecidableEq C] in
/-- The sensor weight is nonnegative. -/
theorem weight_nonneg {N : ℕ} (lab : C → Fin 2) (L : Fin 2 → ℕ) (β : ℝ) (σu σv : Spin)
    (s : Cfg C N) : 0 ≤ weight lab L β σu σv s := by
  unfold weight; positivity

/-- The sensor sum is positive (the configuration with all switches off has weight `1`). -/
theorem sum_weight_pos (lab : C → Fin 2) {N : ℕ} {L : Fin 2 → ℕ} (hL : ∀ k, L k ≤ N) (β : ℝ)
    (σu σv : Spin) : 0 < ∑ s : Cfg C N, weight lab L β σu σv s := by
  rw [sum_weight lab hL]; positivity

end Sensor

end UPD

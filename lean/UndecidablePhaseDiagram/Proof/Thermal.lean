/-
# `pay:sum` (the coefficients) and `prf:thermal`: the sensor coupling `J_n(β)`

`pay:sum` defines, for a ready depth with label `n`,
`G_n = 2^{20n+5} e^{-20β}`, `H_n = 1 + 2^{20n-5} e^{-20β} + 2^{40n} e^{-40β}`,
`b_n(β) = H_n / G_n` and the coupling `J_n(β)` with `e^{2 J_n} = 1 + 1/b_n`.
Here: those definitions (`Gc`, `Hc`, `bc`, `Jc`), the closed form
`b_n = 2^{20(n - 1/4 - s)} + 2^{20(s - n - 1/4)} + 2^{-10}`, `s = β / log 2` (`bc_eq`), the
identity `tanh J = 1 / (2b + 1)` (`tanh_Jc`), and `prf:thermal` (a), (b), (c)
(`thermal_a`, `thermal_b`, `thermal_c`).
The combinatorial half of `pay:sum` (the sum over the sensor configurations) is not here.
-/
import UndecidablePhaseDiagram.Statements
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option autoImplicit false

noncomputable section

namespace UPD

open Real

/-- `pay:sum`: `G_n = 2^{20n+5} e^{-20β}`. -/
def Gc (n : ℕ) (β : ℝ) : ℝ := (2 : ℝ) ^ ((20 * n + 5 : ℝ)) * exp (-20 * β)

/-- `pay:sum`: `H_n = 1 + 2^{20n-5} e^{-20β} + 2^{40n} e^{-40β}`. -/
def Hc (n : ℕ) (β : ℝ) : ℝ :=
  1 + (2 : ℝ) ^ ((20 * n - 5 : ℝ)) * exp (-20 * β) + (2 : ℝ) ^ ((40 * n : ℝ)) * exp (-40 * β)

/-- `pay:sum`: `b_n(β) = H_n / G_n`. -/
def bc (n : ℕ) (β : ℝ) : ℝ := Hc n β / Gc n β

/-- `pay:sum`: the coupling `J = ½ log (1 + 1/b)`, so that `e^{2J} = 1 + 1/b`. -/
def Jc (b : ℝ) : ℝ := log (1 + 1 / b) / 2

theorem Gc_pos (n : ℕ) (β : ℝ) : 0 < Gc n β := by unfold Gc; positivity

theorem Hc_pos (n : ℕ) (β : ℝ) : 0 < Hc n β := by unfold Hc; positivity

theorem bc_pos (n : ℕ) (β : ℝ) : 0 < bc n β := div_pos (Hc_pos n β) (Gc_pos n β)

/-- `e^{-c β} = 2^{-c s}` with `s = β / log 2`. -/
theorem exp_eq_two_rpow (c β : ℝ) : exp (-c * β) = (2 : ℝ) ^ (-c * (β / log 2)) := by
  rw [rpow_def_of_pos (by norm_num)]
  congr 1
  have : log 2 ≠ 0 := by positivity
  field_simp

/-- `pay:sum`: `b_n = 2^{20(n - 1/4 - s)} + 2^{20(s - n - 1/4)} + 2^{-10}`, `s = β / log 2`. -/
theorem bc_eq (n : ℕ) (β : ℝ) :
    bc n β = (2 : ℝ) ^ (20 * (n - 1 / 4 - β / log 2)) +
      (2 : ℝ) ^ (20 * (β / log 2 - n - 1 / 4)) + (2 : ℝ) ^ (-10 : ℝ) := by
  set s := β / log 2
  have h20 : exp (-20 * β) = (2 : ℝ) ^ (-20 * s) := exp_eq_two_rpow 20 β
  have h40 : exp (-40 * β) = (2 : ℝ) ^ (-40 * s) := exp_eq_two_rpow 40 β
  unfold bc Hc Gc
  rw [h20, h40]
  have hpos : (0 : ℝ) < (2 : ℝ) ^ ((20 * n + 5 : ℝ)) * (2 : ℝ) ^ (-20 * s) := by positivity
  rw [div_eq_iff hpos.ne']
  simp only [add_mul, ← rpow_add (by norm_num : (0 : ℝ) < 2)]
  have e1 : (20 * (n - 1 / 4 - s) + (20 * n + 5 + -20 * s) : ℝ) = 40 * n + -40 * s := by ring
  have e2 : (20 * (s - n - 1 / 4) + (20 * n + 5 + -20 * s) : ℝ) = 0 := by ring
  have e3 : (-10 + (20 * n + 5 + -20 * s) : ℝ) = 20 * n - 5 + -20 * s := by ring
  rw [e1, e2, e3, rpow_zero]
  ring

/-- `b_n = 2^{-5} (u + u⁻¹) + 2^{-10}` with `u = 2^{20(s - n)}`. -/
theorem bc_eq_u (n : ℕ) (β : ℝ) :
    bc n β = (2 : ℝ) ^ (-5 : ℝ) * ((2 : ℝ) ^ (20 * (β / log 2 - n)) +
      ((2 : ℝ) ^ (20 * (β / log 2 - n)))⁻¹) + (2 : ℝ) ^ (-10 : ℝ) := by
  rw [bc_eq]
  have e1 : (2 : ℝ) ^ (20 * (n - 1 / 4 - β / log 2)) =
      (2 : ℝ) ^ (-5 : ℝ) * ((2 : ℝ) ^ (20 * (β / log 2 - n)))⁻¹ := by
    rw [← rpow_neg (by norm_num), ← rpow_add (by norm_num)]; ring_nf
  have e2 : (2 : ℝ) ^ (20 * (β / log 2 - n - 1 / 4)) =
      (2 : ℝ) ^ (-5 : ℝ) * (2 : ℝ) ^ (20 * (β / log 2 - n)) := by
    rw [← rpow_add (by norm_num)]; ring_nf
  rw [e1, e2]; ring

theorem exp_two_Jc {b : ℝ} (hb : 0 < b) : exp (2 * Jc b) = 1 + 1 / b := by
  unfold Jc
  rw [show 2 * (log (1 + 1 / b) / 2) = log (1 + 1 / b) by ring, exp_log (by positivity)]

/-- `prf:thermal`: `tanh J = 1 / (2b + 1)` when `e^{2J} = 1 + 1/b`. -/
theorem tanh_Jc {b : ℝ} (hb : 0 < b) : tanh (Jc b) = 1 / (2 * b + 1) := by
  have h := exp_two_Jc hb
  rw [tanh_eq_sinh_div_cosh, sinh_eq, cosh_eq]
  have hx : exp (Jc b) ^ 2 = 1 + 1 / b := by rw [← exp_nat_mul]; push_cast; exact h
  have hpos : 0 < exp (Jc b) := exp_pos _
  rw [exp_neg]
  field_simp
  have : exp (Jc b) * exp (Jc b) = 1 + 1 / b := by rw [← sq]; exact hx
  field_simp at this
  nlinarith [this]

/-- One of `u`, `u⁻¹` is at least `2^{c}` when `|x| ≥ c / 20`, `u = 2^{20 x}`. -/
theorem max_u_ge {x c : ℝ} (h : c ≤ |20 * x|) :
    (2 : ℝ) ^ c ≤ (2 : ℝ) ^ (20 * x) ∨ (2 : ℝ) ^ c ≤ ((2 : ℝ) ^ (20 * x))⁻¹ := by
  rcases le_abs'.1 h with h' | h'
  · right; rw [← rpow_neg (by norm_num)]
    exact rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  · left; exact rpow_le_rpow_of_exponent_le (by norm_num) h'

/-- `prf:thermal`(a): if `|s - m| < 1/20`, then `b_m(β) ≤ 81/1024 < 1/8` and `e^{J_m(β)} > 3`. -/
theorem thermal_a (m : ℕ) (β : ℝ) (h : |β / log 2 - m| < 1 / 20) :
    bc m β ≤ 81 / 1024 ∧ (81 / 1024 : ℝ) < 1 / 8 ∧ 3 < exp (Jc (bc m β)) := by
  set x := β / log 2 - m
  set u := (2 : ℝ) ^ (20 * x)
  have hx : |20 * x| < 1 := by rw [abs_mul]; norm_num; linarith
  have hu1 : (1 / 2 : ℝ) < u := by
    have := rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) (neg_lt_of_abs_lt hx)
    rwa [rpow_neg_one, ← one_div] at this
  have hu2 : u < 2 := by
    have := rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) (lt_of_abs_lt hx)
    rwa [rpow_one] at this
  have hupos : 0 < u := by linarith
  have hsum : u + u⁻¹ < 5 / 2 := by
    rw [← sub_pos]
    have : 5 / 2 - (u + u⁻¹) = (2 - u) * (u - 1 / 2) / u := by field_simp; ring
    rw [this]; exact div_pos (mul_pos (by linarith) (by linarith)) hupos
  have hb : bc m β ≤ 81 / 1024 := by
    rw [bc_eq_u]
    have h5 : (2 : ℝ) ^ (-5 : ℝ) = 1 / 32 := by norm_num [rpow_neg, rpow_natCast]
    have h10 : (2 : ℝ) ^ (-10 : ℝ) = 1 / 1024 := by norm_num [rpow_neg, rpow_natCast]
    rw [h5, h10]; linarith
  refine ⟨hb, by norm_num, ?_⟩
  have hbpos := bc_pos m β
  have h2 := exp_two_Jc hbpos
  have h9 : (9 : ℝ) < exp (2 * Jc (bc m β)) := by
    rw [h2]
    have : (1024 / 81 : ℝ) ≤ 1 / bc m β := by
      rw [le_div_iff₀ hbpos]; nlinarith
    linarith
  have hsq : exp (2 * Jc (bc m β)) = exp (Jc (bc m β)) ^ 2 := by
    rw [← exp_nat_mul]; push_cast; ring_nf
  rw [hsq] at h9
  nlinarith [exp_pos (Jc (bc m β))]

/-- `prf:thermal`(b): if `|s - m| ≥ 19/20`, then `b_m(β) ≥ 2^{14}` and
`4 tanh J_m(β) ≤ 4/32769 < 1`. -/
theorem thermal_b (m : ℕ) (β : ℝ) (h : 19 / 20 ≤ |β / log 2 - m|) :
    (2 : ℝ) ^ 14 ≤ bc m β ∧ 4 * tanh (Jc (bc m β)) ≤ 4 / 32769 ∧ (4 / 32769 : ℝ) < 1 := by
  set x := β / log 2 - m
  set u := (2 : ℝ) ^ (20 * x)
  have hupos : 0 < u := by positivity
  have h19 : (19 : ℝ) ≤ |20 * x| := by rw [abs_mul]; norm_num; linarith
  have hmax : (2 : ℝ) ^ (19 : ℝ) ≤ u + u⁻¹ := by
    rcases max_u_ge h19 with h' | h'
    · linarith [inv_pos.2 hupos]
    · linarith
  have hb : (2 : ℝ) ^ 14 ≤ bc m β := by
    rw [bc_eq_u]
    have h5 : (2 : ℝ) ^ (-5 : ℝ) = 1 / 32 := by norm_num [rpow_neg, rpow_natCast]
    have h19' : (2 : ℝ) ^ (19 : ℝ) = 2 ^ 19 := by norm_num [rpow_natCast]
    rw [h5]; rw [h19'] at hmax
    have : (0 : ℝ) < (2 : ℝ) ^ (-10 : ℝ) := by positivity
    nlinarith
  refine ⟨hb, ?_, by norm_num⟩
  rw [tanh_Jc (bc_pos m β)]
  rw [mul_one_div, div_le_div_iff₀ (by linarith [bc_pos m β]) (by norm_num)]
  nlinarith

/-- `prf:thermal`(c): if `|s - m| > 9/20`, then `b_m(β) > 16` and `4 tanh J_m(β) < 4/33 < 1`. -/
theorem thermal_c (m : ℕ) (β : ℝ) (h : 9 / 20 < |β / log 2 - m|) :
    16 < bc m β ∧ 4 * tanh (Jc (bc m β)) < 4 / 33 ∧ (4 / 33 : ℝ) < 1 := by
  set x := β / log 2 - m
  set u := (2 : ℝ) ^ (20 * x)
  have hupos : 0 < u := by positivity
  have h9 : (9 : ℝ) < |20 * x| := by rw [abs_mul]; norm_num; linarith
  have hmax : (2 : ℝ) ^ (9 : ℝ) < u + u⁻¹ := by
    rcases lt_abs.1 h9 with h' | h'
    · have : (2 : ℝ) ^ (9 : ℝ) < u :=
        rpow_lt_rpow_of_exponent_lt (by norm_num) h'
      linarith [inv_pos.2 hupos]
    · have : (2 : ℝ) ^ (9 : ℝ) < u⁻¹ := by
        rw [← rpow_neg (by norm_num)]
        exact rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
      linarith
  have hb : 16 < bc m β := by
    rw [bc_eq_u]
    have h5 : (2 : ℝ) ^ (-5 : ℝ) = 1 / 32 := by norm_num [rpow_neg, rpow_natCast]
    have h9' : (2 : ℝ) ^ (9 : ℝ) = 2 ^ 9 := by norm_num [rpow_natCast]
    rw [h5]; rw [h9'] at hmax
    have : (0 : ℝ) < (2 : ℝ) ^ (-10 : ℝ) := by positivity
    nlinarith
  refine ⟨hb, ?_, by norm_num⟩
  rw [tanh_Jc (bc_pos m β)]
  rw [mul_one_div, div_lt_div_iff₀ (by linarith [bc_pos m β]) (by norm_num)]
  nlinarith

end UPD

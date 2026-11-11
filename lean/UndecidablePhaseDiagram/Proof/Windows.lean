/-
# `prf:windows`: the rational windows `J_n`

`λ_K = 2 ∑_{j<K} 1/((2j+1) 3^{2j+1})`, `β_n = n λ_{n+3}`, `J_n = (β_n - 1/1000, β_n + 1/1000)`.
* (a) `windows_a`: `0 < log 2 - λ_K ≤ 3 / (4 (2K+1) 9^K)` for `K ≥ 1` (in fact for every `K`), from
  Mathlib's series `log (1 + a⁻¹) = ∑ 2/(2k+1) (1/(2a+1))^{2k+1}` at `a = 1`.
* (b) `windows_b`: `0 < n log 2 - β_n ≤ 3/26244 < 1/1000` for `n ≥ 1`.
* (c) `windows_c`: `β_{n+1} - β_n > 2/3` and `β_1 - 1/1000 > 0`; hence (`betaN_sub_pos`,
  `J_disjoint`) the intervals `J_n`, `n ≥ 1`, consist of positive numbers and are pairwise
  disjoint. Part (c) is pure rational arithmetic.
* (d) `windows_d`: if `β ∈ J_n` (`n ≥ 1`), then `|β / log 2 - n| < 1/250`.
-/
import UndecidablePhaseDiagram.Statements
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

set_option autoImplicit false

noncomputable section

open Finset

namespace UPD

/-! ## Part (c): rational arithmetic -/

/-- The `j`-th term `2 / ((2j+1) 3^{2j+1})` of `λ`, as a rational. -/
def lamTerm (j : ℕ) : ℚ := 2 / ((2 * (j : ℚ) + 1) * 3 ^ (2 * j + 1))

theorem lamTerm_pos (j : ℕ) : 0 < lamTerm j := by unfold lamTerm; positivity

theorem lam_eq_sum (K : ℕ) : lam K = ∑ j ∈ range K, lamTerm j := by
  unfold lam lamTerm
  rw [mul_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [mul_one_div]

theorem lam_succ (K : ℕ) : lam (K + 1) = lam K + lamTerm K := by
  rw [lam_eq_sum, lam_eq_sum, sum_range_succ]

theorem lam_mono {K L : ℕ} (h : K ≤ L) : lam K ≤ lam L :=
  monotone_nat_of_le_succ (fun K => by rw [lam_succ]; linarith [lamTerm_pos K]) h

theorem lam_strictMono {K L : ℕ} (h : K < L) : lam K < lam L := by
  have := lam_mono (Nat.succ_le_of_lt h)
  rw [lam_succ] at this
  linarith [lamTerm_pos K]

theorem lam_one : lam 1 = 2 / 3 := by norm_num [lam]

theorem lam_four_gt : 2 / 3 < lam 4 := by rw [← lam_one]; exact lam_strictMono (by norm_num)

/-- `prf:windows`(c), first claim: `β_{n+1} - β_n > 2/3`. -/
theorem windows_c (n : ℕ) : 2 / 3 < betaN (n + 1) - betaN n := by
  unfold betaN
  have h1 : lam (n + 3) ≤ lam (n + 1 + 3) := lam_mono (by omega)
  have h2 : 2 / 3 < lam (n + 1 + 3) := lt_of_lt_of_le lam_four_gt (lam_mono (by omega))
  push_cast
  nlinarith [h1, h2, (Nat.cast_nonneg n : (0 : ℚ) ≤ n)]

/-- `prf:windows`(c), second claim: `β_1 - 1/1000 > 0`. -/
theorem windows_c' : 0 < betaN 1 - 1 / 1000 := by
  have : betaN 1 = lam 4 := by simp [betaN]
  rw [this]; linarith [lam_four_gt]

theorem betaN_mono {n m : ℕ} (h : n ≤ m) : betaN n ≤ betaN m := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => linarith [windows_c ‹_›]

theorem betaN_gap {n m : ℕ} (h : n < m) : betaN n + 2 / 3 < betaN m := by
  have := windows_c n
  have := betaN_mono (Nat.succ_le_of_lt h)
  linarith

/-- The intervals `J_n`, `n ≥ 1`, consist of positive numbers: `β_n - 1/1000 > 0`. -/
theorem betaN_sub_pos {n : ℕ} (hn : 1 ≤ n) : 0 < (betaN n : ℝ) - 1 / 1000 := by
  have h := betaN_mono hn
  have h' := windows_c'
  have : (0 : ℚ) < betaN n - 1 / 1000 := by linarith
  have h'' : ((0 : ℚ) : ℝ) < ((betaN n - 1 / 1000 : ℚ) : ℝ) := Rat.cast_lt.2 this
  push_cast at h''
  exact h''

/-- The intervals `J_n` are pairwise disjoint (`prf:windows`(c)). -/
theorem J_disjoint {n m : ℕ} (h : n < m) : Disjoint (J n) (J m) := by
  rw [Set.disjoint_left]
  intro x hn hm
  have hg : (betaN n : ℝ) + 2 / 3 < betaN m := by
    have h' : ((betaN n + 2 / 3 : ℚ) : ℝ) < ((betaN m : ℚ) : ℝ) := Rat.cast_lt.2 (betaN_gap h)
    push_cast at h'
    exact h'
  simp only [J, Set.mem_Ioo] at hn hm
  linarith [hn.2, hm.1]

/-- `β_n ∈ J_n`. -/
theorem betaN_mem_J (n : ℕ) : (betaN n : ℝ) ∈ J n := by
  simp only [J, Set.mem_Ioo]; constructor <;> linarith

/-! ## Part (a): the series for `log 2` -/

/-- The `j`-th term of the series for `log 2`, as a real number. -/
def logTerm (j : ℕ) : ℝ := 2 / ((2 * (j : ℝ) + 1) * 3 ^ (2 * j + 1))

theorem logTerm_pos (j : ℕ) : 0 < logTerm j := by unfold logTerm; positivity

theorem logTerm_eq_cast (j : ℕ) : logTerm j = (lamTerm j : ℝ) := by
  simp [logTerm, lamTerm]

/-- `log 2 = 2 ∑_{j ≥ 0} 1/((2j+1) 3^{2j+1})` (Mathlib's `hasSum_log_one_add_inv` at `a = 1`). -/
theorem hasSum_logTerm : HasSum logTerm (Real.log 2) := by
  have h := Real.hasSum_log_one_add_inv (a := 1) one_pos
  have e : (fun k : ℕ => (2 : ℝ) * (1 / (2 * k + 1)) * (1 / (2 * 1 + 1)) ^ (2 * k + 1)) =
      logTerm := by
    funext k
    simp only [logTerm]
    rw [div_pow, one_pow]
    norm_num
    field_simp
  rw [e] at h
  norm_num at h
  exact h

theorem lam_cast (K : ℕ) : (lam K : ℝ) = ∑ j ∈ range K, logTerm j := by
  rw [lam_eq_sum]; push_cast; simp [logTerm_eq_cast]

/-- `log 2 - λ_K` is the tail `∑_{i ≥ 0} t_{i+K}`. -/
theorem log_two_sub_lam (K : ℕ) : Real.log 2 - lam K = ∑' i, logTerm (i + K) := by
  rw [lam_cast, ← hasSum_logTerm.tsum_eq, ← hasSum_logTerm.summable.sum_add_tsum_nat_add K]
  ring

theorem logTerm_shift_le (K i : ℕ) : logTerm (i + K) ≤ logTerm K * (1 / 9) ^ i := by
  unfold logTerm
  have h3 : (3 : ℝ) ^ (2 * (i + K) + 1) = 3 ^ (2 * K + 1) * 9 ^ i := by
    rw [show 2 * (i + K) + 1 = (2 * K + 1) + 2 * i by ring, pow_add, pow_mul]; norm_num
  rw [h3, div_pow, one_pow]
  have hK : (2 * (K : ℝ) + 1) ≤ 2 * ((i + K : ℕ) : ℝ) + 1 := by push_cast; linarith [(i.cast_nonneg : (0 : ℝ) ≤ i)]
  rw [div_mul_div_comm, mul_one]
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_right hK (by positivity)

/-- `prf:windows`(a): `0 < log 2 - λ_K ≤ 3 / (4 (2K+1) 9^K)`. -/
theorem windows_a (K : ℕ) :
    0 < Real.log 2 - lam K ∧ Real.log 2 - lam K ≤ 3 / (4 * (2 * K + 1) * 9 ^ K) := by
  rw [log_two_sub_lam]
  have hs : Summable fun i => logTerm (i + K) :=
    (summable_nat_add_iff K).2 hasSum_logTerm.summable
  refine ⟨hs.tsum_pos (fun i => (logTerm_pos _).le) 0 (logTerm_pos _), ?_⟩
  have hg : Summable fun i : ℕ => logTerm K * (1 / 9 : ℝ) ^ i :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  calc ∑' i, logTerm (i + K) ≤ ∑' i : ℕ, logTerm K * (1 / 9 : ℝ) ^ i :=
        hs.tsum_le_tsum (logTerm_shift_le K) hg
    _ = logTerm K * (1 - 1 / 9)⁻¹ := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    _ = 3 / (4 * (2 * K + 1) * 9 ^ K) := by
        unfold logTerm
        rw [pow_succ, pow_mul]
        field_simp
        ring

/-! ## Part (b) -/

theorem nat_le_nine_pow (n : ℕ) (hn : 1 ≤ n) : (n : ℝ) * 9 ^ 4 ≤ 9 ^ (n + 3) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hb : (1 : ℝ) + m * 8 ≤ (1 + 8) ^ m := one_add_mul_le_pow (by norm_num) m
  have hm : (m : ℝ) + 1 ≤ 9 ^ m := by norm_num at hb; linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
  rw [show m + 1 + 3 = m + 4 by ring, pow_add]
  push_cast
  exact mul_le_mul_of_nonneg_right hm (by positivity)

/-- `prf:windows`(b): `0 < n log 2 - β_n ≤ 3/26244 < 1/1000` for `n ≥ 1`. -/
theorem windows_b (n : ℕ) (hn : 1 ≤ n) :
    0 < n * Real.log 2 - betaN n ∧ n * Real.log 2 - betaN n ≤ 3 / 26244 ∧
      (3 / 26244 : ℝ) < 1 / 1000 := by
  have hb : (n : ℝ) * Real.log 2 - betaN n = n * (Real.log 2 - lam (n + 3)) := by
    simp [betaN]; ring
  obtain ⟨ha1, ha2⟩ := windows_a (n + 3)
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  refine ⟨by rw [hb]; positivity, ?_, by norm_num⟩
  rw [hb]
  calc (n : ℝ) * (Real.log 2 - lam (n + 3))
      ≤ n * (3 / (4 * (2 * ((n + 3 : ℕ) : ℝ) + 1) * 9 ^ (n + 3))) :=
        mul_le_mul_of_nonneg_left ha2 (by positivity)
    _ ≤ n * (3 / (4 * 9 ^ (n + 3))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
        have : (1 : ℝ) ≤ 2 * ((n + 3 : ℕ) : ℝ) + 1 := by push_cast; linarith
        nlinarith [pow_pos (by norm_num : (0 : ℝ) < 9) (n + 3)]
    _ ≤ 3 / 26244 := by
        have h9 := nat_le_nine_pow n hn
        rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith [h9]

/-! ## Part (d) -/

/-- `prf:windows`(d): if `β ∈ J_n` with `n ≥ 1`, then `|β / log 2 - n| < 1/250`. -/
theorem windows_d {n : ℕ} (hn : 1 ≤ n) {β : ℝ} (hβ : β ∈ J n) :
    |β / Real.log 2 - n| < 1 / 250 := by
  obtain ⟨hb1, hb2, -⟩ := windows_b n hn
  simp only [J, Set.mem_Ioo] at hβ
  have hl : (1 / 2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlpos : (0 : ℝ) < Real.log 2 := by linarith
  have hdiff : |β - n * Real.log 2| < 2 / 1000 := by
    rw [abs_lt]; constructor <;> linarith
  have : β / Real.log 2 - n = (β - n * Real.log 2) / Real.log 2 := by field_simp
  rw [this, abs_div, abs_of_pos hlpos, div_lt_iff₀ hlpos]
  linarith

end UPD

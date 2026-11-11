/-
# The label passes and the input (proof of `bg:ready`, "Label")

New in this project (BLUEPRINT G.1, step (3), continued).

* `Reaches C k C'`: `C` reaches `C'` in `k` steps of `M` on the tape `ℕ` (`stepU`); composition
  `Reaches.trans` adds the times. Scans with a state sequence and a write, up (`scan_upX`) and
  down (`scan_downX`); the head moves at most one cell per step (`iterate_head_le`).
* The tape before the label pass `r` (`tapeL U d r m`): marks `𝗉 = 1` on the cells `2 + 2^r i`,
  `i < d / 2^r`, and `𝗇 = 1` on the cells `0, …, m - 1`. The parity of the marks below a cell
  (`parK_tapeL`: `⌈j / 2^r⌉ mod 2`, via `div_add_pred`).
* One pass (`label_pass`): it keeps the marks `2 + 2^{r+1} i` and ends at the marker cell in `H` of
  the parity of `d / 2^r`. Even case (`label_even`: `S₂, S₃, S₁` append a cell with `𝗇 = 1` and
  restart at cell `0`) and odd case (`label_odd`: `S₄, S₅, S₆` write `1^{r+1}` on the `𝗎`-track
  and enter `(q⁰_U, run)`), each in `2d + 2r + 10` steps.
* "Starting from `c = d ≥ 8`, the passes end after `v₂(d)` even passes and one odd pass, leaving
  `𝗇 = 1` exactly on the cells `0, …, n - 1`": `label_iter`, `load` (the label
  `n(d) = 1 + v₂(d)` is `label d`, with `v₂ = padicValNat 2`), at the explicit time `timeS d`.
-/
import UndecidablePhaseDiagram.Background.Run
import Mathlib.NumberTheory.Padics.PadicVal.Basic

set_option autoImplicit false

namespace UPD

namespace MachineM

variable {U : Machine}

/-- `C` reaches `C'` in `k` steps of `M` on the tape `ℕ`. -/
def Reaches (C : MCfg U) (k : ℕ) (C' : MCfg U) : Prop := (stepU)^[k] C = C'

theorem Reaches.trans {C C' C'' : MCfg U} {k k' : ℕ} (h : Reaches C k C')
    (h' : Reaches C' k' C'') : Reaches C (k + k') C'' := by
  unfold Reaches at *
  rw [add_comm, Function.iterate_add_apply, h, h']

theorem Reaches.one {C C' : MCfg U} (h : stepU C = C') : Reaches C 1 C' := h

theorem Reaches.zero (C : MCfg U) : Reaches C 0 C := rfl

theorem Reaches.congr_time {C C' : MCfg U} {k k' : ℕ} (h : Reaches C k C') (e : k = k') :
    Reaches C k' C' := e ▸ h

/-- Scanning up over the cells `a, …, a + k - 1` in the states `X 0, …, X k`, writing `w`. -/
theorem scan_upX (X : ℕ → StateM U) (w : TapeM U → TapeM U) (P : TapeM U → Prop)
    (t : ℕ → TapeM U) (a k : ℕ)
    (hX : ∀ s g, s < k → P g → deltaM U (X s) g = (X (s + 1), w g, .up))
    (hP : ∀ j, a ≤ j → j < a + k → P (t j)) :
    Reaches ⟨t, a, X 0⟩ k ⟨fun j => if a ≤ j ∧ j < a + k then w (t j) else t j, a + k, X k⟩ := by
  induction k with
  | zero =>
    have e : (fun j => if a ≤ j ∧ j < a + 0 then w (t j) else t j) = t := by
      funext j; rw [if_neg (by omega)]
    rw [e]; rfl
  | succ k ih =>
    unfold Reaches at *
    rw [Function.iterate_succ_apply', ih (fun s g hs hg => hX s g (by omega) hg)
      (fun j h1 h2 => hP j h1 (by omega))]
    have hd : deltaM U (X k) ((fun j => if a ≤ j ∧ j < a + k then w (t j) else t j) (a + k)) =
        (X (k + 1), w (t (a + k)), .up) := by
      dsimp only
      rw [if_neg (by omega)]
      exact hX k _ (by omega) (hP (a + k) (by omega) (by omega))
    rw [stepU_up hd]
    congr 1
    funext j
    by_cases hj : j = a + k
    · subst hj
      rw [Function.update_self, if_pos (by omega)]
    · rw [Function.update_of_ne hj]
      by_cases h1 : a ≤ j ∧ j < a + k
      · rw [if_pos h1, if_pos (by omega)]
      · rw [if_neg h1, if_neg (by omega)]

/-- Scanning down from cell `a + k` to cell `a` in the states `X 0, …, X k`, writing `w` on the
cells `a + k, …, a + 1`. -/
theorem scan_downX (X : ℕ → StateM U) (w : TapeM U → TapeM U) (P : TapeM U → Prop)
    (t : ℕ → TapeM U) (a k : ℕ)
    (hX : ∀ s g, s < k → P g → deltaM U (X s) g = (X (s + 1), w g, .down))
    (hP : ∀ j, a < j → j ≤ a + k → P (t j)) :
    Reaches ⟨t, a + k, X 0⟩ k ⟨fun j => if a < j ∧ j ≤ a + k then w (t j) else t j, a, X k⟩ := by
  induction k generalizing a with
  | zero =>
    have e : (fun j => if a < j ∧ j ≤ a + 0 then w (t j) else t j) = t := by
      funext j; rw [if_neg (by omega)]
    rw [e]; rfl
  | succ k ih =>
    have h1 := ih (a + 1) (fun s g hs hg => hX s g (by omega) hg)
      (fun j h1 h2 => hP j (by omega) (by omega))
    unfold Reaches at *
    rw [show a + (k + 1) = a + 1 + k by ring, Function.iterate_succ_apply', h1]
    have hd : deltaM U (X k)
        ((fun j => if a + 1 < j ∧ j ≤ a + 1 + k then w (t j) else t j) (a + 1)) =
        (X (k + 1), w (t (a + 1)), .down) := by
      dsimp only
      rw [if_neg (by omega)]
      exact hX k _ (by omega) (hP (a + 1) (by omega) (by omega))
    rw [stepU_down hd (by omega)]
    congr 1
    funext j
    by_cases hj : j = a + 1
    · subst hj
      rw [Function.update_self, if_pos (by omega)]
    · rw [Function.update_of_ne hj]
      by_cases h1 : a + 1 < j ∧ j ≤ a + 1 + k
      · rw [if_pos h1, if_pos (by omega)]
      · rw [if_neg h1, if_neg (by omega)]

/-- The head moves by at most one cell per step. -/
theorem stepU_head_le (c : MCfg U) : (stepU c).head ≤ c.head + 1 := by
  unfold stepU
  split
  · simp
  · simp
  · split
    · simp
    · simp; omega

/-- After `k` steps the head is at most `k` cells above where it started. -/
theorem iterate_head_le (c : MCfg U) (k : ℕ) : ((stepU)^[k] c).head ≤ c.head + k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have := stepU_head_le ((stepU)^[k] c)
    omega

/-! ## The label passes -/

/-- The tape before the label pass `r`: the marks `𝗉 = 1` on the cells `2 + 2^r i`, `i < d / 2^r`
(written `2 ≤ j < d + 2`, `2^r ∣ j - 2`), and `𝗇 = 1` on the cells `0, …, m - 1`. -/
def tapeL (U : Machine) (d r m : ℕ) : ℕ → TapeM U :=
  fun j => ⟨decide (j = d + 2), decide (j = 0), 0, decide (2 ≤ j ∧ j < d + 2 ∧ 2 ^ r ∣ j - 2),
    if j < m then 1 else 0, false, false⟩

theorem tapeL0_eq (d : ℕ) : tapeL0 U d = tapeL U d 0 1 := by
  funext j
  by_cases hj : j = 0
  · subst hj
    simp [tapeL0, tapeL, tapeP, tape0]
  · simp only [tapeL0]
    rw [Function.update_of_ne hj]
    simp [tapeL, tapeP, tape0, hj]

/-- `⌈m / q⌉ = ⌊m / q⌋ + [q ∤ m]`. -/
theorem div_add_pred (m q : ℕ) (hq : 0 < q) :
    (m + q - 1) / q = m / q + if q ∣ m then 0 else 1 := by
  have hm := Nat.div_add_mod m q
  have hb := Nat.mod_lt m hq
  have e : m + q - 1 = (m % q + q - 1) + q * (m / q) := by
    generalize q * (m / q) = A at hm ⊢
    omega
  rw [e, Nat.add_mul_div_left _ _ hq, add_comm]
  congr 1
  by_cases h : q ∣ m
  · rw [if_pos h, Nat.dvd_iff_mod_eq_zero.mp h]
    exact Nat.div_eq_of_lt (by omega)
  · rw [if_neg h]
    have h0 : m % q ≠ 0 := fun h0 => h (Nat.dvd_of_mod_eq_zero h0)
    exact Nat.div_eq_of_lt_le (by omega) (by omega)

/-- The parity of the marks below the cell `j + 2` before the pass `r`: `⌈j / 2^r⌉ mod 2`. -/
theorem parK_tapeL (d r m : ℕ) : ∀ j, j ≤ d →
    parK (tapeL U d r m) 0 (j + 2) = decide ((j + 2 ^ r - 1) / 2 ^ r % 2 = 1) := by
  have hq : 0 < 2 ^ r := by positivity
  intro j
  induction j with
  | zero =>
    intro _
    have : (0 + 2 ^ r - 1) / 2 ^ r = 0 := Nat.div_eq_of_lt (by omega)
    rw [this]
    simp [parK, tapeL]
  | succ j ih =>
    intro hj
    rw [show j + 1 + 2 = (j + 2) + 1 by ring, parK, ih (by omega)]
    have hp : (tapeL U d r m (0 + (j + 2))).p = decide (2 ^ r ∣ j) := by
      have h1 : 2 ≤ j + 2 ∧ j + 2 < d + 2 := ⟨by omega, by omega⟩
      simp [tapeL, h1]
    rw [hp, show j + 1 + 2 ^ r - 1 = j + 2 ^ r by omega, Nat.add_div_right _ hq,
      div_add_pred _ _ hq]
    generalize j / 2 ^ r = A
    by_cases h : 2 ^ r ∣ j
    · simp only [h, if_true, add_zero, decide_true, Bool.xor_true]
      by_cases hA : A % 2 = 1
      · have : ¬ (A + 1) % 2 = 1 := by omega
        simp [hA, this]
      · have : (A + 1) % 2 = 1 := by omega
        simp [hA, this]
    · simp only [h, if_false, decide_false, Bool.xor_false]

theorem dvd_pow_succ_iff {i r : ℕ} (h : 2 ^ r ∣ i) : 2 ^ (r + 1) ∣ i ↔ i / 2 ^ r % 2 = 0 := by
  obtain ⟨A, rfl⟩ := h
  rw [pow_succ, Nat.mul_div_cancel_left _ (by positivity),
    Nat.mul_dvd_mul_iff_left (by positivity), Nat.dvd_iff_mod_eq_zero]

/-- **Label pass** `r` (`2^r ∣ d`): a pass of `H₀, H₁` from cell `0` keeps the marks
`2 + 2^{r+1} i` and erases the others, and ends at the marker cell `d + 2` in `H` of the parity of
the number `d / 2^r` of marks. -/
theorem label_pass {d r : ℕ} (m : ℕ) (hr : 2 ^ r ∣ d) :
    Reaches ⟨tapeL U d r m, 0, .H false⟩ (d + 2)
      ⟨tapeL U d (r + 1) m, d + 2, .H (decide (d / 2 ^ r % 2 = 1))⟩ := by
  have hq : 0 < 2 ^ r := by positivity
  have hs := pass_scan (tapeL U d r m) 0 false (d + 2)
    (fun j _ h2 => by simp [tapeL]; omega)
  unfold Reaches
  rw [hs, zero_add]
  have hfin : parK (tapeL U d r m) 0 (d + 2) = decide (d / 2 ^ r % 2 = 1) := by
    rw [parK_tapeL d r m d le_rfl, div_add_pred d _ hq, if_pos hr, add_zero]
  rw [Bool.false_xor, hfin]
  congr 1
  funext j
  simp only [Bool.false_xor, Nat.sub_zero, Nat.zero_le, true_and]
  by_cases h2 : 2 ≤ j
  swap
  · have hp : (tapeL U d r m j).p = false := by simp [tapeL]; omega
    rw [if_neg (by simp [hp])]
    simp [tapeL, h2]
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 2 := ⟨j - 2, by omega⟩
  by_cases hi : i < d ∧ 2 ^ r ∣ i
  · obtain ⟨hi1, hi2⟩ := hi
    have hpar : parK (tapeL U d r m) 0 (i + 2) = decide (i / 2 ^ r % 2 = 1) := by
      rw [parK_tapeL d r m i hi1.le, div_add_pred _ _ hq, if_pos hi2, add_zero]
    have hp : (tapeL U d r m (i + 2)).p = true := by simp [tapeL, hi1, hi2]
    rw [hpar, hp, Bool.and_true]
    have hiff := dvd_pow_succ_iff hi2
    by_cases hodd : i / 2 ^ r % 2 = 1
    · rw [if_pos ⟨by omega, by simp [hodd]⟩]
      have hn : ¬ 2 ^ (r + 1) ∣ i := fun h => by have := hiff.1 h; omega
      simp [tapeL, hn]
    · rw [if_neg (fun h => hodd (by simpa using h.2))]
      have hy : 2 ^ (r + 1) ∣ i := hiff.2 (by omega)
      simp [tapeL, hy, hi1, hi2]
  · have hp : (tapeL U d r m (i + 2)).p = false := by
      simp only [tapeL, Nat.add_sub_cancel, decide_eq_false_iff_not]
      intro h; exact hi ⟨by omega, h.2.2⟩
    rw [if_neg (by simp [hp])]
    have hn : ¬ (i < d ∧ 2 ^ (r + 1) ∣ i) := fun h =>
      hi ⟨h.1, (pow_dvd_pow 2 (Nat.le_succ r)).trans h.2⟩
    simp only [tapeL, Nat.add_sub_cancel, TapeM.mk.injEq, true_and, and_true]
    simp only [decide_eq_decide]
    constructor
    · intro h; exact absurd ⟨by omega, h.2.2⟩ hi
    · intro h; exact absurd ⟨by omega, h.2.2⟩ hn

/-- `M` simulating the configuration `c` of `U` on the background tape `T` in the state `q`: the
`𝗎`-track is the tape of `c`, the head is the head of `c`. -/
def simCfg (T : ℕ → TapeM U) (c : U.Cfg) (q : StateM U) : MCfg U :=
  ⟨fun j => { T j with u := c.tape j }, c.head, q⟩

/-- **Label, even case** (`2^{r+1} ∣ d`): the pass `r` leaves `d / 2^{r+1}` marks, and `S₂, S₃,
S₁` append one cell with `𝗇 = 1` above the existing ones and start the next pass at cell `0`, in
`2d + 2r + 10` steps. -/
theorem label_even {d r : ℕ} (hr : 2 ^ (r + 1) ∣ d) :
    Reaches ⟨tapeL U d r (r + 1), 0, .H false⟩ (2 * d + 2 * r + 10)
      ⟨tapeL U d (r + 1) (r + 2), 0, .H false⟩ := by
  have hr' : 2 ^ r ∣ d := (pow_dvd_pow 2 (Nat.le_succ r)).trans hr
  have hpar : decide (d / 2 ^ r % 2 = 1) = false := by
    have := (dvd_pow_succ_iff hr').1 hr; simp [this]
  have h1 := label_pass (U := U) (r + 1) hr'
  rw [hpar] at h1
  have h2 : Reaches ⟨tapeL U d (r + 1) (r + 1), d + 2, .H false⟩ 1
      ⟨tapeL U d (r + 1) (r + 1), d + 2, .S2⟩ := by
    apply Reaches.one
    have hd : deltaM U (.H false) (tapeL U d (r + 1) (r + 1) (d + 2)) =
        (.S2, tapeL U d (r + 1) (r + 1) (d + 2), .stay) := by
      simp [deltaM, programM, tapeL]
    rw [stepU_stay hd, Function.update_eq_self]
  have h3 : Reaches ⟨tapeL U d (r + 1) (r + 1), d + 2, .S2⟩ (d + 2)
      ⟨tapeL U d (r + 1) (r + 1), 0, .S2⟩ := by
    have := scan_down .S2 (fun g hg => by simp [deltaM, programM, hg])
      (tapeL U d (r + 1) (r + 1)) 0 (d + 2) (fun j h1 _ => by simp [tapeL]; omega)
    rwa [zero_add] at this
  have h4 : Reaches ⟨tapeL U d (r + 1) (r + 1), 0, .S2⟩ 1
      ⟨tapeL U d (r + 1) (r + 1), 0, .S3⟩ := by
    apply Reaches.one
    have hd : deltaM U .S2 (tapeL U d (r + 1) (r + 1) 0) =
        (.S3, tapeL U d (r + 1) (r + 1) 0, .stay) := by
      simp [deltaM, programM, tapeL]
    rw [stepU_stay hd, Function.update_eq_self]
  have h5 : Reaches ⟨tapeL U d (r + 1) (r + 1), 0, .S3⟩ (r + 1)
      ⟨tapeL U d (r + 1) (r + 1), r + 1, .S3⟩ := by
    have := scan_up .S3 id (fun g => g.n = 1) (fun g hg => by simp [deltaM, programM, hg])
      (tapeL U d (r + 1) (r + 1)) 0 (r + 1) (fun j _ h2 => by simp [tapeL]; omega)
    unfold Reaches; rw [this]; simp
  have h6 : Reaches ⟨tapeL U d (r + 1) (r + 1), r + 1, .S3⟩ 1
      ⟨tapeL U d (r + 1) (r + 2), r + 1, .S1⟩ := by
    apply Reaches.one
    have hd : deltaM U .S3 (tapeL U d (r + 1) (r + 1) (r + 1)) =
        (.S1, { tapeL U d (r + 1) (r + 1) (r + 1) with n := 1 }, .stay) := by
      simp [deltaM, programM, tapeL]
    rw [stepU_stay hd]
    congr 1
    funext j
    by_cases hj : j = r + 1
    · subst hj; simp [tapeL]
    · rw [Function.update_of_ne hj]
      simp only [tapeL, TapeM.mk.injEq, true_and, and_true]
      have : j < r + 1 ↔ j < r + 2 := by omega
      simp [this]
  have h7 : Reaches ⟨tapeL U d (r + 1) (r + 2), r + 1, .S1⟩ (r + 1)
      ⟨tapeL U d (r + 1) (r + 2), 0, .S1⟩ := by
    have := scan_down .S1 (fun g hg => by simp [deltaM, programM, hg])
      (tapeL U d (r + 1) (r + 2)) 0 (r + 1) (fun j h1 _ => by simp [tapeL]; omega)
    rwa [zero_add] at this
  have h8 : Reaches ⟨tapeL U d (r + 1) (r + 2), 0, .S1⟩ 1
      ⟨tapeL U d (r + 1) (r + 2), 0, .H false⟩ := by
    apply Reaches.one
    have hd : deltaM U .S1 (tapeL U d (r + 1) (r + 2) 0) =
        (.H false, tapeL U d (r + 1) (r + 2) 0, .stay) := by
      simp [deltaM, programM, tapeL]
    rw [stepU_stay hd, Function.update_eq_self]
  exact ((((((h1.trans h2).trans h3).trans h4).trans h5).trans h6).trans h7).trans h8
    |>.congr_time (by ring)

/-- **Label, odd case** (`2^r ∣ d`, `2^{r+1} ∤ d`): after the pass `r`, `S₄, S₅, S₆` write the
symbol `1` on the `𝗎`-track of the cells `0, …, r` and return to cell `0` in `(q⁰_U, run)`, in
`2d + 2r + 10` steps: `M` now simulates `U` started on `1^{r+1}`. -/
theorem label_odd {d r : ℕ} (hr : 2 ^ r ∣ d) (hr1 : ¬ 2 ^ (r + 1) ∣ d) :
    Reaches ⟨tapeL U d r (r + 1), 0, .H false⟩ (2 * d + 2 * r + 10)
      (simCfg (tapeL U d (r + 1) (r + 1)) (U.start (r + 1)) (.run ⟨0, U.init_not_halting⟩)) := by
  have hpar : decide (d / 2 ^ r % 2 = 1) = true := by
    have : ¬ d / 2 ^ r % 2 = 0 := fun h => hr1 ((dvd_pow_succ_iff hr).2 h)
    simp; omega
  have h1 := label_pass (U := U) (r + 1) hr
  rw [hpar] at h1
  set t := tapeL U d (r + 1) (r + 1) with ht
  have h2 : Reaches ⟨t, d + 2, .H true⟩ 1 ⟨t, d + 2, .S4⟩ := by
    apply Reaches.one
    have hd : deltaM U (.H true) (t (d + 2)) = (.S4, t (d + 2), .stay) := by
      simp [deltaM, programM, t, tapeL]
    rw [stepU_stay hd, Function.update_eq_self]
  have h3 : Reaches ⟨t, d + 2, .S4⟩ (d + 2) ⟨t, 0, .S4⟩ := by
    have := scan_down .S4 (fun g hg => by simp [deltaM, programM, hg]) t 0 (d + 2)
      (fun j h1 _ => by simp [t, tapeL]; omega)
    rwa [zero_add] at this
  have h4 : Reaches ⟨t, 0, .S4⟩ 1 ⟨t, 0, .S5⟩ := by
    apply Reaches.one
    have hd : deltaM U .S4 (t 0) = (.S5, t 0, .stay) := by simp [deltaM, programM, t, tapeL]
    rw [stepU_stay hd, Function.update_eq_self]
  set t' : ℕ → TapeM U := fun j => { t j with u := (U.start (r + 1)).tape j } with ht'
  have h5 : Reaches ⟨t, 0, .S5⟩ (r + 1) ⟨t', r + 1, .S5⟩ := by
    have := scan_up .S5 (fun g => { g with u := 1 }) (fun g => g.n = 1)
      (fun g hg => by simp [deltaM, programM, hg]) t 0 (r + 1)
      (fun j _ h2 => by simp [t, tapeL]; omega)
    unfold Reaches; rw [this, zero_add]
    congr 1
    funext j
    by_cases hj : j < r + 1
    · simp [t', hj, Machine.start]; omega
    · simp [t', hj, Machine.start, t, tapeL]; omega
  have h6 : Reaches ⟨t', r + 1, .S5⟩ 1 ⟨t', r + 1, .S6⟩ := by
    apply Reaches.one
    have hd : deltaM U .S5 (t' (r + 1)) = (.S6, t' (r + 1), .stay) := by
      simp [deltaM, programM, t', t, tapeL]
    rw [stepU_stay hd, Function.update_eq_self]
  have h7 : Reaches ⟨t', r + 1, .S6⟩ (r + 1) ⟨t', 0, .S6⟩ := by
    have := scan_down .S6 (fun g hg => by simp [deltaM, programM, hg]) t' 0 (r + 1)
      (fun j h1 _ => by simp [t', t, tapeL]; omega)
    rwa [zero_add] at this
  have h8 : Reaches ⟨t', 0, .S6⟩ 1 ⟨t', 0, .run ⟨0, U.init_not_halting⟩⟩ := by
    apply Reaches.one
    have hd : deltaM U .S6 (t' 0) = (.run ⟨0, U.init_not_halting⟩, t' 0, .stay) := by
      simp [deltaM, programM, t', t, tapeL]
    rw [stepU_stay hd, Function.update_eq_self]
  exact ((((((h1.trans h2).trans h3).trans h4).trans h5).trans h6).trans h7).trans h8
    |>.congr_time (by ring)

/-- The time of the label phase: `T_L(d, 0) = 2d + 6` (the depth phase) and
`T_L(d, r + 1) = T_L(d, r) + 2d + 2r + 10`. -/
def timeL (d : ℕ) : ℕ → ℕ
  | 0 => 2 * d + 6
  | r + 1 => timeL d r + (2 * d + 2 * r + 10)

/-- "Label": after the depth phase and `r` even passes (`2^r ∣ d`), the head is at cell `0` in
`H₀`, with `d / 2^r` marks and `𝗇 = 1` exactly on the cells `0, …, r`. -/
theorem label_iter {d : ℕ} (hd : 8 ≤ d) : ∀ r, 2 ^ r ∣ d →
    Reaches (cfg0 U d) (timeL d r) ⟨tapeL U d r (r + 1), 0, .H false⟩
  | 0, _ => by rw [← tapeL0_eq]; exact depth_phase hd
  | r + 1, h => (label_iter hd r ((pow_dvd_pow 2 (Nat.le_succ r)).trans h)).trans (label_even h)

/-- The label `n(d) = 1 + v₂(d)`. -/
def label (d : ℕ) : ℕ := 1 + padicValNat 2 d

/-- The time at which the simulation of `U` starts. -/
def timeS (d : ℕ) : ℕ := timeL d (padicValNat 2 d) + (2 * d + 2 * padicValNat 2 d + 10)

/-- "Label" and the input: for `d ≥ 8`, after `timeS d` steps `M` is at cell `0` in
`(q⁰_U, run)` with `𝗇 = 1` exactly on the cells `0, …, n - 1` and the input `1^n` on the
`𝗎`-track, `n = n(d)`. -/
theorem load {d : ℕ} (hd : 8 ≤ d) :
    Reaches (cfg0 U d) (timeS d) (simCfg (tapeL U d (label d) (label d)) (U.start (label d))
      (.run ⟨0, U.init_not_halting⟩)) := by
  have hd0 : d ≠ 0 := by omega
  have h1 : 2 ^ padicValNat 2 d ∣ d := pow_padicValNat_dvd
  have h2 : ¬ 2 ^ (padicValNat 2 d + 1) ∣ d := pow_succ_padicValNat_not_dvd hd0
  rw [label, add_comm 1]
  exact (label_iter hd _ h1).trans (label_odd h1 h2)

end MachineM

end UPD

/-
# The run of `M` as iterates of one step (App. C, `mach:def-run`; `bg:ready`)

New in this project (BLUEPRINT G.1, step (2)).

* Configurations of `M` (`MCfg`: tape `ℕ → Γ_M`, head cell, state) and one step of `M`
  (`stepU`, on the tape `ℕ`, a move down from cell `0` gives `q_fail`); the step on the tape
  `[0, N)` (`stepB N`): a move up from cell `N - 1` gives `q_fail` without writing or moving.
* The column of a configuration on `[0, N)` (`colOf`: the tape, and the head as the state at one
  cell), and the paper's induction step after `mach:def-run`: `nextRow (colOf c) = colOf (stepB c)`
  (`nextRow_colOf`, from the one-head lemmas of `Background/Machine.lean`).
* **`mach:def-run`**: the run `runM U d i` (`c_0(j) = init([j = d+2], [j = 0])`,
  `c_{i+1} = f_M(c_i(j-1), c_i(j), c_i(j+1))`, `⊥` beyond both ends) on `N_d = 2^{d+2} - 2` cells,
  and the readiness `ρ_d` (`ready`: `c_{N-1}(0)` carries `q_acc`). `runM_eq`: `c_i` is the column
  of the `i`-th configuration of `M` on `[0, N_d)` started from `(init-tape, 0, P₀)`: "`(c_i)` is
  the run of `M` for `N - 1` steps on a tape of `N` cells, with an exit through either end counted
  as failure".
* Bounded and unbounded runs agree until the first exit (`stepB_iterate`); `q_fail` is absorbing.
* Phase lemmas (BLUEPRINT G.1, step (3)), on the tape `ℕ`: scans up in a fixed state with a write
  (`scan_up`) and down to cell `0` without writing (`scan_down`, the returns in `S₁, S₂, S₄, S₆,
  E₀, E₆`); "Depth" (`depth_loop`, `depth_S1`, `depth_fail`, `depth_phase`: after `2d + 6` steps
  the head is at cell `0` in `H₀`, with `𝗉 = 1` on `2, …, d+1` and `𝗇 = 1` at cell `0`; for
  `d ≤ 7` the run fails at step `d + 3`); one label pass (`pass_scan`: a pass in `H₀, H₁` keeps
  the first, third, … mark, erases the others, and ends in `H` of the parity of the marks).
* **`bg:ready`(a)**, first claim: `ρ_d = 1 ⇒ d ≥ 8` (`ready_ge_eight`).
-/
import UndecidablePhaseDiagram.Background.Machine

set_option autoImplicit false

namespace UPD

namespace MachineM

variable {U : Machine}

/-- A configuration of `M`: tape (cells `0, 1, 2, …`), head cell, state. -/
structure MCfg (U : Machine) where
  /-- the tape -/
  tape : ℕ → TapeM U
  /-- the head cell -/
  head : ℕ
  /-- the state -/
  state : StateM U

/-- One step of `M` on the tape `ℕ`: `δ_M(q, g) = (q', g', D)`; write `g'`, enter `q'`, move by
`D`; a move down from cell `0` gives `q_fail` without writing or moving. -/
def stepU (c : MCfg U) : MCfg U :=
  match (deltaM U c.state (c.tape c.head)).2.2 with
  | .stay => ⟨Function.update c.tape c.head (deltaM U c.state (c.tape c.head)).2.1, c.head,
      (deltaM U c.state (c.tape c.head)).1⟩
  | .up => ⟨Function.update c.tape c.head (deltaM U c.state (c.tape c.head)).2.1, c.head + 1,
      (deltaM U c.state (c.tape c.head)).1⟩
  | .down => if c.head = 0 then ⟨c.tape, c.head, .fail⟩ else
      ⟨Function.update c.tape c.head (deltaM U c.state (c.tape c.head)).2.1, c.head - 1,
        (deltaM U c.state (c.tape c.head)).1⟩

/-- One step of `M` on the tape `[0, N)`: as `stepU`, except that a move up from cell `N - 1`
gives `q_fail` without writing or moving. -/
def stepB (N : ℕ) (c : MCfg U) : MCfg U :=
  if (deltaM U c.state (c.tape c.head)).2.2 = .up ∧ N ≤ c.head + 1 then ⟨c.tape, c.head, .fail⟩
  else stepU c

/-- The column of a configuration on the cells `0, …, N - 1`: the tape, with the state at the head
cell and `·` elsewhere. -/
def colOf (N : ℕ) (c : MCfg U) : Fin N → CellM U :=
  fun i => (c.tape i, if i.val = c.head then some c.state else none)

theorem colOf_eq {N : ℕ} (c : MCfg U) (hc : c.head < N) :
    colOf N c = oneHead (fun i : Fin N => c.tape i) ⟨c.head, hc⟩ c.state := by
  funext i
  simp only [colOf, oneHead, Fin.ext_iff]

theorem update_restrict {N : ℕ} (t : ℕ → TapeM U) (h : ℕ) (hh : h < N) (g : TapeM U) :
    (fun i : Fin N => Function.update t h g i.val) =
      Function.update (fun i : Fin N => t i) ⟨h, hh⟩ g := by
  funext i
  by_cases hi : i.val = h
  · have : i = ⟨h, hh⟩ := Fin.ext hi
    subst this; simp
  · rw [Function.update_of_ne hi, Function.update_of_ne (fun h' => hi (by rw [h']))]

/-- The paper's induction step after `mach:def-run`: one step of the automaton on a column with one
head is one step of `M` on `[0, N)`, an exit through either end counted as failure. -/
theorem nextRow_colOf {N : ℕ} (c : MCfg U) (hc : c.head < N) :
    (stepB N c).head < N ∧ nextRow (colOf N c) = colOf N (stepB N c) := by
  obtain ⟨t, h, q⟩ := c
  simp only at hc
  rw [colOf_eq _ hc]
  rcases hD : (deltaM U q (t h)).2.2 with _ | _ | _
  · -- up
    by_cases hN : N ≤ h + 1
    · have hs : stepB N ⟨t, h, q⟩ = ⟨t, h, .fail⟩ := by simp [stepB, hD, hN]
      rw [hs]
      refine ⟨hc, ?_⟩
      rw [colOf_eq _ hc]
      exact nextRow_up_fail (fun i : Fin N => t i) ⟨h, hc⟩ q hD (by simp; omega)
    · have hh : h + 1 < N := by omega
      have hs : stepB N ⟨t, h, q⟩ =
          ⟨Function.update t h (deltaM U q (t h)).2.1, h + 1, (deltaM U q (t h)).1⟩ := by
        simp only [stepB, hD, true_and, if_neg hN, stepU]
      rw [hs]
      refine ⟨hh, ?_⟩
      rw [colOf_eq _ hh, update_restrict _ _ hc]
      exact nextRow_up (fun i : Fin N => t i) ⟨h, hc⟩ q hD hh
  · -- down
    by_cases h0 : h = 0
    · subst h0
      have hs : stepB N ⟨t, 0, q⟩ = ⟨t, 0, .fail⟩ := by simp [stepB, stepU, hD]
      rw [hs]
      refine ⟨hc, ?_⟩
      rw [colOf_eq _ hc]
      exact nextRow_down_fail (fun i : Fin N => t i) ⟨0, hc⟩ q hD rfl
    · have hs : stepB N ⟨t, h, q⟩ =
          ⟨Function.update t h (deltaM U q (t h)).2.1, h - 1, (deltaM U q (t h)).1⟩ := by
        simp [stepB, stepU, hD, h0]
      rw [hs]
      refine ⟨show h - 1 < N by omega, ?_⟩
      rw [colOf_eq _ (by omega : h - 1 < N), update_restrict _ _ hc]
      exact nextRow_down (fun i : Fin N => t i) ⟨h, hc⟩ q hD (by simp; omega)
  · -- stay
    have hs : stepB N ⟨t, h, q⟩ =
        ⟨Function.update t h (deltaM U q (t h)).2.1, h, (deltaM U q (t h)).1⟩ := by
      simp [stepB, stepU, hD]
    rw [hs]
    refine ⟨hc, ?_⟩
    rw [colOf_eq _ hc, update_restrict _ _ hc]
    exact nextRow_stay (fun i : Fin N => t i) ⟨h, hc⟩ q hD

/-- Iterating the induction step. -/
theorem nextRow_iterate {N : ℕ} (c : MCfg U) (hc : c.head < N) (i : ℕ) :
    ((stepB N)^[i] c).head < N ∧ nextRow^[i] (colOf N c) = colOf N ((stepB N)^[i] c) := by
  induction i with
  | zero => exact ⟨hc, rfl⟩
  | succ i ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih.2]
    exact nextRow_colOf _ ih.1

/-! ## `mach:def-run` -/

/-- `N_d = 2^{d+2} - 2`. -/
def Nd (d : ℕ) : ℕ := 2 ^ (d + 2) - 2

/-- The initial tape on the grid of depth `d`: `𝗁 = [j = d+2]`, `𝗓 = [j = 0]`, all other tracks
blank (`init`). -/
def tape0 (U : Machine) (d : ℕ) : ℕ → TapeM U :=
  fun j => ⟨decide (j = d + 2), decide (j = 0), 0, false, 0, false, false⟩

/-- The initial configuration: the tape `tape0`, the head at cell `0` in state `P₀`. -/
def cfg0 (U : Machine) (d : ℕ) : MCfg U := ⟨tape0 U d, 0, .P 0⟩

/-- **`mach:def-run`**: the run `c_i : [0, N) → 𝒮_M` of `M` on the grid of depth `d`,
`N = N_d`: `c_0(j) = init([j = d+2], [j = 0])`, `c_{i+1}(j) = f_M(c_i(j-1), c_i(j), c_i(j+1))`
with `c_i(-1) = c_i(N) = ⊥`. -/
def runM (U : Machine) (d i : ℕ) : Fin (Nd d) → CellM U :=
  nextRow^[i] (fun j => initM U (decide (j.val = d + 2)) (decide (j.val = 0)))

theorem two_le_Nd (d : ℕ) : 2 ≤ Nd d := by
  unfold Nd
  have : 4 ≤ 2 ^ (d + 2) := by
    rw [pow_add]; have := Nat.one_le_two_pow (n := d); omega
  omega

/-- `d + 2 < N_d - 1` for `d ≥ 1` (the paper after `mach:def-run`: `d + 2 < N_d`). -/
theorem add_four_le_Nd {d : ℕ} (hd : 1 ≤ d) : d + 4 ≤ Nd d := by
  unfold Nd
  have : d + 6 ≤ 2 ^ (d + 2) := by
    induction d, hd using Nat.le_induction with
    | base => norm_num
    | succ d _ ih => rw [pow_succ]; omega
  omega

/-- The paper after `mach:def-run`: `c_0` has one head, at cell `0` in state `P₀`, and `c_i` is
the column of the `i`-th configuration of `M` on the tape `[0, N_d)`. -/
theorem runM_eq (U : Machine) (d i : ℕ) :
    runM U d i = colOf (Nd d) ((stepB (Nd d))^[i] (cfg0 U d)) := by
  have h0 : (fun j : Fin (Nd d) => initM U (decide (j.val = d + 2)) (decide (j.val = 0))) =
      colOf (Nd d) (cfg0 U d) := by
    funext j
    simp only [initM, colOf, cfg0, tape0]
    by_cases hj : j.val = 0 <;> simp [hj]
  rw [runM, h0]
  exact (nextRow_iterate (cfg0 U d) (by simp [cfg0]; have := two_le_Nd d; omega) i).2

/-- The readiness `ρ_d`: the last column `c_{N-1}` carries `q_acc` at cell `0`. -/
def ready (U : Machine) (d : ℕ) : Prop :=
  (runM U d (Nd d - 1) ⟨0, by have := two_le_Nd d; omega⟩).2 = some .acc

/-! ## Bounded and unbounded runs -/

theorem stepB_of_not_exit {N : ℕ} {c : MCfg U}
    (h : ¬ ((deltaM U c.state (c.tape c.head)).2.2 = .up ∧ N ≤ c.head + 1)) :
    stepB N c = stepU c := by
  simp only [stepB, if_neg h]

/-- `q_fail` is absorbing. -/
theorem stepB_fail {N : ℕ} (t : ℕ → TapeM U) (h : ℕ) :
    stepB N ⟨t, h, .fail⟩ = ⟨t, h, .fail⟩ := by
  have hd : deltaM U .fail (t h) = (.fail, t h, .stay) := by simp [deltaM, programM]
  simp [stepB, stepU, hd]

theorem stepB_iterate_fail {N : ℕ} (t : ℕ → TapeM U) (h k : ℕ) :
    (stepB N)^[k] ⟨t, h, .fail⟩ = ⟨t, h, .fail⟩ := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih, stepB_fail]

/-- Bounded and unbounded runs agree until the first exit: after `k` steps the bounded run is the
unbounded one, or it is in `q_fail`. -/
theorem stepB_iterate (N : ℕ) (c : MCfg U) (k : ℕ) :
    (stepB N)^[k] c = (stepU)^[k] c ∨ ((stepB N)^[k] c).state = .fail := by
  induction k with
  | zero => exact Or.inl rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    rcases ih with h | h
    · rw [h]
      by_cases hx : (deltaM U ((stepU)^[k] c).state (((stepU)^[k] c).tape
          ((stepU)^[k] c).head)).2.2 = .up ∧ N ≤ ((stepU)^[k] c).head + 1
      · right; simp [stepB, hx]
      · left; exact stepB_of_not_exit hx
    · right
      generalize (stepB N)^[k] c = c' at h ⊢
      obtain ⟨t, hh, q⟩ := c'
      simp only at h
      subst h
      rw [stepB_fail]

/-! ## Single steps and scans -/

theorem stepU_up {t : ℕ → TapeM U} {h : ℕ} {q q' : StateM U} {g' : TapeM U}
    (hd : deltaM U q (t h) = (q', g', .up)) :
    stepU ⟨t, h, q⟩ = ⟨Function.update t h g', h + 1, q'⟩ := by
  simp [stepU, hd]

theorem stepU_stay {t : ℕ → TapeM U} {h : ℕ} {q q' : StateM U} {g' : TapeM U}
    (hd : deltaM U q (t h) = (q', g', .stay)) :
    stepU ⟨t, h, q⟩ = ⟨Function.update t h g', h, q'⟩ := by
  simp [stepU, hd]

theorem stepU_down {t : ℕ → TapeM U} {h : ℕ} {q q' : StateM U} {g' : TapeM U}
    (hd : deltaM U q (t h) = (q', g', .down)) (h0 : h ≠ 0) :
    stepU ⟨t, h, q⟩ = ⟨Function.update t h g', h - 1, q'⟩ := by
  simp [stepU, hd, h0]

/-- `q_fail` is absorbing for `stepU`. -/
theorem stepU_fail (t : ℕ → TapeM U) (h : ℕ) : stepU ⟨t, h, .fail⟩ = ⟨t, h, .fail⟩ := by
  have hd : deltaM U .fail (t h) = (.fail, t h, .stay) := by simp [deltaM, programM]
  rw [stepU_stay hd, Function.update_eq_self]

theorem stepU_iterate_fail (t : ℕ → TapeM U) (h k : ℕ) :
    (stepU)^[k] ⟨t, h, .fail⟩ = ⟨t, h, .fail⟩ := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih, stepU_fail]

/-- Scanning up in a fixed state `X` over the cells `a, …, a + k - 1`, each satisfying `P`, writing
`w` on each. -/
theorem scan_up (X : StateM U) (w : TapeM U → TapeM U) (P : TapeM U → Prop)
    (hX : ∀ g, P g → deltaM U X g = (X, w g, .up)) (t : ℕ → TapeM U) (a k : ℕ)
    (hP : ∀ j, a ≤ j → j < a + k → P (t j)) :
    (stepU)^[k] ⟨t, a, X⟩ =
      ⟨fun j => if a ≤ j ∧ j < a + k then w (t j) else t j, a + k, X⟩ := by
  induction k with
  | zero =>
    have e : (fun j => if a ≤ j ∧ j < a + 0 then w (t j) else t j) = t := by
      funext j; rw [if_neg (by omega)]
    rw [e]; rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih (fun j h1 h2 => hP j h1 (by omega))]
    have hd : deltaM U X ((fun j => if a ≤ j ∧ j < a + k then w (t j) else t j) (a + k)) =
        (X, w (t (a + k)), .up) := by
      dsimp only
      rw [if_neg (by omega)]
      exact hX _ (hP (a + k) (by omega) (by omega))
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

/-- Scanning down in a fixed state `X` (`𝗓 = 0 ↦` move down, no write) from cell `a + k` to cell
`a`. -/
theorem scan_down (X : StateM U) (hX : ∀ g : TapeM U, g.z = false → deltaM U X g = (X, g, .down))
    (t : ℕ → TapeM U) (a k : ℕ) (hz : ∀ j, a < j → j ≤ a + k → (t j).z = false) :
    (stepU)^[k] ⟨t, a + k, X⟩ = ⟨t, a, X⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply,
      stepU_down (hX _ (hz (a + (k + 1)) (by omega) le_rfl)) (by omega),
      Function.update_eq_self, show a + (k + 1) - 1 = a + k by omega]
    exact ih (fun j h1 h2 => hz j h1 (by omega))

/-! ## The depth phase (proof of `bg:ready`, "Depth") -/

/-- The tape during the depth phase: `𝗉 = 1` on the cells `2, …, j - 1`. -/
def tapeP (U : Machine) (d j : ℕ) : ℕ → TapeM U :=
  fun i => { tape0 U d i with p := decide (2 ≤ i ∧ i < j) }

theorem tapeP_z (d j i : ℕ) : (tapeP U d j i).z = decide (i = 0) := rfl

theorem tapeP_h (d j i : ℕ) : (tapeP U d j i).h = decide (i = d + 2) := rfl

theorem deltaM_P_h0 (k : Fin 11) (g : TapeM U) (hg : g.h = false) :
    deltaM U (.P k) g = (.P ⟨min (k.val + 1) 10, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩,
      (if 2 ≤ k.val then { g with p := true } else g), .up) := by
  simp [deltaM, programM, hg]

/-- "Depth": in state `P_k` the head is at cell `k` while `k < 10`, and at a cell at least `10` in
state `P_{10}`; it moves up, marking `𝗉 = 1` at the cells `2, …, d + 1`. -/
theorem depth_loop (d : ℕ) {j : ℕ} (hj : j ≤ d + 2) :
    (stepU)^[j] (cfg0 U d) = ⟨tapeP U d j, j, .P ⟨min j 10, by omega⟩⟩ := by
  induction j with
  | zero =>
    simp only [Function.iterate_zero, id, cfg0]
    congr 1
    funext i
    simp [tapeP, tape0]
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih (by omega)]
    have hh : (tapeP U d j j).h = false := by rw [tapeP_h]; simp; omega
    rw [stepU_up (deltaM_P_h0 _ _ hh)]
    congr 1
    · funext i
      by_cases hi : i = j
      · subst hi
        rw [Function.update_self]
        by_cases h2 : 2 ≤ i
        · rw [if_pos (by simp; omega)]; simp [tapeP, h2]
        · rw [if_neg (by simp; omega)]; simp [tapeP, h2]
      · rw [Function.update_of_ne hi]
        simp only [tapeP]
        congr 1
        simp only [decide_eq_decide]
        omega
    · congr 1
      ext
      simp
      omega

/-- "Depth", end: at cell `d + 2` (`𝗁 = 1`) the head enters `S₁` if `d ≥ 8`. -/
theorem depth_S1 {d : ℕ} (hd : 8 ≤ d) :
    (stepU)^[d + 3] (cfg0 U d) = ⟨tapeP U d (d + 2), d + 2, .S1⟩ := by
  rw [Function.iterate_succ_apply', depth_loop d le_rfl]
  have hh : (tapeP U d (d + 2) (d + 2)).h = true := by rw [tapeP_h]; simp
  have hd' : deltaM U (.P ⟨min (d + 2) 10, by omega⟩) (tapeP U d (d + 2) (d + 2)) =
      (.S1, tapeP U d (d + 2) (d + 2), .stay) := by
    have hk : ¬ (min (d + 2) 10 ≤ 9) := by omega
    simp [deltaM, programM, hh, hk]
  rw [stepU_stay hd', Function.update_eq_self]

/-- "Depth": if `d + 2 ≤ 9`, that is `d ≤ 7`, the head fails at cell `d + 2`. -/
theorem depth_fail {d : ℕ} (hd : d ≤ 7) :
    (stepU)^[d + 3] (cfg0 U d) = ⟨tapeP U d (d + 2), d + 2, .fail⟩ := by
  rw [Function.iterate_succ_apply', depth_loop d le_rfl]
  have hh : (tapeP U d (d + 2) (d + 2)).h = true := by rw [tapeP_h]; simp
  have hd' : deltaM U (.P ⟨min (d + 2) 10, by omega⟩) (tapeP U d (d + 2) (d + 2)) =
      (.fail, tapeP U d (d + 2) (d + 2), .stay) := by
    have hk : min (d + 2) 10 ≤ 9 := by omega
    simp [deltaM, programM, hh, hk]
  rw [stepU_stay hd', Function.update_eq_self]

/-- The tape at the start of the first label pass: the depth marks, and `𝗇 = 1` at cell `0`. -/
def tapeL0 (U : Machine) (d : ℕ) : ℕ → TapeM U :=
  Function.update (tapeP U d (d + 2)) 0 { tapeP U d (d + 2) 0 with n := 1 }

/-- "Depth", end: `S₁` returns to cell `0`, writes `𝗇 = 1` there and enters `H₀`, after `2d + 6`
steps in all. -/
theorem depth_phase {d : ℕ} (hd : 8 ≤ d) :
    (stepU)^[2 * d + 6] (cfg0 U d) = ⟨tapeL0 U d, 0, .H false⟩ := by
  have hS1 : ∀ g : TapeM U, g.z = false → deltaM U .S1 g = (.S1, g, .down) := by
    intro g hg; simp [deltaM, programM, hg]
  have hs := scan_down .S1 hS1 (tapeP U d (d + 2)) 0 (d + 2)
    (fun j h1 _ => by rw [tapeP_z]; simp; omega)
  rw [zero_add] at hs
  rw [show 2 * d + 6 = 1 + ((d + 2) + (d + 3)) by ring, Function.iterate_add_apply,
    Function.iterate_add_apply, depth_S1 hd, hs]
  have hz : (tapeP U d (d + 2) 0).z = true := by rw [tapeP_z]; simp
  have hd' : deltaM U .S1 (tapeP U d (d + 2) 0) =
      (.H false, { tapeP U d (d + 2) 0 with n := 1 }, .stay) := by
    simp [deltaM, programM, hz]
  simp only [Function.iterate_one]
  rw [stepU_stay hd']
  rfl

/-- "Depth": for `d ≤ 7` the run is in `q_fail` from step `d + 3` on. -/
theorem depth_fail_forever {d : ℕ} (hd : d ≤ 7) {k : ℕ} (hk : d + 3 ≤ k) :
    ((stepU)^[k] (cfg0 U d)).state = .fail := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [add_comm, Function.iterate_add_apply, depth_fail hd, stepU_iterate_fail]

/-- **`bg:ready`(a)**, first claim: if `ρ_d = 1` (`d ≥ 1`), then `d ≥ 8`. -/
theorem ready_ge_eight {d : ℕ} (hd1 : 1 ≤ d) (h : ready U d) : 8 ≤ d := by
  by_contra hlt
  push Not at hlt
  have hN : d + 3 ≤ Nd d - 1 := by have := add_four_le_Nd hd1; omega
  have hfail : ((stepB (Nd d))^[Nd d - 1] (cfg0 U d)).state = .fail := by
    rcases stepB_iterate (Nd d) (cfg0 U d) (Nd d - 1) with e | e
    · rw [e]; exact depth_fail_forever (by omega) hN
    · exact e
  unfold ready at h
  rw [runM_eq] at h
  simp only [colOf] at h
  split_ifs at h with h0
  · rw [hfail] at h; simp at h

/-! ## A label pass (proof of `bg:ready`, "Label") -/

/-- The parity of the marks `𝗉 = 1` on the cells `a, …, a + k - 1`. -/
def parK (t : ℕ → TapeM U) (a : ℕ) : ℕ → Bool
  | 0 => false
  | k + 1 => xor (parK t a k) (t (a + k)).p

/-- `H_π` on a cell with `𝗁 = 0`: keep the mark if `π = 0` and erase it if `π = 1`; the parity
flips at each mark. -/
theorem deltaM_H (π : Bool) (g : TapeM U) (hg : g.h = false) :
    deltaM U (.H π) g = (.H (xor π g.p), (if π && g.p then { g with p := false } else g), .up) := by
  cases π <;> cases hp : g.p <;> simp [deltaM, programM, hg, hp]

/-- "Label": a pass in the states `H₀, H₁` over the cells `a, …, a + k - 1` (none of them the
marker cell) keeps the first, third, … mark and erases the second, fourth, … (counted from the
parity `π`), and ends in `H_{π ⊕ (number of marks mod 2)}`. -/
theorem pass_scan (t : ℕ → TapeM U) (a : ℕ) (π : Bool) (k : ℕ)
    (hh : ∀ j, a ≤ j → j < a + k → (t j).h = false) :
    (stepU)^[k] ⟨t, a, .H π⟩ =
      ⟨fun j => if a ≤ j ∧ j < a + k ∧ (xor π (parK t a (j - a)) && (t j).p) = true then
          { t j with p := false } else t j, a + k, .H (xor π (parK t a k))⟩ := by
  induction k with
  | zero =>
    have e : (fun j => if a ≤ j ∧ j < a + 0 ∧ (xor π (parK t a (j - a)) && (t j).p) = true then
        { t j with p := false } else t j) = t := by
      funext j; rw [if_neg (by omega)]
    rw [e]; simp [parK]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih (fun j h1 h2 => hh j h1 (by omega))]
    have hd : deltaM U (.H (xor π (parK t a k)))
        ((fun j => if a ≤ j ∧ j < a + k ∧ (xor π (parK t a (j - a)) && (t j).p) = true then
          { t j with p := false } else t j) (a + k)) =
        (.H (xor (xor π (parK t a k)) (t (a + k)).p),
          (if (xor π (parK t a k) && (t (a + k)).p) = true then { t (a + k) with p := false }
            else t (a + k)), .up) := by
      dsimp only
      rw [if_neg (by omega)]
      exact deltaM_H _ _ (hh (a + k) (by omega) (by omega))
    rw [stepU_up hd]
    congr 1
    · funext j
      by_cases hj : j = a + k
      · subst hj
        rw [Function.update_self]
        simp only [Nat.add_sub_cancel_left]
        by_cases hc : (xor π (parK t a k) && (t (a + k)).p) = true
        · rw [if_pos hc, if_pos ⟨by omega, by omega, hc⟩]
        · rw [if_neg hc, if_neg (fun h => hc h.2.2)]
      · rw [Function.update_of_ne hj]
        dsimp only
        have hiff : (a ≤ j ∧ j < a + k ∧ (xor π (parK t a (j - a)) && (t j).p) = true) ↔
            (a ≤ j ∧ j < a + (k + 1) ∧ (xor π (parK t a (j - a)) && (t j).p) = true) := by
          constructor
          · rintro ⟨h1, h2, h3⟩; exact ⟨h1, by omega, h3⟩
          · rintro ⟨h1, h2, h3⟩; exact ⟨h1, by omega, h3⟩
        by_cases hc : a ≤ j ∧ j < a + k ∧ (xor π (parK t a (j - a)) && (t j).p) = true
        · rw [if_pos hc, if_pos (hiff.1 hc)]
        · rw [if_neg hc, if_neg (fun h => hc (hiff.2 h))]
    · simp only [parK, Bool.xor_assoc]

end MachineM

end UPD

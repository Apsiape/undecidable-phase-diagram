/-
# The simulation, the masks, and the readiness lemma (`bg:ready`)

New in this project (BLUEPRINT G.1, steps (3) and (4)).

* "Simulation" (`sim_step`, `sim_step_none`, `sim_run`): from `(q⁰_U, run)` with the input on the
  `𝗎`-track, each step of `M` is one step of `U` on the `𝗎`-track (`simCfg`), until `U` enters a
  halting state, when `M` enters `E₀`; a move left from cell `0` gives `q_fail` on both sides.
  `sim_not_halts`: if `U` does not halt on `n`, `M` never reaches `q_acc`; `sim_firstHalt`: at the
  first halting time `M` is in `E₀`.
* "Masks": `E₀` returns (`E0_return`); a round (`mask_round`, `40ρ + 41` steps) consumes the
  lowest cell with `𝗇 = 1` and extends both masks by `20` cells; after `n` rounds (`mask_rounds`)
  `E₃, E₄` set `𝗆⁺ = 1` on `20n, …, 20n + 4` (`mask_end1`: the head reaches the cell `20n + 4`),
  `E₅` clears `𝗆⁻` on `20n - 5, …, 20n - 1` and `E₆` returns (`mask_end2`), and enters `q_acc`
  (`mask_acc`), which is absorbing (`acc_after`).
* `run_acc`: the whole run when `U` halts, with explicit times.
* **`bg:ready`(a)** (`ready_a`) and **(b)** (`ready_b`). [gap] 6 of `STATUS.md`: (b) uses crude
  bounds instead of the paper's step count: for fixed `n` the time to reach `q_acc` is at most
  `(2n + 2) d + K` (`K` depending on `n` and on the first halt of `U`), and the head never exceeds
  the elapsed time, so the run stays on the tape once this time is below `N_d - 1 = 2^{d+2} - 3`
  (`eventually_lin_lt`).
-/
import UndecidablePhaseDiagram.Background.Label

set_option autoImplicit false

namespace UPD

namespace MachineM

variable {U : Machine}

/-! ## The simulation -/

/-- The state of `M` after a simulated step of `U` into the configuration `c`: `(q, run)` for a
non-halting state `q` of `c`, and `E₀` for a halting one. -/
def simState (c : U.Cfg) : StateM U :=
  if h : U.halting c.state = true then .E0 else .run ⟨c.state, by simpa using h⟩

theorem simState_start (n : ℕ) : simState (U.start n) = .run ⟨0, U.init_not_halting⟩ := by
  simp [simState, Machine.start, U.init_not_halting]

theorem simState_of_not_halting {c : U.Cfg} (hq : U.halting c.state = false) :
    simState c = .run ⟨c.state, hq⟩ := by
  simp [simState, hq]

theorem simState_of_halting {c : U.Cfg} (hq : U.halting c.state = true) : simState c = .E0 := by
  simp [simState, hq]

/-- **Simulation**, one step: in the state `(q, run)`, one step of `M` is one step of `U` on the
`𝗎`-track (`δ_U(q, γ) = (q', γ', D)`: write `γ'`, move by `D`, enter `(q', run)`, or `E₀` if `q'`
halts). -/
theorem sim_step (T : ℕ → TapeM U) (hz : ∀ j, (T j).z = decide (j = 0)) (c c' : U.Cfg)
    (hq : U.halting c.state = false) (hs : U.step c = some c') :
    stepU (simCfg T c (.run ⟨c.state, hq⟩)) = simCfg T c' (simState c') := by
  obtain ⟨q, h, tp⟩ := c
  simp only at hq
  simp only [Machine.step] at hs
  rcases hD : (U.trans q (tp h)).2.2 with _ | _
  · rw [hD] at hs
    by_cases h0 : h = 0
    · simp [h0] at hs
    · simp only [Bool.false_eq_true, if_false, h0, Option.some.injEq] at hs
      subst hs
      have hd : deltaM U (.run ⟨q, hq⟩) { T h with u := tp h } =
          (simState ⟨(U.trans q (tp h)).1, h - 1, Function.update tp h (U.trans q (tp h)).2.1⟩,
            { T h with u := (U.trans q (tp h)).2.1 }, .down) := by
        simp [deltaM, programM, hD, hz, h0, simState]
      simp only [simCfg]
      rw [stepU_down hd h0]
      congr 1
      funext j
      by_cases hj : j = h
      · subst hj; simp
      · simp [Function.update_of_ne hj]
  · rw [hD] at hs
    simp only [if_true, Option.some.injEq] at hs
    subst hs
    have hd : deltaM U (.run ⟨q, hq⟩) { T h with u := tp h } =
        (simState ⟨(U.trans q (tp h)).1, h + 1, Function.update tp h (U.trans q (tp h)).2.1⟩,
          { T h with u := (U.trans q (tp h)).2.1 }, .up) := by
      simp [deltaM, programM, hD, simState]
    simp only [simCfg]
    rw [stepU_up hd]
    congr 1
    funext j
    by_cases hj : j = h
    · subst hj; simp
    · simp [Function.update_of_ne hj]

/-- **Simulation**, a move left from cell `0`: `U` stops without halting (`Machine.step` gives
`none`) and `M` enters `q_fail` (the `𝗓 = 1` rule of `δ_M`). -/
theorem sim_step_none (T : ℕ → TapeM U) (hz : ∀ j, (T j).z = decide (j = 0)) (c : U.Cfg)
    (hq : U.halting c.state = false) (hs : U.step c = none) :
    (stepU (simCfg T c (.run ⟨c.state, hq⟩))).state = .fail := by
  obtain ⟨q, h, tp⟩ := c
  simp only at hq
  simp only [Machine.step] at hs
  rcases hD : (U.trans q (tp h)).2.2 with _ | _
  · rw [hD] at hs
    by_cases h0 : h = 0
    · subst h0
      have hd : deltaM U (.run ⟨q, hq⟩) { T 0 with u := tp 0 } =
          (.fail, { T 0 with u := tp 0 }, .stay) := by
        simp [deltaM, programM, hD, hz]
      simp only [simCfg]
      rw [stepU_stay hd]
    · simp [h0] at hs
  · rw [hD] at hs
    simp at hs

/-- **Simulation**: started at `(q⁰_U, run)` with the input of `U` on the `𝗎`-track, as long as
`U` has not halted before time `s`, after `s` steps `M` simulates `U.run n s`, or both have
stopped (`U` by a move left from cell `0`, `M` in `q_fail`). -/
theorem sim_run (T : ℕ → TapeM U) (hz : ∀ j, (T j).z = decide (j = 0)) (n : ℕ) : ∀ s,
    (∀ s' < s, ∀ c, U.run n s' = some c → U.halting c.state = false) →
    (∃ c, U.run n s = some c ∧
      Reaches (simCfg T (U.start n) (.run ⟨0, U.init_not_halting⟩)) s
        (simCfg T c (simState c))) ∨
    (U.run n s = none ∧
      ((stepU)^[s] (simCfg T (U.start n) (.run ⟨0, U.init_not_halting⟩))).state = .fail)
  | 0, _ => Or.inl ⟨U.start n, rfl, by rw [simState_start]; rfl⟩
  | s + 1, h => by
    rcases sim_run T hz n s (fun s' hs' => h s' (by omega)) with ⟨c, hc, hr⟩ | ⟨hc, hf⟩
    · have hq : U.halting c.state = false := h s (by omega) c hc
      rw [simState_of_not_halting hq] at hr
      cases hs : U.step c with
      | none =>
        right
        refine ⟨by simp [Machine.run, hc, hs], ?_⟩
        unfold Reaches at hr
        rw [Function.iterate_succ_apply', hr]
        exact sim_step_none T hz c hq hs
      | some c' =>
        left
        refine ⟨c', by simp [Machine.run, hc, hs], ?_⟩
        unfold Reaches at hr ⊢
        rw [Function.iterate_succ_apply', hr]
        exact sim_step T hz c c' hq hs
    · right
      refine ⟨by simp [Machine.run, hc], ?_⟩
      rw [Function.iterate_succ_apply']
      generalize (stepU)^[s] (simCfg T (U.start n) (.run ⟨0, U.init_not_halting⟩)) = C at hf ⊢
      obtain ⟨t, hh, q⟩ := C
      simp only at hf
      subst hf
      rw [stepU_fail]

/-- **Simulation**: "If `U` does not halt on `n`, `M` never leaves the states `(q, run)` and
`q_fail`"; in particular it never reaches `q_acc`. -/
theorem sim_not_halts (T : ℕ → TapeM U) (hz : ∀ j, (T j).z = decide (j = 0)) {n : ℕ}
    (hn : ¬ U.HaltsOn n) (s : ℕ) :
    ((stepU)^[s] (simCfg T (U.start n) (.run ⟨0, U.init_not_halting⟩))).state ≠ .acc := by
  have hno : ∀ s' c, U.run n s' = some c → U.halting c.state = false := by
    intro s' c hc
    by_contra hh
    exact hn ⟨s', c, hc, by simpa using hh⟩
  rcases sim_run T hz n s (fun s' _ c hc => hno s' c hc) with ⟨c, hc, hr⟩ | ⟨_, hf⟩
  · unfold Reaches at hr
    rw [hr]
    simp [simCfg, simState_of_not_halting (hno s c hc)]
  · rw [hf]; simp

/-- **Simulation**: if `U` halts on `n`, at its first halting time `t` (configuration `c`) `M`
enters `E₀`, with the tape of `c` on the `𝗎`-track and the head at the head of `c`. -/
theorem sim_halts (T : ℕ → TapeM U) (hz : ∀ j, (T j).z = decide (j = 0)) {n : ℕ}
    (hn : U.HaltsOn n) : ∃ (t : ℕ) (c : U.Cfg), U.run n t = some c ∧ U.halting c.state = true ∧
      Reaches (simCfg T (U.start n) (.run ⟨0, U.init_not_halting⟩)) t (simCfg T c .E0) := by
  classical
  let t := Nat.find hn
  obtain ⟨c, hc, hh⟩ := Nat.find_spec hn
  have hmin : ∀ s' < t, ∀ c', U.run n s' = some c' → U.halting c'.state = false := by
    intro s' hs' c' hc'
    by_contra hh'
    exact Nat.find_min hn hs' ⟨c', hc', by simpa using hh'⟩
  refine ⟨t, c, hc, hh, ?_⟩
  rcases sim_run T hz n t hmin with ⟨c', hc', hr⟩ | ⟨hc', _⟩
  · rw [hc] at hc'
    cases hc'
    rwa [simState_of_halting hh] at hr
  · rw [hc] at hc'; cases hc'

/-! ## The masks -/

theorem Reaches.of_eq {C C' D D' : MCfg U} {k : ℕ} (h : Reaches C k C') (hC : C = D)
    (hC' : C' = D') : Reaches D k D' := hC ▸ hC' ▸ h

/-- Equality of tape symbols, track by track. -/
theorem tapeM_ext {g g' : TapeM U} (h1 : g.h = g'.h) (h2 : g.z = g'.z) (h3 : g.u = g'.u)
    (h4 : g.p = g'.p) (h5 : g.n = g'.n) (h6 : g.mm = g'.mm) (h7 : g.mp = g'.mp) : g = g' := by
  cases g; cases g'; simp_all

/-- `E₀` returns to cell `0` and enters `E₁`. -/
theorem E0_return (B : ℕ → TapeM U) (hz : ∀ j, (B j).z = decide (j = 0)) (h : ℕ) :
    Reaches ⟨B, h, .E0⟩ (h + 1) ⟨B, 0, .E1⟩ := by
  have h1 : Reaches ⟨B, h, .E0⟩ h ⟨B, 0, .E0⟩ := by
    have := scan_down .E0 (fun g hg => by simp [deltaM, programM, hg]) B 0 h
      (fun j h1 _ => by rw [hz]; simp; omega)
    rwa [zero_add] at this
  have h2 : Reaches ⟨B, 0, .E0⟩ 1 ⟨B, 0, .E1⟩ := by
    apply Reaches.one
    have hd : deltaM U .E0 (B 0) = (.E1, B 0, .stay) := by simp [deltaM, programM, hz]
    rw [stepU_stay hd, Function.update_eq_self]
  exact h1.trans h2

/-- The tape during the mask rounds: `𝗇 = 2` on the cells `0, …, ρ - 1`, `𝗇 = 1` on `ρ, …, n - 1`,
`𝗇 = 0` above, and `𝗆⁻ = 𝗆⁺ = 1` exactly on `0, …, 20ρ - 1`. -/
def tapeE (B : ℕ → TapeM U) (n ρ : ℕ) : ℕ → TapeM U :=
  fun j => { B j with
    n := (if j < ρ then 2 else if j < n then 1 else 0)
    mm := decide (j < 20 * ρ)
    mp := decide (j < 20 * ρ) }

/-- **Mask round** `ρ < n`: `E₁` consumes the lowest cell with `𝗇 = 1` (cell `ρ`), setting it to
`2`; `E₂^{(20)}, …, E₂^{(1)}` extend both masks by the `20` cells `20ρ, …, 20ρ + 19`; `E₀` returns
to cell `0`; `40ρ + 41` steps. -/
theorem mask_round (B : ℕ → TapeM U) (hz : ∀ j, (B j).z = decide (j = 0)) {n ρ : ℕ}
    (hρ : ρ < n) :
    Reaches ⟨tapeE B n ρ, 0, .E1⟩ (40 * ρ + 41) ⟨tapeE B n (ρ + 1), 0, .E1⟩ := by
  set t := tapeE B n ρ with ht
  have h1 : Reaches ⟨t, 0, .E1⟩ ρ ⟨t, ρ, .E1⟩ := by
    have := scan_up .E1 id (fun g => g.n = 2) (fun g hg => by simp [deltaM, programM, hg]) t 0 ρ
      (fun j _ h2 => by simp [t, tapeE]; omega)
    unfold Reaches; rw [this]; simp
  set t1 := Function.update t ρ { t ρ with n := 2 } with ht1
  have h2 : Reaches ⟨t, ρ, .E1⟩ 1 ⟨t1, ρ, .E2 19⟩ := by
    apply Reaches.one
    have hd : deltaM U .E1 (t ρ) = (.E2 19, { t ρ with n := 2 }, .stay) := by
      have : (t ρ).n = 1 := by simp [t, tapeE, hρ]
      simp [deltaM, programM, this]
    rw [stepU_stay hd]
  have h3 : Reaches ⟨t1, ρ, .E2 19⟩ (19 * ρ) ⟨t1, 20 * ρ, .E2 19⟩ := by
    have := scan_up (.E2 19) id (fun g => g.mm = true)
      (fun g hg => by simp [deltaM, programM, hg]) t1 ρ (19 * ρ)
      (fun j h1 h2 => by
        by_cases hj : j = ρ
        · subst hj; simp [t1, t, tapeE]; omega
        · simp [t1, t, tapeE, Function.update_of_ne hj]; omega)
    unfold Reaches; rw [this, show ρ + 19 * ρ = 20 * ρ by ring]; simp
  set t2 : ℕ → TapeM U := fun j =>
    if 20 * ρ ≤ j ∧ j < 20 * ρ + 19 then { t1 j with mm := true, mp := true } else t1 j
    with ht2
  have h4 : Reaches ⟨t1, 20 * ρ, .E2 19⟩ 19 ⟨t2, 20 * ρ + 19, .E2 0⟩ := by
    have := scan_upX (fun s => .E2 ⟨19 - s, by omega⟩) (fun g => { g with mm := true, mp := true })
      (fun g => g.mm = false)
      t1 (20 * ρ) 19
      (fun s g hs hg => by
        have h1 : 1 ≤ 19 - s := by omega
        have h2 : (⟨19 - s - 1, by omega⟩ : Fin 20) = ⟨19 - (s + 1), by omega⟩ := by
          ext; simp; omega
        simp [deltaM, programM, hg, h1, h2])
      (fun j h1 h2 => by
        by_cases hj : j = ρ
        · subst hj; simp [t1, t, tapeE]; omega
        · simp [t1, t, tapeE, Function.update_of_ne hj]; omega)
    exact this
  set t3 := Function.update t2 (20 * ρ + 19) { t2 (20 * ρ + 19) with mm := true, mp := true }
    with ht3
  have h5 : Reaches ⟨t2, 20 * ρ + 19, .E2 0⟩ 1 ⟨t3, 20 * ρ + 19, .E0⟩ := by
    apply Reaches.one
    have hm : (t2 (20 * ρ + 19)).mm = false := by
      have hj : 20 * ρ + 19 ≠ ρ := by omega
      simp [t2, t1, t, tapeE, Function.update_of_ne hj]
    have hd : deltaM U (.E2 0) (t2 (20 * ρ + 19)) =
        (.E0, { t2 (20 * ρ + 19) with mm := true, mp := true }, .stay) := by
      simp [deltaM, programM, hm]
    rw [stepU_stay hd]
  have ht3' : t3 = tapeE B n (ρ + 1) := by
    funext j
    apply tapeM_ext <;> simp only [t3, t2, t1, t, tapeE, Function.update_apply] <;>
      split_ifs <;> subst_vars <;> simp <;> omega
  have h6 : Reaches ⟨t3, 20 * ρ + 19, .E0⟩ (20 * ρ + 19 + 1) ⟨t3, 0, .E1⟩ :=
    E0_return t3 (by intro j; rw [ht3']; simp [tapeE, hz]) _
  rw [← ht3']
  exact (((((h1.trans h2).trans h3).trans h4).trans h5).trans h6).congr_time (by ring)

/-- The time of the first `ρ` mask rounds. -/
def timeR : ℕ → ℕ
  | 0 => 0
  | ρ + 1 => timeR ρ + (40 * ρ + 41)

/-- "After `n` rounds `E₁` reaches the cell `n`, where `𝗇 = 0`, and `𝗆⁻ = 𝗆⁺ = 1` exactly on the
cells `0, …, 20n - 1`." -/
theorem mask_rounds (B : ℕ → TapeM U) (hz : ∀ j, (B j).z = decide (j = 0)) (n : ℕ) :
    ∀ ρ, ρ ≤ n → Reaches ⟨tapeE B n 0, 0, .E1⟩ (timeR ρ) ⟨tapeE B n ρ, 0, .E1⟩
  | 0, _ => Reaches.zero _
  | ρ + 1, h => (mask_rounds B hz n ρ (by omega)).trans (mask_round B hz (by omega))

/-- The tape when the head reaches the cell `20n + 4` (in `E₄^{(1)}`). -/
def tapeG (B : ℕ → TapeM U) (n : ℕ) : ℕ → TapeM U :=
  fun j => { B j with
    n := (if j < n then 2 else 0)
    mm := decide (j < 20 * n)
    mp := decide (j < 20 * n + 4) }

/-- The final tape: `𝗆⁻ = 1` exactly on `j < 20n - 5`, `𝗆⁺ = 1` exactly on `j < 20n + 5`. -/
def tapeF (B : ℕ → TapeM U) (n : ℕ) : ℕ → TapeM U :=
  fun j => { B j with
    n := (if j < n then 2 else 0)
    mm := decide (j < 20 * n - 5)
    mp := decide (j < 20 * n + 5) }

/-- "Then `E₃` and `E₄` set `𝗆⁺ = 1` on the cells `20n, …`": after `20n + 5` steps the head is at
the cell `20n + 4` in `E₄^{(1)}`. -/
theorem mask_end1 (B : ℕ → TapeM U) (n : ℕ) :
    Reaches ⟨tapeE B n n, 0, .E1⟩ (20 * n + 5) ⟨tapeG B n, 20 * n + 4, .E4 0⟩ := by
  set t := tapeE B n n with ht
  have h1 : Reaches ⟨t, 0, .E1⟩ n ⟨t, n, .E1⟩ := by
    have := scan_up .E1 id (fun g => g.n = 2) (fun g hg => by simp [deltaM, programM, hg]) t 0 n
      (fun j _ h2 => by simp [t, tapeE]; omega)
    unfold Reaches; rw [this]; simp
  have h2 : Reaches ⟨t, n, .E1⟩ 1 ⟨t, n, .E3⟩ := by
    apply Reaches.one
    have hd : deltaM U .E1 (t n) = (.E3, t n, .stay) := by
      have : (t n).n = 0 := by simp [t, tapeE]
      simp [deltaM, programM, this]
    rw [stepU_stay hd, Function.update_eq_self]
  have h3 : Reaches ⟨t, n, .E3⟩ (19 * n) ⟨t, 20 * n, .E3⟩ := by
    have := scan_up .E3 id (fun g => g.mp = true) (fun g hg => by simp [deltaM, programM, hg])
      t n (19 * n) (fun j h1 h2 => by simp [t, tapeE]; omega)
    unfold Reaches; rw [this, show n + 19 * n = 20 * n by ring]; simp
  have h4 : Reaches ⟨t, 20 * n, .E3⟩ 4 ⟨tapeG B n, 20 * n + 4, .E4 0⟩ := by
    have := scan_upX (fun s => if h : s = 0 then .E3 else .E4 ⟨4 - s, by omega⟩)
      (fun g => { g with mp := true }) (fun g => g.mp = false) t (20 * n) 4
      (fun s g hs hg => by
        rcases (show s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 by omega) with rfl | rfl | rfl | rfl <;>
          simp [deltaM, programM, hg])
      (fun j h1 h2 => by simp [t, tapeE]; omega)
    refine Reaches.of_eq this rfl ?_
    congr 1
    funext j
    apply tapeM_ext <;> simp only [t, tapeE, tapeG] <;> split_ifs <;> simp <;> omega
  exact (((h1.trans h2).trans h3).trans h4).congr_time (by ring)

/-- "`E₅` clears `𝗆⁻` on the cells `20n - 5, …, 20n - 1`, and `E₆` returns to cell `0`": from the
cell `20n + 4` in `E₄^{(1)}`, after `20n + 5` steps the head is at cell `0` in `E₆` (`n ≥ 1`). -/
theorem mask_end2 (B : ℕ → TapeM U) (hz : ∀ j, (B j).z = decide (j = 0)) {n : ℕ} (hn : 1 ≤ n) :
    Reaches ⟨tapeG B n, 20 * n + 4, .E4 0⟩ (20 * n + 5) ⟨tapeF B n, 0, .E6⟩ := by
  set t1 := Function.update (tapeG B n) (20 * n + 4) { tapeG B n (20 * n + 4) with mp := true }
    with ht1
  have h1 : Reaches ⟨tapeG B n, 20 * n + 4, .E4 0⟩ 1 ⟨t1, 20 * n + 3, .E5 4⟩ := by
    apply Reaches.one
    have hd : deltaM U (.E4 0) (tapeG B n (20 * n + 4)) =
        (.E5 4, { tapeG B n (20 * n + 4) with mp := true }, .down) := by
      have : (tapeG B n (20 * n + 4)).z = false := by simp [tapeG, hz]
      simp [deltaM, programM, this]
    rw [stepU_down hd (by omega), show 20 * n + 4 - 1 = 20 * n + 3 by omega]
  have h2 : Reaches ⟨t1, 20 * n + 3, .E5 4⟩ 4 ⟨t1, 20 * n - 1, .E5 4⟩ := by
    have := scan_downX (fun _ => .E5 4) id (fun g => g.mm = false ∧ g.z = false) t1 (20 * n - 1) 4
      (fun s g hs hg => by simp [deltaM, programM, hg.1, hg.2])
      (fun j h1 h2 => by
        have hj : j ≠ 20 * n + 4 := by omega
        simp [t1, tapeG, hz, Function.update_of_ne hj]; omega)
    refine Reaches.of_eq this (by congr 1; omega) ?_
    congr 1
    funext j
    simp
  set t2 : ℕ → TapeM U := fun j =>
    if 20 * n - 5 < j ∧ j ≤ 20 * n - 5 + 4 then { t1 j with mm := false } else t1 j
    with ht2
  have h3 : Reaches ⟨t1, 20 * n - 1, .E5 4⟩ 4 ⟨t2, 20 * n - 5, .E5 0⟩ := by
    have := scan_downX (fun s => .E5 ⟨4 - s, by omega⟩) (fun g => { g with mm := false })
      (fun g => g.mm = true ∧ g.z = false) t1 (20 * n - 5) 4
      (fun s g hs hg => by
        rcases (show s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 by omega) with rfl | rfl | rfl | rfl <;>
          simp [deltaM, programM, hg.1, hg.2])
      (fun j h1 h2 => by
        have hj : j ≠ 20 * n + 4 := by omega
        simp [t1, tapeG, hz, Function.update_of_ne hj]; omega)
    exact Reaches.of_eq this (by congr 1; omega) rfl
  set t3 := Function.update t2 (20 * n - 5) { t2 (20 * n - 5) with mm := false } with ht3
  have h4 : Reaches ⟨t2, 20 * n - 5, .E5 0⟩ 1 ⟨t3, 20 * n - 5, .E6⟩ := by
    apply Reaches.one
    have hm : (t2 (20 * n - 5)).mm = true := by
      have hj : 20 * n - 5 ≠ 20 * n + 4 := by omega
      simp [t2, t1, tapeG, Function.update_of_ne hj]; omega
    have hd : deltaM U (.E5 0) (t2 (20 * n - 5)) =
        (.E6, { t2 (20 * n - 5) with mm := false }, .stay) := by
      simp [deltaM, programM, hm]
    rw [stepU_stay hd]
  have ht3' : t3 = tapeF B n := by
    funext j
    apply tapeM_ext <;> simp only [t3, t2, t1, tapeG, tapeF, Function.update_apply] <;>
      split_ifs <;> subst_vars <;> simp <;> omega
  have h5 : Reaches ⟨t3, 20 * n - 5, .E6⟩ (20 * n - 5) ⟨t3, 0, .E6⟩ := by
    have := scan_down .E6 (fun g hg => by simp [deltaM, programM, hg]) t3 0 (20 * n - 5)
      (fun j h1 _ => by rw [ht3']; simp [tapeF, hz]; omega)
    rwa [zero_add] at this
  rw [← ht3']
  exact ((((h1.trans h2).trans h3).trans h4).trans h5).congr_time (by omega)

/-- "`E₆` … enters the absorbing state `q_acc`." -/
theorem mask_acc (B : ℕ → TapeM U) (hz : ∀ j, (B j).z = decide (j = 0)) (n : ℕ) :
    Reaches ⟨tapeF B n, 0, .E6⟩ 1 ⟨tapeF B n, 0, .acc⟩ := by
  apply Reaches.one
  have hd : deltaM U .E6 (tapeF B n 0) = (.acc, tapeF B n 0, .stay) := by
    simp [deltaM, programM, tapeF, hz]
  rw [stepU_stay hd, Function.update_eq_self]

/-- `q_acc` is absorbing for `stepU`. -/
theorem stepU_acc (t : ℕ → TapeM U) (h : ℕ) : stepU ⟨t, h, .acc⟩ = ⟨t, h, .acc⟩ := by
  have hd : deltaM U .acc (t h) = (.acc, t h, .stay) := by simp [deltaM, programM]
  rw [stepU_stay hd, Function.update_eq_self]

theorem stepU_iterate_acc (t : ℕ → TapeM U) (h k : ℕ) :
    (stepU)^[k] ⟨t, h, .acc⟩ = ⟨t, h, .acc⟩ := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih, stepU_acc]

/-! ## The whole run, `bg:ready` (a) and (b) -/

/-- `(t, c)` is the first halting time of `U` on `n` and its configuration. -/
def FirstHalt (U : Machine) (n t : ℕ) (c : U.Cfg) : Prop :=
  U.run n t = some c ∧ U.halting c.state = true ∧
    ∀ s' < t, ∀ c', U.run n s' = some c' → U.halting c'.state = false

theorem exists_firstHalt {n : ℕ} (h : U.HaltsOn n) : ∃ t c, FirstHalt U n t c := by
  classical
  obtain ⟨c, hc, hh⟩ := Nat.find_spec h
  refine ⟨Nat.find h, c, hc, hh, fun s' hs' c' hc' => ?_⟩
  by_contra hh'
  exact Nat.find_min h hs' ⟨c', hc', by simpa using hh'⟩

/-- **Simulation** up to the first halt: `M` enters `E₀` with the tape of `c` on the `𝗎`-track. -/
theorem sim_firstHalt (T : ℕ → TapeM U) (hz : ∀ j, (T j).z = decide (j = 0)) {n t : ℕ}
    {c : U.Cfg} (hf : FirstHalt U n t c) :
    Reaches (simCfg T (U.start n) (.run ⟨0, U.init_not_halting⟩)) t (simCfg T c .E0) := by
  rcases sim_run T hz n t hf.2.2 with ⟨c', hc', hr⟩ | ⟨hc', _⟩
  · rw [hf.1] at hc'
    cases hc'
    rwa [simState_of_halting hf.2.1] at hr
  · rw [hf.1] at hc'; cases hc'

/-- The tape during the masks: the background of the label phase with the final tape of `U`
(configuration `c`) on the `𝗎`-track. -/
def tapeB (U : Machine) (d : ℕ) (c : U.Cfg) : ℕ → TapeM U :=
  fun j => { tapeL U d (label d) (label d) j with u := c.tape j }

theorem tapeB_z (d : ℕ) (c : U.Cfg) (j : ℕ) : (tapeB U d c j).z = decide (j = 0) := rfl

/-- The time at which the head reaches the cell `20n + 4` (in `E₄^{(1)}`), for the first halt at
time `t` with the head at `h`. -/
def time4 (d t h : ℕ) : ℕ := timeS d + t + (h + 1) + timeR (label d) + (20 * label d + 5)

/-- **The run of `M` when `U` halts** (`d ≥ 8`, first halt `(t, c)` of `U` on `n(d)`): the head
reaches the cell `20n + 4` at time `time4`, enters `E₆` at cell `0` with the final masks
`20n + 5` steps later, and `q_acc` one step after that. -/
theorem run_acc {d t : ℕ} {c : U.Cfg} (hd : 8 ≤ d) (hf : FirstHalt U (label d) t c) :
    Reaches (cfg0 U d) (time4 d t c.head)
      ⟨tapeG (tapeB U d c) (label d), 20 * label d + 4, .E4 0⟩ ∧
    Reaches (cfg0 U d) (time4 d t c.head + (20 * label d + 5))
      ⟨tapeF (tapeB U d c) (label d), 0, .E6⟩ ∧
    Reaches (cfg0 U d) (time4 d t c.head + (20 * label d + 5) + 1)
      ⟨tapeF (tapeB U d c) (label d), 0, .acc⟩ := by
  have hzT : ∀ j, (tapeL U d (label d) (label d) j).z = decide (j = 0) := fun j => rfl
  have hzB : ∀ j, (tapeB U d c j).z = decide (j = 0) := tapeB_z d c
  have hn1 : 1 ≤ label d := by unfold label; omega
  have h1 := (load (U := U) hd).trans (sim_firstHalt _ hzT hf)
  have h2 := E0_return (tapeB U d c) hzB c.head
  have hB : tapeE (tapeB U d c) (label d) 0 = tapeB U d c := by
    funext j
    apply tapeM_ext <;> simp [tapeE, tapeB, tapeL]
  have h3 := mask_rounds (tapeB U d c) hzB (label d) (label d) le_rfl
  rw [hB] at h3
  have h4 := mask_end1 (tapeB U d c) (label d)
  have h5 := mask_end2 (tapeB U d c) hzB hn1
  have h6 := mask_acc (tapeB U d c) hzB (label d)
  have e4 : Reaches (cfg0 U d) (time4 d t c.head)
      ⟨tapeG (tapeB U d c) (label d), 20 * label d + 4, .E4 0⟩ :=
    (((h1.trans h2).trans h3).trans h4)
  exact ⟨e4, e4.trans h5, (e4.trans h5).trans h6⟩

/-- `q_acc` is absorbing: once the run is in `q_acc`, it stays in the same configuration. -/
theorem acc_after {c : MCfg U} {K : ℕ} (hK : ((stepU)^[K] c).state = .acc) :
    ∀ K', K ≤ K' → (stepU)^[K'] c = (stepU)^[K] c := by
  intro K' hK'
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hK'
  rw [add_comm, Function.iterate_add_apply]
  generalize (stepU)^[K] c = C at hK ⊢
  obtain ⟨t, h, q⟩ := C
  simp only at hK
  subst hK
  exact stepU_iterate_acc t h m

/-- Bounded and unbounded runs agree while the bounded run has not failed. -/
theorem stepB_eq_stepU_of_le {N K k : ℕ} {c : MCfg U}
    (hK : ((stepB N)^[K] c).state ≠ .fail) (hk : k ≤ K) : (stepB N)^[k] c = (stepU)^[k] c := by
  rcases stepB_iterate N c k with e | e
  · exact e
  · exfalso
    apply hK
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
    rw [add_comm, Function.iterate_add_apply]
    generalize (stepB N)^[k] c = C at e ⊢
    obtain ⟨t, h, q⟩ := C
    simp only at e
    subst e
    rw [stepB_iterate_fail]

/-- Bounded and unbounded runs agree as long as the unbounded head stays below the cell `N - 1`. -/
theorem stepB_eq_of_head {N : ℕ} (c : MCfg U) :
    ∀ K, (∀ k < K, ((stepU)^[k] c).head + 1 < N) → (stepB N)^[K] c = (stepU)^[K] c
  | 0, _ => rfl
  | K + 1, h => by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      stepB_eq_of_head c K (fun k hk => h k (by omega))]
    apply stepB_of_not_exit
    have := h K (by omega)
    omega

/-- The readiness bit read off a configuration: `c_{N-1}(0)` carries `q_acc` iff the head is at
cell `0` in `q_acc`. -/
theorem colOf_zero_acc {N : ℕ} (C : MCfg U) (h0 : 0 < N) :
    (colOf N C ⟨0, h0⟩).2 = some .acc ↔ C.head = 0 ∧ C.state = .acc := by
  simp only [colOf]
  constructor
  · intro h
    split_ifs at h with h1
    · simp at h; exact ⟨h1.symm, h⟩
  · rintro ⟨h1, h2⟩
    simp [h1, h2]

/-- **`bg:ready`(a).** If `ρ_d = 1` (`d ≥ 1`), then `d ≥ 8`, `U` halts on `n(d)`, and
`𝗆⁻(c_{N-1}(j)) = [j < 20n(d) - 5]`, `𝗆⁺(c_{N-1}(j)) = [j < 20n(d) + 5]` for all `j ∈ [0, N)`;
moreover `20n(d) + 5 ≤ N_d`. -/
theorem ready_a {d : ℕ} (hd1 : 1 ≤ d) (h : ready U d) :
    8 ≤ d ∧ U.HaltsOn (label d) ∧
    (∀ j : Fin (Nd d), maskMinus U (runM U d (Nd d - 1) j) = decide (j.val < 20 * label d - 5) ∧
      maskPlus U (runM U d (Nd d - 1) j) = decide (j.val < 20 * label d + 5)) ∧
    20 * label d + 5 ≤ Nd d := by
  have hd8 := ready_ge_eight hd1 h
  have hN := two_le_Nd d
  set K := Nd d - 1 with hKdef
  unfold ready at h
  rw [runM_eq, colOf_zero_acc] at h
  obtain ⟨hC0, hCacc⟩ := h
  -- the bounded run did not fail, so it is the unbounded run
  have hCU : (stepB (Nd d))^[K] (cfg0 U d) = (stepU)^[K] (cfg0 U d) :=
    stepB_eq_stepU_of_le (by rw [hCacc]; simp) le_rfl
  have hUacc : ((stepU)^[K] (cfg0 U d)).state = .acc := by rw [← hCU]; exact hCacc
  -- `U` halts on `n(d)`
  have hhalt : U.HaltsOn (label d) := by
    by_contra hn
    have h1 := acc_after hUacc (timeS d + K) (by omega)
    have h2 := sim_not_halts (tapeL U d (label d) (label d)) (fun j => rfl) hn K
    have hl := load (U := U) hd8
    unfold Reaches at hl
    rw [← hl, ← Function.iterate_add_apply, add_comm, h1] at h2
    exact h2 hUacc
  refine ⟨hd8, hhalt, ?_⟩
  obtain ⟨t, c, hf⟩ := exists_firstHalt hhalt
  obtain ⟨e4, e6, eacc⟩ := run_acc hd8 hf
  -- the run reaches `q_acc` no later than the last column
  have hAK : time4 d t c.head + (20 * label d + 5) + 1 ≤ K := by
    by_contra hlt
    have h1 := acc_after hUacc (time4 d t c.head + (20 * label d + 5)) (by omega)
    unfold Reaches at e6
    rw [e6] at h1
    have := congrArg MCfg.state h1
    rw [hUacc] at this
    simp at this
  have hfinal : (stepU)^[K] (cfg0 U d) = ⟨tapeF (tapeB U d c) (label d), 0, .acc⟩ := by
    have h1 := acc_after (c := cfg0 U d)
      (K := time4 d t c.head + (20 * label d + 5) + 1) (by unfold Reaches at eacc; rw [eacc]) K hAK
    unfold Reaches at eacc
    rw [h1, eacc]
  refine ⟨fun j => ?_, ?_⟩
  · rw [runM_eq, hCU, hfinal]
    simp [maskMinus, maskPlus, colOf, tapeF]
  · -- the head visited the cell `20n + 4` without leaving the tape
    have hle : time4 d t c.head ≤ K := by omega
    have hB := stepB_eq_stepU_of_le (N := Nd d) (by rw [hCacc]; simp) hle
    have hh := (nextRow_iterate (N := Nd d) (cfg0 U d) (by simp [cfg0]; omega)
      (time4 d t c.head)).1
    rw [hB] at hh
    unfold Reaches at e4
    rw [e4] at hh
    simp only at hh
    omega

/-- A linear function is eventually below `2^d`: `B (m + 4B) < 2^{m + 4B}`. -/
theorem lin_lt_two_pow (B : ℕ) : ∀ m, B * (m + 4 * B) < 2 ^ (m + 4 * B)
  | 0 => by
    rw [zero_add]
    rcases Nat.eq_zero_or_pos B with h | h
    · subst h; simp
    · have h1 : B < 2 ^ B := Nat.lt_two_pow_self
      have h2 : 2 ≤ 2 ^ B := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ B := Nat.pow_le_pow_right (by norm_num) h
      have h3 : 2 ^ (4 * B) = 2 ^ B * 2 ^ B * (2 ^ B * 2 ^ B) := by
        rw [show 4 * B = B + B + (B + B) by ring, pow_add, pow_add]
      rw [h3]
      generalize 2 ^ B = X at h1 h2
      have h4 : B * B < X * X := Nat.mul_lt_mul'' h1 h1
      have h5 : 4 ≤ X * X := by nlinarith
      calc B * (4 * B) = 4 * (B * B) := by ring
        _ < 4 * (X * X) := by omega
        _ ≤ X * X * (X * X) := Nat.mul_le_mul_right _ h5
  | m + 1 => by
    have ih := lin_lt_two_pow B m
    have h1 : B < 2 ^ B := Nat.lt_two_pow_self
    have h2 : 2 ^ B ≤ 2 ^ (m + 4 * B) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [show m + 1 + 4 * B = (m + 4 * B) + 1 by ring, pow_succ]
    nlinarith

theorem eventually_lin_lt (A K : ℕ) : ∀ d, 4 * (A + K) + 1 ≤ d → A * d + K < 2 ^ d := by
  intro d hd
  have h := lin_lt_two_pow (A + K) (d - 4 * (A + K))
  rw [Nat.sub_add_cancel (by omega)] at h
  have : A * d + K ≤ (A + K) * d := by nlinarith
  omega

theorem timeL_le (d : ℕ) : ∀ r, timeL d r ≤ (r + 1) * (2 * d + 2 * r + 10)
  | 0 => by simp [timeL]
  | r + 1 => by
    have := timeL_le d r
    simp only [timeL]
    nlinarith

theorem label_pow (n k : ℕ) (hn : 1 ≤ n) : label (2 ^ (n - 1) * (2 * k + 1)) = n := by
  unfold label
  rw [padicValNat.mul (by positivity) (by omega), padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (by omega)]
  omega

/-- **`bg:ready`(b).** If `U` halts on `n` (`n ≥ 1`), there is `d₀` such that `ρ_d = 1` for every
`d ≥ d₀` with `n(d) = n`; there are infinitely many such `d` (the depths `2^{n-1}(2k + 1)`). -/
theorem ready_b {n : ℕ} (hn1 : 1 ≤ n) (hn : U.HaltsOn n) :
    (∃ d₀, ∀ d, d₀ ≤ d → label d = n → ready U d) ∧
      {d | 1 ≤ d ∧ ready U d ∧ label d = n}.Infinite := by
  obtain ⟨t, c, hf⟩ := exists_firstHalt hn
  -- the time to reach `q_acc` is at most `(2n + 2) d + Kc` for every `d ≥ 8` with `n(d) = n`
  set Kc := (n + 1) * (2 * n + 8) + t + (c.head + 1) + timeR n + (20 * n + 5) + (20 * n + 5) + 1
    with hKc
  have hfirst : ∀ d, 4 * ((2 * n + 2) + Kc) + 1 + 8 ≤ d → label d = n → ready U d := by
    intro d hd hl
    have hd8 : 8 ≤ d := by omega
    subst hl
    have hN := two_le_Nd d
    obtain ⟨_, _, eacc⟩ := run_acc hd8 hf
    set A := time4 d t c.head + (20 * label d + 5) + 1 with hA
    -- `A ≤ (2n + 2) d + Kc < 2^d ≤ N_d - 1`
    have hv : padicValNat 2 d + 1 = label d := by unfold label; omega
    have hS : timeS d ≤ (2 * label d + 2) * d + (label d + 1) * (2 * label d + 8) := by
      have h1 := timeL_le d (padicValNat 2 d)
      unfold timeS
      have e : (padicValNat 2 d + 1) * (2 * d + 2 * padicValNat 2 d + 10) +
          (2 * d + 2 * padicValNat 2 d + 10) =
          (2 * label d + 2) * d + (label d + 1) * (2 * label d + 8) := by
        rw [← hv]; ring
      omega
    have hAle : A ≤ (2 * label d + 2) * d + Kc := by
      simp only [hA, time4]
      omega
    have hlt := eventually_lin_lt (2 * label d + 2) Kc d (by omega)
    have hpow : 2 ^ d + 3 ≤ Nd d := by
      unfold Nd
      have : 2 ^ (d + 2) = 4 * 2 ^ d := by rw [pow_add]; ring
      have : 1 ≤ 2 ^ d := Nat.one_le_two_pow
      omega
    have hAK : A ≤ Nd d - 1 := by omega
    -- the head stays below `A ≤ N_d - 1`, then sits at cell `0` in `q_acc`
    have hacc : ((stepU)^[A] (cfg0 U d)).state = .acc := by
      unfold Reaches at eacc; rw [eacc]
    have hhead : ∀ k < Nd d - 1, ((stepU)^[k] (cfg0 U d)).head + 1 < Nd d := by
      intro k hk
      by_cases hkA : k < A
      · have := iterate_head_le (cfg0 U d) k
        have h0 : (cfg0 U d).head = 0 := rfl
        omega
      · rw [acc_after hacc k (by omega)]
        unfold Reaches at eacc
        rw [eacc]
        simp only
        omega
    have hB := stepB_eq_of_head (N := Nd d) (cfg0 U d) (Nd d - 1) hhead
    unfold ready
    rw [runM_eq, colOf_zero_acc, hB, acc_after hacc (Nd d - 1) hAK]
    unfold Reaches at eacc
    rw [eacc]
    exact ⟨rfl, rfl⟩
  refine ⟨⟨_, hfirst⟩, ?_⟩
  apply Set.infinite_of_not_bddAbove
  rw [not_bddAbove_iff]
  intro M
  set d₀ := 4 * ((2 * n + 2) + Kc) + 1 + 8
  refine ⟨2 ^ (n - 1) * (2 * (M + d₀) + 1), ⟨?_, ?_, label_pow n _ hn1⟩, ?_⟩
  · have : 1 ≤ 2 ^ (n - 1) := Nat.one_le_two_pow
    nlinarith
  · apply hfirst _ _ (label_pow n _ hn1)
    have : 1 ≤ 2 ^ (n - 1) := Nat.one_le_two_pow
    nlinarith
  · have : 1 ≤ 2 ^ (n - 1) := Nat.one_le_two_pow
    nlinarith

/-- Section 7: the set `𝒟_n = {d ≥ 1 : ρ_d = 1, n(d) = n}` of ready depths with label `n` is empty
if `U` does not halt on `n` (by `bg:ready`(a)) ... -/
theorem readyDepths_empty {n : ℕ} (hn : ¬ U.HaltsOn n) :
    {d | 1 ≤ d ∧ ready U d ∧ label d = n} = ∅ := by
  ext d
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨hd, hr, hl⟩
  exact hn (hl ▸ (ready_a hd hr).2.1)

/-- ... and infinite if it does (by `bg:ready`(b)). -/
theorem readyDepths_infinite {n : ℕ} (hn1 : 1 ≤ n) (hn : U.HaltsOn n) :
    {d | 1 ≤ d ∧ ready U d ∧ label d = n}.Infinite :=
  (ready_b hn1 hn).2

end MachineM

end UPD

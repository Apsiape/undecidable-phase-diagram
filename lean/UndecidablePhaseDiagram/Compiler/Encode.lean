/-
# Numbering a one-sided machine (session 11)

An `OMachine σ γ` (`Compiler/OneSided.lean`) with finitely many states and symbols becomes a
`Machine` (`Statements.lean`, Section 2.2) by numbering its states and symbols: the states by
`Fin (card σ - 1 + 1)` with the initial state numbered `0`, the symbols by
`Fin (card γ - 2 + 2)` with the blank numbered `0` and the symbol `one` numbered `1`. The numbered
machine runs in lockstep with `A` (`run_cfgMap`), so halting is unchanged (`toMachine_haltsOn`).
-/
import UndecidablePhaseDiagram.Compiler.OneSided
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fin.SuccPred
import Mathlib.Logic.Equiv.Basic

set_option autoImplicit false

noncomputable section

namespace UPD.Compiler.OMachine

variable {σ γ : Type*} [Fintype σ] [Fintype γ]

/-! ## The numberings -/

omit [Fintype γ] in
/-- There is a state (`A.init`), so `card σ - 1 + 1 = card σ`. -/
theorem card_states (A : OMachine σ γ) : Fintype.card σ - 1 + 1 = Fintype.card σ := by
  have := Fintype.card_pos_iff.mpr ⟨A.init⟩
  omega

omit [Fintype σ] in
/-- There are two distinct symbols (`A.blank ≠ A.one`), so `card γ - 2 + 2 = card γ`. -/
theorem card_symbols (A : OMachine σ γ) (h1 : A.blank ≠ A.one) :
    Fintype.card γ - 2 + 2 = Fintype.card γ := by
  have := Fintype.one_lt_card_iff.mpr ⟨A.blank, A.one, h1⟩
  omega

omit [Fintype γ] in
/-- The numbering of the states, with `A.init` numbered `0` (`stateEquiv_init`). -/
def stateEquiv (A : OMachine σ γ) : σ ≃ Fin (Fintype.card σ - 1 + 1) :=
  let e := (Fintype.equivFin σ).trans (finCongr A.card_states.symm)
  e.trans (Equiv.swap (e A.init) 0)

omit [Fintype γ] in
theorem stateEquiv_init (A : OMachine σ γ) : A.stateEquiv A.init = 0 := by
  simp only [stateEquiv, Equiv.trans_apply, Equiv.swap_apply_left]

omit [Fintype γ] in
theorem stateEquiv_symm_zero (A : OMachine σ γ) : A.stateEquiv.symm 0 = A.init :=
  A.stateEquiv.symm_apply_eq.mpr A.stateEquiv_init.symm

omit [Fintype σ] in
/-- The numbering of the symbols, first stage: `A.blank` numbered `0`. -/
def symEquiv0 (A : OMachine σ γ) (h1 : A.blank ≠ A.one) : γ ≃ Fin (Fintype.card γ - 2 + 2) :=
  let e := (Fintype.equivFin γ).trans (finCongr (A.card_symbols h1).symm)
  e.trans (Equiv.swap (e A.blank) 0)

omit [Fintype σ] in
theorem symEquiv0_blank (A : OMachine σ γ) (h1 : A.blank ≠ A.one) :
    A.symEquiv0 h1 A.blank = 0 := by
  simp only [symEquiv0, Equiv.trans_apply, Equiv.swap_apply_left]

omit [Fintype σ] in
/-- The numbering of the symbols, with `A.blank` numbered `0` (`symEquiv_blank`) and `A.one`
numbered `1` (`symEquiv_one`). -/
def symEquiv (A : OMachine σ γ) (h1 : A.blank ≠ A.one) : γ ≃ Fin (Fintype.card γ - 2 + 2) :=
  (A.symEquiv0 h1).trans (Equiv.swap (A.symEquiv0 h1 A.one) 1)

omit [Fintype σ] in
theorem symEquiv_one (A : OMachine σ γ) (h1 : A.blank ≠ A.one) : A.symEquiv h1 A.one = 1 := by
  simp only [symEquiv, Equiv.trans_apply, Equiv.swap_apply_left]

omit [Fintype σ] in
theorem symEquiv_blank (A : OMachine σ γ) (h1 : A.blank ≠ A.one) :
    A.symEquiv h1 A.blank = 0 := by
  rw [symEquiv, Equiv.trans_apply, symEquiv0_blank]
  apply Equiv.swap_apply_of_ne_of_ne
  · intro h
    rw [← A.symEquiv0_blank h1] at h
    exact h1 ((A.symEquiv0 h1).injective h)
  · intro h
    have := congrArg Fin.val h
    simp at this

/-! ## The numbered machine -/

/-- The numbered machine of `A`. -/
def toMachine (A : OMachine σ γ) (h0 : A.halting A.init = false) (h1 : A.blank ≠ A.one) :
    Machine where
  numStates := Fintype.card σ - 1
  numSymbols := Fintype.card γ - 2
  halting q := A.halting (A.stateEquiv.symm q)
  trans q s :=
    let t := A.trans (A.stateEquiv.symm q) ((A.symEquiv h1).symm s)
    (A.stateEquiv t.1, A.symEquiv h1 t.2.1, t.2.2)
  init_not_halting := (congrArg A.halting A.stateEquiv_symm_zero).trans h0

section Lockstep

variable (A : OMachine σ γ) (h0 : A.halting A.init = false) (h1 : A.blank ≠ A.one)

/-- The numbered image of a configuration of `A`. -/
def cfgMap (c : Cfg σ γ) : (A.toMachine h0 h1).Cfg :=
  ⟨A.stateEquiv c.state, c.head, A.symEquiv h1 ∘ c.tape⟩

theorem halting_cfgMap (c : Cfg σ γ) :
    (A.toMachine h0 h1).halting (A.cfgMap h0 h1 c).state = A.halting c.state := by
  simp only [toMachine, cfgMap, Equiv.symm_apply_apply]

/-- One step of the numbered machine is the numbered image of one step of `A`. -/
theorem step_cfgMap (c : Cfg σ γ) :
    (A.toMachine h0 h1).step (A.cfgMap h0 h1 c) = (A.step c).map (A.cfgMap h0 h1) :=
  set_option backward.isDefEq.respectTransparency false in by
  obtain ⟨s, h, τ⟩ := c
  simp only [Machine.step, step, cfgMap, toMachine, Function.comp_apply, Equiv.symm_apply_apply]
  generalize A.trans s (τ h) = t
  obtain ⟨q, g, d⟩ := t
  cases d
  · by_cases hh : h = 0
    · simp [hh]
    · simp only [hh, Bool.false_eq_true, ↓reduceIte, Option.map_some, cfgMap,
        Function.comp_update]
  · simp only [↓reduceIte, Option.map_some, cfgMap, Function.comp_update]

/-- The numbered machine starts at the numbered image of the start of `A`. -/
theorem start_cfgMap (n : ℕ) : (A.toMachine h0 h1).start n = A.cfgMap h0 h1 (A.start n) :=
  set_option backward.isDefEq.respectTransparency false in by
  simp only [Machine.start, start, cfgMap]
  congr 1
  · exact A.stateEquiv_init.symm
  · funext j
    simp only [Function.comp_apply]
    split_ifs
    · exact (A.symEquiv_one h1).symm
    · exact (A.symEquiv_blank h1).symm

/-- The numbered machine runs in lockstep with `A`. -/
theorem run_cfgMap (n t : ℕ) :
    (A.toMachine h0 h1).run n t = (A.run n t).map (A.cfgMap h0 h1) := by
  induction t with
  | zero => exact congrArg some (A.start_cfgMap h0 h1 n)
  | succ t ih =>
    change ((A.toMachine h0 h1).run n t).bind (A.toMachine h0 h1).step =
      ((A.run n t).bind A.step).map (A.cfgMap h0 h1)
    rw [ih]
    cases A.run n t with
    | none => rfl
    | some c => exact A.step_cfgMap h0 h1 c

end Lockstep

/-- Numbering does not change halting. -/
theorem toMachine_haltsOn (A : OMachine σ γ) (h0 : A.halting A.init = false)
    (h1 : A.blank ≠ A.one) (n : ℕ) : (A.toMachine h0 h1).HaltsOn n ↔ A.HaltsOn n := by
  constructor
  · rintro ⟨t, c', hrun, hhalt⟩
    rw [run_cfgMap] at hrun
    cases hc : A.run n t with
    | none =>
      rw [hc] at hrun
      exact absurd hrun (by simp)
    | some c =>
      rw [hc] at hrun
      have hc' : A.cfgMap h0 h1 c = c' := Option.some.inj hrun
      subst hc'
      exact ⟨t, c, hc, (A.halting_cfgMap h0 h1 c).symm.trans hhalt⟩
  · rintro ⟨t, c, hc, hh⟩
    refine ⟨t, A.cfgMap h0 h1 c, ?_, (A.halting_cfgMap h0 h1 c).trans hh⟩
    rw [run_cfgMap, hc]
    rfl

end UPD.Compiler.OMachine

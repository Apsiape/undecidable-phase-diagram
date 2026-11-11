/-
# One-sided machines over arbitrary types (session 11)

The project's machines (`Machine`, `Statements.lean`, Section 2.2) have numbered states
`Fin (k + 1)` (initial state `0`) and numbered symbols `Fin (m + 2)` (blank `0`, the symbol `1`).
For the construction of a universal machine (`exists_universal`) it is convenient to work first
with machines whose states and symbols are arbitrary types: `OMachine σ γ`, with exactly the step,
start, run and halting of `Machine` (a left move from cell `0` ends the run without halting).
`Compiler/Encode.lean` numbers the states and symbols of an `OMachine` with finitely many of each
and shows that halting is unchanged; `Compiler/Fold.lean` folds a Mathlib `TM0` machine onto a
one-sided tape as an `OMachine`.
-/
import UndecidablePhaseDiagram.Statements

set_option autoImplicit false

namespace UPD.Compiler

/-- A one-sided machine whose states and symbols are types: the initial state, the blank, the
symbol `1` of unary inputs, the halting states, and the transition function
(`trans q γ = (q', γ', D)`: write `γ'`, go to `q'`, move one cell right if `D = true` and one cell
left if `D = false`), as in `Machine`. -/
structure OMachine (σ γ : Type*) where
  /-- the initial state -/
  init : σ
  /-- the blank -/
  blank : γ
  /-- the symbol `1` of unary inputs -/
  one : γ
  /-- the halting states -/
  halting : σ → Bool
  /-- the transition function -/
  trans : σ → γ → σ × γ × Bool

namespace OMachine

/-- A configuration: state, head cell, one-sided tape (as `Machine.Cfg`). -/
structure Cfg (σ γ : Type*) where
  /-- the state -/
  state : σ
  /-- the head cell -/
  head : ℕ
  /-- the tape -/
  tape : ℕ → γ

variable {σ γ : Type*} (A : OMachine σ γ)

/-- One step (as `Machine.step`): write, change state, move one cell left or right; a move left
from cell `0` ends the run (`none`). -/
def step (c : Cfg σ γ) : Option (Cfg σ γ) :=
  let t := A.trans c.state (c.tape c.head)
  if t.2.2 then some ⟨t.1, c.head + 1, Function.update c.tape c.head t.2.1⟩
  else if c.head = 0 then none
  else some ⟨t.1, c.head - 1, Function.update c.tape c.head t.2.1⟩

/-- The start on input `n` (as `Machine.start`): initial state, head on cell `0`, cells
`0, …, n-1` hold `one`, all other cells are blank. -/
def start (n : ℕ) : Cfg σ γ := ⟨A.init, 0, fun j => if j < n then A.one else A.blank⟩

/-- The configuration after `t` steps on input `n` (as `Machine.run`). -/
def run (n : ℕ) : ℕ → Option (Cfg σ γ)
  | 0 => some (A.start n)
  | t + 1 => (run n t).bind A.step

/-- `A` halts on input `n` (as `Machine.HaltsOn`): started on input `n`, it enters a halting
state. -/
def HaltsOn (n : ℕ) : Prop :=
  ∃ (t : ℕ) (c : Cfg σ γ), A.run n t = some c ∧ A.halting c.state = true

theorem run_zero (n : ℕ) : A.run n 0 = some (A.start n) := rfl

theorem run_succ (n t : ℕ) : A.run n (t + 1) = (A.run n t).bind A.step := rfl

theorem run_succ_of {n t : ℕ} {c c' : Cfg σ γ} (h : A.run n t = some c)
    (h' : A.step c = some c') : A.run n (t + 1) = some c' := by
  rw [run_succ, h, Option.bind_some, h']

/-- A step with a right move. -/
theorem step_right {c : Cfg σ γ} (h : (A.trans c.state (c.tape c.head)).2.2 = true) :
    A.step c = some ⟨(A.trans c.state (c.tape c.head)).1, c.head + 1,
      Function.update c.tape c.head (A.trans c.state (c.tape c.head)).2.1⟩ := by
  simp only [step, h, if_true]

/-- A step with a left move from a cell `≥ 1`. -/
theorem step_left {c : Cfg σ γ} (h : (A.trans c.state (c.tape c.head)).2.2 = false)
    (hc : c.head ≠ 0) :
    A.step c = some ⟨(A.trans c.state (c.tape c.head)).1, c.head - 1,
      Function.update c.tape c.head (A.trans c.state (c.tape c.head)).2.1⟩ := by
  simp only [step, h, Bool.false_eq_true, if_false, hc]

end OMachine

end UPD.Compiler

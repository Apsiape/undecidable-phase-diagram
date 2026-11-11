/-
# Sanity checks of the statement-level definitions

Small theorems that exercise the definitions of `Statements.lean` against their printed meaning
(they guard fidelity; nothing downstream depends on them yet):
* `fill`: as `ζ` ranges over `Λ → 𝔖`, `fill ω Λ ζ` ranges exactly once over the configurations
  `η` with `η_{Λᶜ} = ω_{Λᶜ}` (`fill_agrees`, `fill_restrict`, `fill_injective`) — the sum in
  `kernelApply` is the paper's sum over `η`.
* Halting (Section 2.2): a machine that walks right over the input `1ⁿ` and halts on the first
  blank halts on every input (`walker_halts`, which checks the input convention); a machine whose
  first move is to the left never halts (`leftFirst_not_halts`, the **[choice]** of `Machine.step`).
* The machine `M` (App. C): `q_acc` and `q_fail` are absorbing (`deltaM_acc`, `deltaM_fail`),
  `init(h, 1)` carries `q_start = P₀` (`initM_start`).
-/
import UndecidablePhaseDiagram.Statements

set_option autoImplicit false

namespace UPD

/-! ## `fill` -/

section Fill

variable {S : Type}

theorem fill_agrees (ω : Config S) (Λ : Finset Plane) (ζ : Λ → S) {ξ : Plane} (h : ξ ∉ Λ) :
    fill ω Λ ζ ξ = ω ξ := by simp [fill, h]

theorem fill_restrict (ω η : Config S) (Λ : Finset Plane) (h : ∀ ξ, ξ ∉ Λ → η ξ = ω ξ) :
    fill ω Λ (fun x => η x.1) = η := by
  funext ξ
  by_cases hξ : ξ ∈ Λ
  · simp [fill, hξ]
  · simp [fill, hξ, h ξ hξ]

theorem fill_injective (ω : Config S) (Λ : Finset Plane) : Function.Injective (fill ω Λ) := by
  intro ζ ζ' h
  funext x
  have := congrFun h x.1
  simpa [fill, x.2] using this

end Fill

/-! ## Halting -/

/-- A machine with states `{0, 1}` (`1` halting) and symbols `{0, 1}`: in state `0` it moves right
over the symbol `1` and enters the halting state `1` on a blank. -/
def walker : Machine where
  numStates := 1
  numSymbols := 0
  halting q := decide (q = 1)
  trans q γ := (if q = 0 ∧ γ = 0 then 1 else q, γ, true)
  init_not_halting := rfl

theorem walker_run (n t : ℕ) (ht : t ≤ n) :
    walker.run n t = some ⟨0, t, fun j => if j < n then 1 else 0⟩ :=
  set_option backward.isDefEq.respectTransparency false in by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Machine.run, ih (by omega)]
    simp only [Option.bind_some, Machine.step, walker]
    have : (t < n) := by omega
    simp only [this, if_true]
    congr
    funext j
    by_cases hj : j = t <;> simp [Function.update_apply, hj, this]

/-- `walker` halts on every input `n` (after `n + 1` steps, on the first blank cell `n`). -/
theorem walker_halts (n : ℕ) : walker.HaltsOn n :=
  set_option backward.isDefEq.respectTransparency false in by
  refine ⟨n + 1, ⟨1, n + 1, fun j => if j < n then 1 else 0⟩, ?_, rfl⟩
  rw [Machine.run, walker_run n n le_rfl]
  simp only [Option.bind_some, Machine.step, walker, lt_irrefl, if_false, if_true]
  congr
  funext j
  by_cases hj : j = n <;> simp [Function.update_apply, hj]

/-- A machine whose only move is to the left, into the halting state `1`. -/
def leftFirst : Machine where
  numStates := 1
  numSymbols := 0
  halting q := decide (q = 1)
  trans _ γ := (1, γ, false)
  init_not_halting := rfl

theorem leftFirst_run (n t : ℕ) : leftFirst.run n (t + 1) = none := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Machine.run, ih]; rfl

/-- **[choice] check.** A left move from cell `0` ends the run without halting: `leftFirst`
would enter its halting state only by moving left from cell `0`, so it halts on no input. -/
theorem leftFirst_not_halts (n : ℕ) : ¬ leftFirst.HaltsOn n :=
  set_option backward.isDefEq.respectTransparency false in by
  rintro ⟨t, c, hc, hh⟩
  cases t with
  | zero =>
    simp only [Machine.run, Option.some.injEq] at hc
    subst hc
    simp [leftFirst, Machine.start] at hh
  | succ t => rw [leftFirst_run] at hc; cases hc

/-! ## The machine `M` -/

theorem deltaM_acc (U : Machine) (g : TapeM U) : deltaM U .acc g = (.acc, g, .stay) := rfl

theorem deltaM_fail (U : Machine) (g : TapeM U) : deltaM U .fail g = (.fail, g, .stay) := rfl

theorem initM_start (U : Machine) (h : Bool) :
    initM U h true = (⟨h, true, 0, false, 0, false, false⟩, some (.P 0)) := rfl

end UPD

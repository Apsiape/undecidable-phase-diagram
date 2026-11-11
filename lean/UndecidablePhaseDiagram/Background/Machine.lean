/-
# The run of `M`: one head per column (App. C, the paragraph after `mach:def-run`; `bg:ready`)

The paper (after `mach:def-run`): "By induction on `i`, each `c_i` has exactly one cell with a head,
and `c_{i+1}` is obtained from `c_i` by one step of `M`, except that a step that would move the head
off the tape `[0, N)` instead puts it in `q_fail`." This file proves the induction step: for a
column `oneHead t h q` (tape `t`, one head at `h` in state `q`), the next column `nextRow` (the local
rule `f_M` with `⊥` beyond both ends, as in `mach:def-run`) is the column after one step of `δ_M`:
* `nextRow_stay`, `nextRow_up`, `nextRow_down`: the head writes `g'`, enters `q'` and moves by `D`;
* `nextRow_up_fail`, `nextRow_down_fail`: a move off the tape leaves the tape unchanged and puts
  the head in `q_fail` at the same cell.
First step of `bg:ready` (BLUEPRINT G.1, step (1)).
-/
import UndecidablePhaseDiagram.Statements

set_option autoImplicit false

namespace UPD

namespace MachineM

variable {U : Machine}

/-- One row of the automaton of App. C on the cells `0, …, N - 1` (`⊥` beyond both ends): cell `i`
becomes `f_M(row(i-1), row(i), row(i+1))`. -/
def nextRow {N : ℕ} (row : Fin N → CellM U) (i : Fin N) : CellM U :=
  fM U (if h : 0 < i.val then some (row ⟨i.val - 1, by omega⟩) else none) (row i)
    (if h : i.val + 1 < N then some (row ⟨i.val + 1, h⟩) else none)

/-- A row with exactly one head, at `h`, in state `q`, on the tape `t`. -/
def oneHead {N : ℕ} (t : Fin N → TapeM U) (h : Fin N) (q : StateM U) : Fin N → CellM U :=
  fun i => (t i, if i = h then some q else none)

theorem fromBelow_none_of_none {g : TapeM U} : fromBelow U (some (g, none)) = none := rfl

theorem fromAbove_none_of_none {g : TapeM U} : fromAbove U (some (g, none)) = none := rfl

/-- **One-head invariant, move up.** -/
theorem nextRow_up {N : ℕ} (t : Fin N → TapeM U) (h : Fin N) (q : StateM U)
    (hD : (deltaM U q (t h)).2.2 = .up) (hh : h.val + 1 < N) :
    nextRow (oneHead t h q) =
      oneHead (Function.update t h (deltaM U q (t h)).2.1) ⟨h.val + 1, hh⟩ (deltaM U q (t h)).1 := by
  funext i
  by_cases hi : i = h
  · subst hi
    have hne : i ≠ ⟨i.val + 1, hh⟩ := fun h' => by
      have := congrArg Fin.val h'; simp at this
    simp [nextRow, oneHead, fM, hD, hh, hne]
  · by_cases hi1 : i.val = h.val + 1
    · have hpos : 0 < i.val := by omega
      have hprev : (⟨i.val - 1, by omega⟩ : Fin N) = h := Fin.ext (by simp; omega)
      have hieq : i = ⟨h.val + 1, hh⟩ := Fin.ext hi1
      have hup : Function.update t h (deltaM U q (t h)).2.1 i = t i :=
        Function.update_of_ne hi _ _
      simp only [nextRow, oneHead, fM, if_neg hi, dif_pos hpos, hprev, fromBelow, hup, if_pos hieq]
      simp [hD]
    · have hieq : i ≠ ⟨h.val + 1, hh⟩ := fun h' => hi1 (by rw [h'])
      have hbelow : ∀ hp : 0 < i.val, (⟨i.val - 1, by omega⟩ : Fin N) ≠ h := fun hp h' => by
        have := congrArg Fin.val h'; simp at this; omega
      have habove : ∀ ha : i.val + 1 < N, (⟨i.val + 1, ha⟩ : Fin N) = h →
          fromAbove U (some (t h, some q)) = none := fun _ _ => by
        simp [fromAbove, hD]
      simp only [nextRow, oneHead, fM, if_neg hi, if_neg hieq, Function.update_of_ne hi]
      split_ifs with h1 h2 h3 <;> simp_all [fromBelow, fromAbove]

/-- **One-head invariant, stay.** -/
theorem nextRow_stay {N : ℕ} (t : Fin N → TapeM U) (h : Fin N) (q : StateM U)
    (hD : (deltaM U q (t h)).2.2 = .stay) :
    nextRow (oneHead t h q) =
      oneHead (Function.update t h (deltaM U q (t h)).2.1) h (deltaM U q (t h)).1 := by
  funext i
  by_cases hi : i = h
  · subst hi
    simp [nextRow, oneHead, fM, hD]
  · have hb : ∀ g : TapeM U, ∀ q₀ : StateM U, (deltaM U q₀ g).2.2 = .stay →
        fromBelow U (some (g, some q₀)) = none := fun g q₀ h' => by simp [fromBelow, h']
    have ha : ∀ g : TapeM U, ∀ q₀ : StateM U, (deltaM U q₀ g).2.2 = .stay →
        fromAbove U (some (g, some q₀)) = none := fun g q₀ h' => by simp [fromAbove, h']
    simp only [nextRow, oneHead, fM, if_neg hi, Function.update_of_ne hi]
    split_ifs with h1 h2 h3 h4 <;> simp_all [fromBelow, fromAbove]

/-- **One-head invariant, move down.** -/
theorem nextRow_down {N : ℕ} (t : Fin N → TapeM U) (h : Fin N) (q : StateM U)
    (hD : (deltaM U q (t h)).2.2 = .down) (hh : 0 < h.val) :
    nextRow (oneHead t h q) =
      oneHead (Function.update t h (deltaM U q (t h)).2.1) ⟨h.val - 1, by omega⟩
        (deltaM U q (t h)).1 := by
  funext i
  by_cases hi : i = h
  · subst hi
    have hne : i ≠ ⟨i.val - 1, by omega⟩ := fun h' => by
      have := congrArg Fin.val h'; simp at this; omega
    simp [nextRow, oneHead, fM, hD, hh, hne]
  · by_cases hi1 : i.val + 1 = h.val
    · have hlt : i.val + 1 < N := by omega
      have hnext : (⟨i.val + 1, hlt⟩ : Fin N) = h := Fin.ext (by simp; omega)
      have hieq : i = ⟨h.val - 1, by omega⟩ := Fin.ext (by simp; omega)
      have hup : Function.update t h (deltaM U q (t h)).2.1 i = t i :=
        Function.update_of_ne hi _ _
      have hbelow : ∀ hp : 0 < i.val, (⟨i.val - 1, by omega⟩ : Fin N) ≠ h := fun hp h' => by
        have := congrArg Fin.val h'; simp at this; omega
      simp only [nextRow, oneHead, fM, if_neg hi, dif_pos hlt, hnext, hup, if_pos hieq]
      split_ifs with h1 <;> simp_all [fromBelow, fromAbove]
    · have hieq : i ≠ ⟨h.val - 1, by omega⟩ := fun h' => hi1 (by rw [h']; simp; omega)
      have habove : ∀ ha : i.val + 1 < N, (⟨i.val + 1, ha⟩ : Fin N) ≠ h := fun ha h' => by
        have := congrArg Fin.val h'; simp at this; omega
      have hb : fromBelow U (some (t h, some q)) = none := by simp [fromBelow, hD]
      simp only [nextRow, oneHead, fM, if_neg hi, if_neg hieq, Function.update_of_ne hi]
      split_ifs with h1 h2 h3 h4 <;> simp_all [fromBelow, fromAbove]

/-- **One-head invariant, exit at the top**: a head that would leave the row upwards enters
`q_fail` and writes nothing. -/
theorem nextRow_up_fail {N : ℕ} (t : Fin N → TapeM U) (h : Fin N) (q : StateM U)
    (hD : (deltaM U q (t h)).2.2 = .up) (hh : h.val + 1 = N) :
    nextRow (oneHead t h q) = oneHead t h .fail := by
  funext i
  by_cases hi : i = h
  · subst hi
    have hn : ¬ (i.val + 1 < N) := by omega
    simp [nextRow, oneHead, fM, hD, hn]
  · have hbelow : ∀ hp : 0 < i.val, (⟨i.val - 1, by omega⟩ : Fin N) ≠ h := fun hp h' => by
      have := congrArg Fin.val h'; simp at this; have := i.2; omega
    have ha : fromAbove U (some (t h, some q)) = none := by simp [fromAbove, hD]
    simp only [nextRow, oneHead, fM, if_neg hi]
    split_ifs with h1 h2 h3 h4 <;> simp_all [fromBelow, fromAbove]

/-- **One-head invariant, exit at the bottom**: a head that would leave the row downwards enters
`q_fail` and writes nothing. -/
theorem nextRow_down_fail {N : ℕ} (t : Fin N → TapeM U) (h : Fin N) (q : StateM U)
    (hD : (deltaM U q (t h)).2.2 = .down) (hh : h.val = 0) :
    nextRow (oneHead t h q) = oneHead t h .fail := by
  funext i
  by_cases hi : i = h
  · subst hi
    have hn : ¬ (0 < i.val) := by omega
    simp [nextRow, oneHead, fM, hD, hn]
  · have habove : ∀ ha : i.val + 1 < N, (⟨i.val + 1, ha⟩ : Fin N) ≠ h := fun ha h' => by
      have := congrArg Fin.val h'; simp at this; omega
    have hb : fromBelow U (some (t h, some q)) = none := by simp [fromBelow, hD]
    simp only [nextRow, oneHead, fM, if_neg hi]
    split_ifs with h1 h2 h3 h4 <;> simp_all [fromBelow, fromAbove]

end MachineM

end UPD

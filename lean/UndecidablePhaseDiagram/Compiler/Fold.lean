/-
# Folding a Mathlib `TM0` machine onto a one-sided tape (session 11)

A Mathlib machine `M : Turing.TM0.Machine Γ Λ` works on a two-sided tape. Its fold
`fold M a0 a1` is a one-sided machine (`OMachine`, `Compiler/OneSided.lean`) with two tracks and a
mark: the positions of `M`'s tape (relative to its start head, position `0` = the first input
symbol) are folded onto the cells `x = 0, 1, 2, …`, the upper track of cell `x` holding position
`x + 1` and the lower track of cell `x` holding position `-x`; the mark singles out cell `0`.

Started on the unary input `1ⁿ` (`one = (a1, blank, unmarked)`), the fold first writes `a0` on the
lower track of cell `0` and marks it (`init`, then `back`), so that its tape holds `M`'s initial
tape on `a0 :: a1ⁿ`; then it simulates `M` step by step: a move of `M` is one move of the fold,
except at cell `0` where a move between the two tracks (position `1 ↔ 0`) and every write of `M`
are bounces (one step right, then one step left in a `back` state). The fold never moves left from
cell `0`. When `M` halts the fold enters its only halting state `halt`.

* `fold_haltsOn`: the fold halts on `1ⁿ` iff `M` halts on `a0 :: a1ⁿ` (`(TM0.eval M _).Dom`).

The construction follows the machine `M°` of the forgetting project
(`C:/Infanox/fixed-noise-ergodicity-lean/FixedNoiseErgodicity/Family/Machine.lean`, section
"The machine `M°`"), here for Mathlib's `TM0` machines started on an input, with cells from `0`.
-/
import UndecidablePhaseDiagram.Compiler.OneSided
import Mathlib.Computability.TuringMachine.PostTuringMachine
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod

set_option autoImplicit false

namespace UPD.Compiler

open Turing

/-- States of the folded machine. -/
inductive FState (Λ : Type*) where
  | init
  | sim (q : Λ) (lower : Bool)
  | back (q : Λ) (lower : Bool)
  | halt

/-- `FState Λ` as a finite combination of `Λ` and `Bool` (no decidable equality needed). -/
def FState.equivOption (Λ : Type*) : Option (Option (Λ × Bool × Bool)) ≃ FState Λ where
  toFun := fun x => match x with
    | none => .init
    | some none => .halt
    | some (some (q, lo, false)) => .sim q lo
    | some (some (q, lo, true)) => .back q lo
  invFun := fun s => match s with
    | .init => none
    | .halt => some none
    | .sim q lo => some (some (q, lo, false))
    | .back q lo => some (some (q, lo, true))
  left_inv := by
    intro x
    rcases x with _ | (_ | ⟨q, lo, (_ | _)⟩) <;> rfl
  right_inv := by
    intro s
    cases s <;> rfl

/-- needed downstream -/
instance FState.instFintype {Λ : Type*} [Fintype Λ] : Fintype (FState Λ) :=
  Fintype.ofEquiv _ (FState.equivOption Λ)

namespace Fold

section Tracks

variable {Γ : Type*}

/-- The symbol on track `lo` of a cell (`false`: upper, `true`: lower). -/
def tget (g : Γ × Γ × Bool) (lo : Bool) : Γ :=
  match lo with
  | false => g.1
  | true => g.2.1

/-- Write `b` on track `lo` of a cell, keeping the other track and the mark. -/
def tset (g : Γ × Γ × Bool) (lo : Bool) (b : Γ) : Γ × Γ × Bool :=
  match lo with
  | false => (b, g.2.1, g.2.2)
  | true => (g.1, b, g.2.2)

theorem tset_mark (g : Γ × Γ × Bool) (lo : Bool) (b : Γ) : (tset g lo b).2.2 = g.2.2 := by
  cases lo <;> rfl

theorem tget_tset (g : Γ × Γ × Bool) (lo l : Bool) (b : Γ) :
    tget (tset g lo b) l = if l = lo then b else tget g l := by
  cases lo <;> cases l <;> rfl

/-- The position of `M`'s tape (relative to its start head) held by track `l` of cell `x`. -/
def pos (l : Bool) (x : ℕ) : ℤ :=
  match l with
  | false => (x : ℤ) + 1
  | true => -(x : ℤ)

theorem pos_inj {l l' : Bool} {x x' : ℕ} (h : pos l x = pos l' x') : l = l' ∧ x = x' := by
  cases l <;> cases l' <;> simp only [pos] at h
  · exact ⟨rfl, by omega⟩
  · exact absurd h (by omega)
  · exact absurd h (by omega)
  · exact ⟨rfl, by omega⟩

/-- The move of the fold for a move `d` of `M` into state `q'` on track `lo`, at a cell with mark
`mk`: the new state and the direction (`true`: right). On the upper track a move of `M` is the
same move of the fold, on the lower track the opposite move; at the marked cell `0` a move from
one track to the other (position `1 → 0` or `0 → 1`) is a bounce through a `back` state. -/
def fmove {Λ : Type*} (q' : Λ) (lo mk : Bool) (d : Dir) : FState Λ × Bool :=
  match lo, d with
  | false, .right => (.sim q' false, true)
  | false, .left => bif mk then (.back q' true, true) else (.sim q' false, false)
  | true, .left => (.sim q' true, true)
  | true, .right => bif mk then (.back q' false, true) else (.sim q' true, false)

end Tracks

/-- The halting states of the fold: only `halt`. -/
def isHalt {Λ : Type*} (s : FState Λ) : Bool :=
  match s with
  | .halt => true
  | _ => false

variable {Γ Λ : Type*} [Inhabited Λ]

/-- The transition function of the fold. `init` (on cell `0`): write `a0` on the lower track,
mark the cell, step right and come back in `sim default true`. `back q lo`: step left into
`sim q lo`, writing back the scanned symbol. `sim q lo`: read the symbol `a` of track `lo`; if `M`
halts on `(q, a)`, enter `halt`; on a write of `M`, write on track `lo` and bounce; on a move of
`M`, move as `fmove` says. `halt` stays and moves right. -/
def tr (M : TM0.Machine Γ Λ) (a0 : Γ) (s : FState Λ) (g : Γ × Γ × Bool) :
    FState Λ × (Γ × Γ × Bool) × Bool :=
  match s with
  | .init => (.back default true, (g.1, a0, true), true)
  | .back q lo => (.sim q lo, g, false)
  | .halt => (.halt, g, true)
  | .sim q lo =>
    match M q (tget g lo) with
    | none => (.halt, g, true)
    | some (q', .write b) => (.back q' lo, tset g lo b, true)
    | some (q', .move d) => ((fmove q' lo g.2.2 d).1, g, (fmove q' lo g.2.2 d).2)

end Fold

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- The fold of `M` (symbols: upper track, lower track, cell-0 mark). -/
def fold (M : TM0.Machine Γ Λ) (a0 a1 : Γ) : OMachine (FState Λ) (Γ × Γ × Bool) where
  init := .init
  blank := ((default : Γ), (default : Γ), false)
  one := (a1, (default : Γ), false)
  halting := Fold.isHalt
  trans := Fold.tr M a0

theorem fold_init (M : TM0.Machine Γ Λ) (a0 a1 : Γ) : (fold M a0 a1).init = FState.init := rfl
theorem fold_blank (M : TM0.Machine Γ Λ) (a0 a1 : Γ) :
    (fold M a0 a1).blank = ((default : Γ), (default : Γ), false) := rfl
theorem fold_one (M : TM0.Machine Γ Λ) (a0 a1 : Γ) :
    (fold M a0 a1).one = (a1, (default : Γ), false) := rfl
theorem fold_halting_init (M : TM0.Machine Γ Λ) (a0 a1 : Γ) :
    (fold M a0 a1).halting (fold M a0 a1).init = false := rfl

namespace Fold

/-! ### Steps of one-sided machines on explicit configurations -/

section Steps

variable {σ γ : Type*} (A : OMachine σ γ)

theorem step_mk_right {s s' : σ} {i : ℕ} {τ : ℕ → γ} {g : γ}
    (h : A.trans s (τ i) = (s', g, true)) :
    A.step ⟨s, i, τ⟩ = some ⟨s', i + 1, Function.update τ i g⟩ := by
  simp only [OMachine.step, h, if_true]

theorem step_mk_left {s s' : σ} {i : ℕ} {τ : ℕ → γ} {g : γ}
    (h : A.trans s (τ (i + 1)) = (s', g, false)) :
    A.step ⟨s, i + 1, τ⟩ = some ⟨s', i, Function.update τ (i + 1) g⟩ := by
  simp only [OMachine.step, h, Bool.false_eq_true, if_false, Nat.add_one_ne_zero,
    Nat.add_sub_cancel]

theorem step_mk_right' {s s' : σ} {i : ℕ} {τ : ℕ → γ}
    (h : A.trans s (τ i) = (s', τ i, true)) : A.step ⟨s, i, τ⟩ = some ⟨s', i + 1, τ⟩ := by
  rw [step_mk_right A h, Function.update_eq_self]

theorem step_mk_left' {s s' : σ} {i : ℕ} {τ : ℕ → γ}
    (h : A.trans s (τ (i + 1)) = (s', τ (i + 1), false)) :
    A.step ⟨s, i + 1, τ⟩ = some ⟨s', i, τ⟩ := by
  rw [step_mk_left A h, Function.update_eq_self]

end Steps

/-! ### The simulation relation -/

section Rel

/-- The tape relation: only cell `0` is marked, and track `l` of cell `x` holds the symbol of `T`
at the position `pos l x`, relative to the head position `pos lo i` (Mathlib's `Tape.nth` is
relative to the head). -/
def TapeRel (τ : ℕ → Γ × Γ × Bool) (T : Tape Γ) (lo : Bool) (i : ℕ) : Prop :=
  ∀ x, (τ x).2.2 = decide (x = 0) ∧ ∀ l, tget (τ x) l = T.nth (pos l x - pos lo i)

/-- The simulation relation: the fold is in `sim q lo` with `q` the state of `M`, its head on
cell `i` and track `lo`, and its tape is related to the tape of `M`. -/
def Rel (c : OMachine.Cfg (FState Λ) (Γ × Γ × Bool)) (b : TM0.Cfg Γ Λ) : Prop :=
  ∃ lo, c.state = .sim b.q lo ∧ TapeRel c.tape b.Tape lo c.head

theorem tapeRel_write {τ : ℕ → Γ × Γ × Bool} {T : Tape Γ} {lo : Bool} {i : ℕ}
    (hτ : TapeRel τ T lo i) (a : Γ) :
    TapeRel (Function.update τ i (tset (τ i) lo a)) (T.write a) lo i := by
  intro x
  by_cases hx : x = i
  · rw [hx, Function.update_self]
    refine ⟨by rw [tset_mark]; exact (hτ i).1, fun l => ?_⟩
    rw [tget_tset, Tape.write_nth]
    by_cases hl : l = lo
    · subst hl; simp
    · rw [if_neg hl, if_neg, (hτ i).2 l]
      intro he
      exact hl (pos_inj (show pos l i = pos lo i by omega)).1
  · rw [Function.update_of_ne hx]
    refine ⟨(hτ x).1, fun l => ?_⟩
    rw [Tape.write_nth, if_neg, (hτ x).2 l]
    intro he
    exact hx (pos_inj (show pos l x = pos lo i by omega)).2

theorem tapeRel_right {τ : ℕ → Γ × Γ × Bool} {T : Tape Γ} {lo lo' : Bool} {i i' : ℕ}
    (hτ : TapeRel τ T lo i) (hp : pos lo' i' = pos lo i + 1) :
    TapeRel τ (T.move .right) lo' i' := by
  intro x
  refine ⟨(hτ x).1, fun l => ?_⟩
  rw [(hτ x).2 l, Tape.move_right_nth, hp]
  congr 1
  omega

theorem tapeRel_left {τ : ℕ → Γ × Γ × Bool} {T : Tape Γ} {lo lo' : Bool} {i i' : ℕ}
    (hτ : TapeRel τ T lo i) (hp : pos lo' i' = pos lo i - 1) :
    TapeRel τ (T.move .left) lo' i' := by
  intro x
  refine ⟨(hτ x).1, fun l => ?_⟩
  rw [(hτ x).2 l, Tape.move_left_nth, hp]
  congr 1
  omega

end Rel

/-! ### One step of `M` -/

section Step

/-- If `M` halts, the fold enters `halt` in one step. -/
theorem rel_step_none (M : TM0.Machine Γ Λ) (a0 a1 : Γ)
    {c : OMachine.Cfg (FState Λ) (Γ × Γ × Bool)} {b : TM0.Cfg Γ Λ} (hr : Rel c b)
    (hb : TM0.step M b = none) :
    ∃ c', (fold M a0 a1).step c = some c' ∧ c'.state = .halt := by
  obtain ⟨s, i, τ⟩ := c
  obtain ⟨q, T⟩ := b
  obtain ⟨lo, hs, hτ⟩ := hr
  change s = .sim q lo at hs
  change TapeRel τ T lo i at hτ
  subst hs
  have hget : tget (τ i) lo = T.head := by rw [(hτ i).2 lo, sub_self, Tape.nth_zero]
  have hM : M q T.head = none := by
    rcases h : M q T.head with _ | ⟨q', st⟩
    · rfl
    · simp [TM0.step, h] at hb
  have htr : (fold M a0 a1).trans (.sim q lo) (τ i) = (.halt, τ i, true) := by
    simp only [fold, tr, hget, hM]
  exact ⟨_, step_mk_right _ htr, rfl⟩

/-- **One step of `M` is one step of the fold (a direct move) or two (a bounce through a `back`
state).** -/
theorem rel_step_some (M : TM0.Machine Γ Λ) (a0 a1 : Γ)
    {c : OMachine.Cfg (FState Λ) (Γ × Γ × Bool)} {b b' : TM0.Cfg Γ Λ} (hr : Rel c b)
    (hb : TM0.step M b = some b') :
    (∃ c', (fold M a0 a1).step c = some c' ∧ Rel c' b') ∨
      ∃ c' c'', (fold M a0 a1).step c = some c' ∧ (fold M a0 a1).halting c'.state = false ∧
        (fold M a0 a1).step c' = some c'' ∧ Rel c'' b' := by
  obtain ⟨s, i, τ⟩ := c
  obtain ⟨q, T⟩ := b
  obtain ⟨lo, hs, hτ⟩ := hr
  change s = .sim q lo at hs
  change TapeRel τ T lo i at hτ
  subst hs
  have hget : tget (τ i) lo = T.head := by rw [(hτ i).2 lo, sub_self, Tape.nth_zero]
  have hmk : (τ i).2.2 = decide (i = 0) := (hτ i).1
  rcases hM : M q T.head with _ | ⟨q', st⟩
  · simp [TM0.step, hM] at hb
  · cases st with
    | write a =>
      have h1 : TM0.step M ⟨q, T⟩ = some ⟨q', T.write a⟩ := by simp [TM0.step, hM]
      rw [h1] at hb
      cases hb
      have htr : (fold M a0 a1).trans (.sim q lo) (τ i) = (.back q' lo, tset (τ i) lo a, true) := by
        simp only [fold, tr, hget, hM]
      exact Or.inr ⟨_, _, step_mk_right _ htr, rfl, step_mk_left' _ rfl,
        Exists.intro lo ⟨rfl, tapeRel_write hτ a⟩⟩
    | move d =>
      have h1 : TM0.step M ⟨q, T⟩ = some ⟨q', T.move d⟩ := by simp [TM0.step, hM]
      rw [h1] at hb
      cases hb
      have htr : (fold M a0 a1).trans (.sim q lo) (τ i) =
          ((fmove q' lo (τ i).2.2 d).1, τ i, (fmove q' lo (τ i).2.2 d).2) := by
        simp only [fold, tr, hget, hM]
      rw [hmk] at htr
      cases lo <;> cases d
      · -- upper track, left move
        rcases i with _ | k
        · -- cell `0`: position `1 → 0`, a bounce onto the lower track
          have h' : (fold M a0 a1).trans (.sim q false) (τ 0) = (.back q' true, τ 0, true) := htr
          exact Or.inr ⟨_, _, step_mk_right' _ h', rfl, step_mk_left' _ rfl,
            Exists.intro true ⟨rfl, tapeRel_left hτ (by simp only [pos]; omega)⟩⟩
        · have h' : (fold M a0 a1).trans (.sim q false) (τ (k + 1)) =
              (.sim q' false, τ (k + 1), false) := htr
          exact Or.inl ⟨_, step_mk_left' _ h',
            Exists.intro false ⟨rfl, tapeRel_left hτ (by simp only [pos]; omega)⟩⟩
      · -- upper track, right move
        have h' : (fold M a0 a1).trans (.sim q false) (τ i) = (.sim q' false, τ i, true) := htr
        exact Or.inl ⟨_, step_mk_right' _ h',
          Exists.intro false ⟨rfl, tapeRel_right hτ (by simp only [pos]; omega)⟩⟩
      · -- lower track, left move
        have h' : (fold M a0 a1).trans (.sim q true) (τ i) = (.sim q' true, τ i, true) := htr
        exact Or.inl ⟨_, step_mk_right' _ h',
          Exists.intro true ⟨rfl, tapeRel_left hτ (by simp only [pos]; omega)⟩⟩
      · -- lower track, right move
        rcases i with _ | k
        · -- cell `0`: position `0 → 1`, a bounce onto the upper track
          have h' : (fold M a0 a1).trans (.sim q true) (τ 0) = (.back q' false, τ 0, true) := htr
          exact Or.inr ⟨_, _, step_mk_right' _ h', rfl, step_mk_left' _ rfl,
            Exists.intro false ⟨rfl, tapeRel_right hτ (by simp only [pos]; omega)⟩⟩
        · have h' : (fold M a0 a1).trans (.sim q true) (τ (k + 1)) =
              (.sim q' true, τ (k + 1), false) := htr
          exact Or.inl ⟨_, step_mk_left' _ h',
            Exists.intro true ⟨rfl, tapeRel_right hτ (by simp only [pos]; omega)⟩⟩

end Step

/-! ### The start -/

section Start

-- Adapted from C:/Infanox/fixed-noise-ergodicity-lean/FixedNoiseErgodicity/Compiler/TM0.lean,
-- `mk₁_nth` (split into the two cases used here).
theorem mk₁_nth_nat (w : List Γ) (k : ℕ) : (Tape.mk₁ w).nth (k : ℤ) = w.getI k := by
  rw [Tape.mk₁, Tape.mk₂, Tape.mk'_nth_nat, ListBlank.nth_mk]

theorem mk₁_nth_neg (w : List Γ) (k : ℕ) : (Tape.mk₁ w).nth (-((k + 1 : ℕ) : ℤ)) = default := by
  show (ListBlank.mk ([] : List Γ)).nth k = default
  rw [ListBlank.nth_mk]
  rfl

theorem getI_replicate (a : Γ) (n x : ℕ) :
    (List.replicate n a).getI x = if x < n then a else default := by
  split_ifs with h
  · rw [List.getI_eq_getElem _ (by rw [List.length_replicate]; exact h), List.getElem_replicate]
  · rw [List.getI_eq_default _ (by rw [List.length_replicate]; omega)]

/-- The start tape of the fold on `1ⁿ`. -/
def tape0 (a1 : Γ) (n : ℕ) : ℕ → Γ × Γ × Bool :=
  fun j => if j < n then (a1, default, false) else (default, default, false)

/-- The tape of the fold after its first step: `a0` on the lower track of cell `0`, marked. -/
def tape1 (a0 a1 : Γ) (n : ℕ) : ℕ → Γ × Γ × Bool :=
  Function.update (tape0 a1 n) 0 ((tape0 a1 n 0).1, a0, true)

theorem tapeRel_init (a0 a1 : Γ) (n : ℕ) :
    TapeRel (tape1 a0 a1 n) (Tape.mk₁ (a0 :: List.replicate n a1)) true 0 := by
  intro x
  rcases x with _ | x
  · have e : tape1 a0 a1 n 0 = ((tape0 a1 n 0).1, a0, true) := by
      rw [tape1, Function.update_self]
    rw [e]
    refine ⟨rfl, fun l => ?_⟩
    cases l
    · rw [show pos false 0 - pos true 0 = ((0 + 1 : ℕ) : ℤ) by simp only [pos]; omega,
        mk₁_nth_nat, List.getI_cons_succ, getI_replicate]
      show (tape0 a1 n 0).1 = _
      simp only [tape0]
      split_ifs <;> rfl
    · rw [show pos true 0 - pos true 0 = ((0 : ℕ) : ℤ) by simp only [pos]; omega,
        mk₁_nth_nat, List.getI_cons_zero]
      rfl
  · have e : tape1 a0 a1 n (x + 1) = tape0 a1 n (x + 1) := by
      rw [tape1, Function.update_of_ne (Nat.succ_ne_zero x)]
    rw [e]
    refine ⟨?_, fun l => ?_⟩
    · simp only [tape0]
      split_ifs <;> simp
    · cases l
      · rw [show pos false (x + 1) - pos true 0 = ((x + 1 + 1 : ℕ) : ℤ) by simp only [pos]; omega,
          mk₁_nth_nat, List.getI_cons_succ, getI_replicate]
        simp only [tape0]
        split_ifs <;> rfl
      · rw [show pos true (x + 1) - pos true 0 = -((x + 1 : ℕ) : ℤ) by simp only [pos]; omega,
          mk₁_nth_neg]
        simp only [tape0]
        split_ifs <;> rfl

end Start

section Run

/-- The first two steps of the fold (`init`, then `back`) reach the start of `M`. -/
theorem run_two (M : TM0.Machine Γ Λ) (a0 a1 : Γ) (n : ℕ) :
    ∃ c1 c2, (fold M a0 a1).run n 1 = some c1 ∧ (fold M a0 a1).halting c1.state = false ∧
      (fold M a0 a1).step c1 = some c2 ∧ Rel c2 (TM0.init (a0 :: List.replicate n a1)) := by
  have h1 : (fold M a0 a1).run n 1 = some ⟨.back default true, 0 + 1, tape1 a0 a1 n⟩ :=
    (fold M a0 a1).run_succ_of ((fold M a0 a1).run_zero n) (step_mk_right _ rfl)
  have h2 : (fold M a0 a1).step ⟨.back default true, 0 + 1, tape1 a0 a1 n⟩ =
      some ⟨.sim default true, 0, tape1 a0 a1 n⟩ := step_mk_left' _ rfl
  exact ⟨_, _, h1, rfl, h2, Exists.intro true ⟨rfl, tapeRel_init a0 a1 n⟩⟩

/-- Every configuration reached by `M` is simulated at some time. -/
theorem exists_rel (M : TM0.Machine Γ Λ) (a0 a1 : Γ) (n : ℕ) {b : TM0.Cfg Γ Λ}
    (hb : StateTransition.Reaches (TM0.step M) (TM0.init (a0 :: List.replicate n a1)) b) :
    ∃ t c, (fold M a0 a1).run n t = some c ∧ Rel c b := by
  unfold StateTransition.Reaches at hb
  induction hb with
  | refl =>
    obtain ⟨c1, c2, h1, -, h2, hr⟩ := run_two M a0 a1 n
    exact ⟨1 + 1, c2, (fold M a0 a1).run_succ_of h1 h2, hr⟩
  | tail _ hbc ih =>
    obtain ⟨t, c, hc, hr⟩ := ih
    rcases rel_step_some M a0 a1 hr (Option.mem_def.1 hbc) with
      ⟨c', h1, hr'⟩ | ⟨c', c'', h1, -, h2, hr'⟩
    · exact ⟨t + 1, c', (fold M a0 a1).run_succ_of hc h1, hr'⟩
    · exact ⟨t + 1 + 1, c'', (fold M a0 a1).run_succ_of ((fold M a0 a1).run_succ_of hc h1) h2,
        hr'⟩

/-- If `M` does not halt, then from time `1` on the fold simulates some configuration reached by
`M`, or is in a non-halting state and simulates one a step later. -/
theorem sim_or_back (M : TM0.Machine Γ Λ) (a0 a1 : Γ) (n : ℕ)
    (hM : ∀ b, StateTransition.Reaches (TM0.step M) (TM0.init (a0 :: List.replicate n a1)) b →
      TM0.step M b ≠ none)
    (t : ℕ) (ht : 1 ≤ t) :
    ∃ c b, (fold M a0 a1).run n t = some c ∧
      StateTransition.Reaches (TM0.step M) (TM0.init (a0 :: List.replicate n a1)) b ∧
      (Rel c b ∨ ((fold M a0 a1).halting c.state = false ∧
        ∃ c', (fold M a0 a1).step c = some c' ∧ Rel c' b)) := by
  induction t, ht using Nat.le_induction with
  | base =>
    obtain ⟨c1, c2, h1, hf, h2, hr⟩ := run_two M a0 a1 n
    exact ⟨c1, _, h1, Relation.ReflTransGen.refl, Or.inr ⟨hf, c2, h2, hr⟩⟩
  | succ t _ ih =>
    obtain ⟨c, b, hc, hreach, hr | ⟨-, c', h1, hr'⟩⟩ := ih
    · rcases hs : TM0.step M b with _ | b'
      · exact absurd hs (hM b hreach)
      · have hreach' : StateTransition.Reaches (TM0.step M)
            (TM0.init (a0 :: List.replicate n a1)) b' :=
          Relation.ReflTransGen.tail hreach (Option.mem_def.2 hs)
        rcases rel_step_some M a0 a1 hr hs with ⟨c', h1, hr'⟩ | ⟨c', c'', h1, hf, h2, hr'⟩
        · exact ⟨c', b', (fold M a0 a1).run_succ_of hc h1, hreach', Or.inl hr'⟩
        · exact ⟨c', b', (fold M a0 a1).run_succ_of hc h1, hreach', Or.inr ⟨hf, c'', h2, hr'⟩⟩
    · exact ⟨c', b, (fold M a0 a1).run_succ_of hc h1, hreach, Or.inl hr'⟩

end Run

end Fold

open Fold in
/-- **The fold halts on the unary input `1ⁿ` iff `M` halts on `a0 :: a1ⁿ`.** -/
theorem fold_haltsOn (M : TM0.Machine Γ Λ) (a0 a1 : Γ) (n : ℕ) :
    (fold M a0 a1).HaltsOn n ↔ (TM0.eval M (a0 :: List.replicate n a1)).Dom := by
  show _ ↔ (StateTransition.eval (TM0.step M) (TM0.init (a0 :: List.replicate n a1))).Dom
  rw [Part.dom_iff_mem]
  constructor
  · rintro ⟨t, c, hc, hh⟩
    by_contra hne
    have hM : ∀ b, StateTransition.Reaches (TM0.step M) (TM0.init (a0 :: List.replicate n a1)) b →
        TM0.step M b ≠ none :=
      fun b hb hs => hne ⟨b, StateTransition.mem_eval.2 ⟨hb, hs⟩⟩
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · rw [OMachine.run_zero] at hc
      cases hc
      exact Bool.false_ne_true hh
    · obtain ⟨c', b, hc', -, hr | ⟨hf, -⟩⟩ := sim_or_back M a0 a1 n hM t ht
      · rw [hc] at hc'
        cases hc'
        obtain ⟨lo, hs, -⟩ := hr
        rw [hs] at hh
        exact Bool.false_ne_true hh
      · rw [hc] at hc'
        cases hc'
        rw [hf] at hh
        exact Bool.false_ne_true hh
  · rintro ⟨b, hb⟩
    obtain ⟨hr, hn⟩ := StateTransition.mem_eval.1 hb
    obtain ⟨t, c, hc, hrel⟩ := exists_rel M a0 a1 n hr
    obtain ⟨c', hc', hs⟩ := rel_step_none M a0 a1 hrel hn
    exact ⟨t + 1, c', (fold M a0 a1).run_succ_of hc hc', by rw [hs]; rfl⟩

namespace Fold

/-! ### The run never ends -/

/-- The invariant of the fold's run from time `1` on: the configuration simulates some
configuration of `M`, or one step leads to such a configuration (the first half of a bounce), or
it is in state `halt`. -/
def Good (M : TM0.Machine Γ Λ) (a0 a1 : Γ) (c : OMachine.Cfg (FState Λ) (Γ × Γ × Bool)) :
    Prop :=
  (∃ b : TM0.Cfg Γ Λ, Rel c b) ∨
    (∃ (c' : OMachine.Cfg (FState Λ) (Γ × Γ × Bool)) (b : TM0.Cfg Γ Λ),
      (fold M a0 a1).step c = some c' ∧ Rel c' b) ∨
    c.state = .halt

/-- From a configuration satisfying the invariant, the fold makes a step (it does not move left
from cell `0`), into a configuration satisfying the invariant. -/
theorem good_step (M : TM0.Machine Γ Λ) (a0 a1 : Γ)
    {c : OMachine.Cfg (FState Λ) (Γ × Γ × Bool)} (h : Good M a0 a1 c) :
    ∃ c', (fold M a0 a1).step c = some c' ∧ Good M a0 a1 c' := by
  rcases h with ⟨b, hr⟩ | ⟨c', b, h1, hr⟩ | hh
  · rcases hs : TM0.step M b with _ | b'
    · obtain ⟨c', h1, hh⟩ := rel_step_none M a0 a1 hr hs
      exact ⟨c', h1, Or.inr (Or.inr hh)⟩
    · rcases rel_step_some M a0 a1 hr hs with ⟨c', h1, hr'⟩ | ⟨c', c'', h1, -, h2, hr'⟩
      · exact ⟨c', h1, Or.inl ⟨b', hr'⟩⟩
      · exact ⟨c', h1, Or.inr (Or.inl ⟨c'', b', h2, hr'⟩)⟩
  · exact ⟨c', h1, Or.inl ⟨b, hr⟩⟩
  · obtain ⟨s, i, τ⟩ := c
    change s = .halt at hh
    subst hh
    have htr : (fold M a0 a1).trans .halt (τ i) = (.halt, τ i, true) := rfl
    exact ⟨_, step_mk_right' _ htr, Or.inr (Or.inr rfl)⟩

/-- At every time `t + 1` the run is a configuration satisfying the invariant. -/
theorem run_succ_good (M : TM0.Machine Γ Λ) (a0 a1 : Γ) (n t : ℕ) :
    ∃ c, (fold M a0 a1).run n (t + 1) = some c ∧ Good M a0 a1 c := by
  induction t with
  | zero =>
    obtain ⟨c1, c2, h1, -, h2, hr⟩ := run_two M a0 a1 n
    exact ⟨c1, h1, Or.inr (Or.inl ⟨c2, _, h2, hr⟩)⟩
  | succ t ih =>
    obtain ⟨c, hc, hg⟩ := ih
    obtain ⟨c', h1, hg'⟩ := good_step M a0 a1 hg
    exact ⟨c', (fold M a0 a1).run_succ_of hc h1, hg'⟩

end Fold

/-- The fold follows the convention of Section 2.2 ("We use the standard convention that the
machine never moves left from cell 0; every machine can be converted into one with this property
and the same halting behaviour."): it never moves left from cell `0`, so its run never ends (on
every input, at every time, the run is a configuration). -/
theorem fold_run_isSome (M : TM0.Machine Γ Λ) (a0 a1 : Γ) (n t : ℕ) :
    ((fold M a0 a1).run n t).isSome = true := by
  cases t with
  | zero => rfl
  | succ t =>
    obtain ⟨c, hc, -⟩ := Fold.run_succ_good M a0 a1 n t
    rw [hc, Option.isSome_some]

end UPD.Compiler

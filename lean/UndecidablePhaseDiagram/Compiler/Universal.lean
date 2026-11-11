/-
# A universal machine with unary input (session 11): `exists_universal`

Section 2.2 of the paper (non-vacuity of Corollary B): there is a machine `U` (`Machine`,
`Statements.lean`: one-sided tape, unary input `1ⁿ`, a left move from cell `0` ends the run without
halting) such that `{n ≥ 1 | U halts on n}` is not computable. The route:

1. **A universal code that reads the bit length of its input.** The partial function
   `lenFun m = univFun (|bin m| - 1)` (`univFun k` = the value at `0` of the code numbered `k`;
   `bin m` = the binary digits of `m`) is partial recursive, hence computed by one code `lenCode`
   of Mathlib's sequential model `Turing.ToPartrec.Code` (`ToPartrec.Code.exists_code`). On
   `m = 2^{k+1} - 1` (the numeral `ones k`, `k + 1` digits `1`) it is `univFun k`.
2. **Mathlib's machine chain** (as in the forgetting project): `PartrecToTM2.tr` evaluates
   `lenCode` on the stack machine TM2, `TM2to1`, `TM1to0` give a `TM0` machine `M₀` on the finite
   alphabet `Γ₁` supported by the finite set `S₀`; `M₀` halts on `input m` iff `lenFun m` is
   defined (`eval_dom`). `M₀'` is `M₀` on the states of `S₀` (a finite type), with the same halting
   (`eval_restrict`).
3. **The input layout.** Mathlib's initial tape for the input `[2^{k+1} - 1]` is
   `a0 :: a1^{k+1}`: the bottom cell (bottom mark, `cons` on the main stack) followed by `k + 1`
   copies of one symbol (the digit `1` on the main stack) (`input_ones`). So the unary input
   `1^{k+1}` is already that tape, folded: `fold M₀' a0 a1` (`Compiler/Fold.lean`) halts on `1ⁿ`
   iff `M₀'` halts on `a0 :: a1ⁿ`.
4. **Numbering** (`Compiler/Encode.lean`): `univMachine` is the fold with numbered states and
   symbols; `univMachine_haltsOn`: it halts on `k + 1` iff the code numbered `k` halts on `0`;
   `univMachine_run_isSome`: it never moves left from cell `0` (the convention of Section 2.2).
5. **Non-computability** (`univMachine_universal`): `c ↦ encode c + 1` reduces Mathlib's halting
   problem at input `0` (`ComputablePred.halting_problem 0`) to `{n | 1 ≤ n ∧ U halts on n}`.

**[choice]** The universal code is chosen once by `Classical.choose` from Mathlib's existence
theorem; `univMachine` is a `noncomputable def` (a fixed object; only its existence is claimed).
-/
import UndecidablePhaseDiagram.Compiler.Encode
import UndecidablePhaseDiagram.Compiler.Fold
import Mathlib.Computability.TuringMachine.ToPartrec
import Mathlib.Computability.PartrecBasis
import Mathlib.Computability.Reduce
import Mathlib.Computability.Halting

set_option autoImplicit false

noncomputable section

namespace UPD.Compiler

open Turing

/-! ## Binary numerals

Copied from `C:/Infanox/fixed-noise-ergodicity-lean/FixedNoiseErgodicity/Compiler/Universal.lean`
(`bsucc`, `bin`, `pbits`, `nbits`, `pbits_succ`, `nbits_succ`, `bin_eq`, `bsucc_eq`,
`primrec_bsucc`, `primrec_bin`; namespace `FNE.Compiler` → `UPD.Compiler`). -/

/-- Binary successor on little-endian lists of bits. -/
def bsucc : List Bool → List Bool
  | [] => [true]
  | false :: l => true :: l
  | true :: l => false :: bsucc l

/-- The binary digits of `n` (least significant first): `n` successors of the empty list. -/
def bin (n : ℕ) : List Bool := bsucc^[n] []

/-- The digits of a positive binary numeral. -/
def pbits : PosNum → List Bool
  | .one => [true]
  | .bit0 p => false :: pbits p
  | .bit1 p => true :: pbits p

/-- The digits of a binary numeral. -/
def nbits : Num → List Bool
  | .zero => []
  | .pos p => pbits p

theorem pbits_succ (p : PosNum) : pbits p.succ = bsucc (pbits p) := by
  induction p with
  | one => rfl
  | bit1 p ih => simp only [PosNum.succ, pbits, bsucc, ih]
  | bit0 p => rfl

theorem nbits_succ (m : Num) : nbits m.succ = bsucc (nbits m) := by
  cases m with
  | zero => rfl
  | pos p => exact pbits_succ p

theorem bin_eq (n : ℕ) : bin n = nbits (n : Num) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hc : ((n + 1 : ℕ) : Num) = Num.succ (n : Num) := by
      rw [← Num.of_to_nat (Num.succ n), Num.succ_to_nat, Num.to_of_nat]
    rw [bin, Function.iterate_succ_apply', ← bin, ih, hc, nbits_succ]

theorem bsucc_eq (l : List Bool) :
    bsucc l = List.recOn l [true] (fun b l IH => cond b (false :: IH) (true :: l)) := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    cases b
    · rfl
    · show false :: bsucc l = _
      rw [ih]
      rfl

theorem primrec_bsucc : Primrec bsucc := by
  have h : Primrec₂ fun (_ : List Bool) (p : Bool × List Bool × List Bool) =>
      cond p.1 (false :: p.2.2) (true :: p.2.1) :=
    (Primrec.cond (Primrec.fst.comp Primrec.snd)
      (Primrec.list_cons.comp (Primrec.const false) (Primrec.snd.comp (Primrec.snd.comp
        Primrec.snd)))
      (Primrec.list_cons.comp (Primrec.const true) (Primrec.fst.comp (Primrec.snd.comp
        Primrec.snd)))).to₂
  exact (Primrec.list_rec Primrec.id (Primrec.const [true]) h).of_eq fun l => (bsucc_eq l).symm

theorem primrec_bin : Primrec bin :=
  (Primrec.nat_iterate Primrec.id (Primrec.const []) (primrec_bsucc.comp Primrec.snd).to₂).of_eq
    fun _ => rfl

/-! ## All-ones numerals -/

/-- The positive binary numeral with `k + 1` digits `1` (the number `2^{k+1} - 1`). -/
def ones : ℕ → PosNum
  | 0 => .one
  | k + 1 => .bit1 (ones k)

theorem pbits_ones (k : ℕ) : pbits (ones k) = List.replicate (k + 1) true := by
  induction k with
  | zero => rfl
  | succ k ih => rw [ones, pbits, ih]; rfl

/-- The binary digits of `2^{k+1} - 1`: `k + 1` ones. -/
theorem bin_ones (k : ℕ) : bin (ones k : ℕ) = List.replicate (k + 1) true := by
  rw [bin_eq, PosNum.of_to_nat]
  exact pbits_ones k

theorem trPosNum_ones (k : ℕ) :
    PartrecToTM2.trPosNum (ones k) = List.replicate (k + 1) PartrecToTM2.Γ'.bit1 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [ones, PartrecToTM2.trPosNum, ih]; rfl

/-- Mathlib's binary encoding of `2^{k+1} - 1`: `k + 1` digits `bit1`. -/
theorem trNat_ones (k : ℕ) :
    PartrecToTM2.trNat (ones k : ℕ) = List.replicate (k + 1) PartrecToTM2.Γ'.bit1 := by
  rw [PartrecToTM2.trNat, PosNum.of_to_nat]
  exact trPosNum_ones k

/-! ## A universal code that reads the bit length of its input -/

/-- The universal partial function: `n ↦` the value at `0` of the code numbered `n`. (Copied from
the forgetting project's `Compiler/Universal.lean`, `univFun`.) -/
def univFun : ℕ →. ℕ := fun n => (Denumerable.ofNat Nat.Partrec.Code n).eval 0

theorem univFun_partrec : Partrec univFun :=
  Nat.Partrec.Code.eval_part.comp (Computable.ofNat _) (Computable.const 0)

/-- The universal function read on the bit length: `m ↦ univFun (|bin m| - 1)`. -/
def lenFun : ℕ →. ℕ := fun m => univFun ((bin m).length - 1)

theorem lenFun_partrec : Partrec lenFun :=
  univFun_partrec.comp
    (Primrec.nat_sub.comp (Primrec.list_length.comp primrec_bin) (Primrec.const 1)).to_comp

/-- On `2^{k+1} - 1`, `lenFun` is `univFun k`. -/
theorem lenFun_ones (k : ℕ) : lenFun (ones k : ℕ) = univFun k := by
  simp only [lenFun, bin_ones, List.length_replicate, Nat.add_sub_cancel]

theorem exists_lenCode :
    ∃ c : ToPartrec.Code, ∀ m : ℕ, c.eval [m] = pure <$> lenFun m := by
  obtain ⟨c, hc⟩ := ToPartrec.Code.exists_code (Nat.Partrec'.part_iff₁.2 lenFun_partrec)
  exact ⟨c, fun m => hc ⟨[m], rfl⟩⟩

/-- **The universal code** (one fixed code of Mathlib's `ToPartrec` model, chosen once). -/
def lenCode : ToPartrec.Code := Classical.choose exists_lenCode

theorem lenCode_eval (m : ℕ) : lenCode.eval [m] = pure <$> lenFun m :=
  Classical.choose_spec exists_lenCode m

/-! ## Mathlib's machine chain for the universal code

Adapted from the forgetting project's `Compiler/Universal.lean` (`startInst`, `fintypeK'`, `Γ₁`,
`Λ₁`, `M₁`, `M₀`, `S₀`, `supports₀`, `input`, `init_eq`, `eval_dom`), with `lenCode` in place of
`univCode`. -/

open PartrecToTM2

/-- The start label of Mathlib's TM2 machine `tr` on the universal code, as the `Inhabited`
instance (the form of Mathlib's `tr_supports`). -/
@[reducible] def startInst : Inhabited Λ' := ⟨trNormal lenCode Cont'.halt⟩

attribute [local instance high] startInst

/-- The four stacks form a finite type (Mathlib derives only `DecidableEq` and `Inhabited`). -/
@[reducible] def fintypeK' : Fintype K' :=
  Fintype.ofList [K'.main, K'.rev, K'.aux, K'.stack] fun k => by cases k <;> simp

attribute [local instance] fintypeK'

/-- The tape alphabet of the one-tape simulations (`TM2to1.Γ'` for the four stacks). -/
abbrev Γ₁ := TM2to1.Γ' K' (fun _ => Γ')

/-- The labels of the TM1 simulation. -/
abbrev Λ₁ := TM2to1.Λ' K' (fun _ => Γ') Λ' (Option Γ')

/-- Mathlib's TM1 machine simulating `tr` (`TM2to1.tr`). -/
def M₁ : Λ₁ → TM1.Stmt Γ₁ Λ₁ (Option Γ') := TM2to1.tr tr

/-- Mathlib's TM0 machine simulating `M₁` (`TM1to0.tr`). -/
def M₀ : TM0.Machine Γ₁ (TM1to0.Λ' M₁) := TM1to0.tr M₁

/-- The finite set of reachable states of `M₀` (from Mathlib's supports). -/
def S₀ : Finset (TM1to0.Λ' M₁) :=
  TM1to0.trStmts M₁ (TM2to1.trSupp tr (codeSupp lenCode Cont'.halt))

theorem supports₀ : TM0.Supports M₀ ↑S₀ :=
  TM1to0.tr_supports M₁ (TM2to1.tr_supports tr (tr_supports lenCode Cont'.halt))

/-- The initial tape of `M₀` for the input `[m]`: Mathlib's `trList [m]` on the main stack. -/
def input (m : ℕ) : List Γ₁ := TM2to1.trInit K'.main (trList [m])

theorem init_eq (v : List ℕ) :
    (TM2.init K'.main (trList v) : TM2.Cfg (fun _ : K' => Γ') Λ' (Option Γ')) =
      init lenCode v := by
  simp only [TM2.init, init]
  congr 1
  funext k
  cases k <;> rfl

/-- `M₀` halts on `input m` iff `lenFun` is defined at `m`. -/
theorem eval_dom (m : ℕ) : (TM0.eval M₀ (input m)).Dom ↔ (lenFun m).Dom := by
  rw [M₀, TM1to0.tr_eval, input, M₁]
  erw [TM2to1.tr_eval_dom]
  change (StateTransition.eval (TM2.step tr) (TM2.init K'.main (trList [m]))).Dom ↔ _
  rw [init_eq, tr_eval, lenCode_eval]
  exact Iff.rfl

/-! ## `M₀` on the finite set of its states -/

/-- The states of `S₀`, a finite type. -/
abbrev Q₀ : Type := {q // q ∈ S₀}

/-- The start state of `M₀` lies in `S₀`. -/
instance instInhabitedQ₀ : Inhabited Q₀ := ⟨⟨default, supports₀.1⟩⟩

open Classical in
/-- A state of `M₀` as a state of `S₀` (the start state if it is not in `S₀`; never used there). -/
def toQ (q : TM1to0.Λ' M₁) : Q₀ := if h : q ∈ S₀ then ⟨q, h⟩ else default

theorem toQ_val {q : TM1to0.Λ' M₁} (h : q ∈ S₀) : (toQ q).1 = q := by
  simp [toQ, h]

/-- `M₀` on the states of `S₀`. -/
def M₀' : TM0.Machine Γ₁ Q₀ := fun q a => (M₀ q.1 a).map fun p => (toQ p.1, p.2)

/-- A configuration of `M₀'` as a configuration of `M₀`. -/
def liftC (c : TM0.Cfg Γ₁ Q₀) : TM0.Cfg Γ₁ (TM1to0.Λ' M₁) := ⟨c.q.1, c.Tape⟩

theorem step_liftC (c : TM0.Cfg Γ₁ Q₀) :
    TM0.step M₀ (liftC c) = (TM0.step M₀' c).map liftC := by
  obtain ⟨⟨q, hq⟩, T⟩ := c
  rcases h : M₀ q T.head with _ | ⟨q', s⟩
  · simp [TM0.step, liftC, M₀', h]
  · have hq' : q' ∈ S₀ := supports₀.2 (by rw [h]; exact rfl) hq
    simp [TM0.step, liftC, M₀', h, toQ_val hq']

theorem respects_liftC :
    StateTransition.Respects (TM0.step M₀') (TM0.step M₀) fun a b => liftC a = b := by
  intro a₁ a₂ hab
  subst hab
  rcases hs : TM0.step M₀' a₁ with _ | b₁
  · show TM0.step M₀ (liftC a₁) = none
    rw [step_liftC, hs]
    rfl
  · exact ⟨liftC b₁, rfl, Relation.TransGen.single (by rw [step_liftC, hs]; exact rfl)⟩

/-- `M₀'` halts on `l` iff `M₀` does. -/
theorem eval_restrict (l : List Γ₁) : (TM0.eval M₀' l).Dom ↔ (TM0.eval M₀ l).Dom := by
  have h := StateTransition.tr_eval' (TM0.step M₀') (TM0.step M₀) liftC respects_liftC
    (TM0.init l)
  change (StateTransition.eval (TM0.step M₀') (TM0.init l)).Dom ↔
    (StateTransition.eval (TM0.step M₀) (TM0.init l)).Dom
  have hi : liftC (TM0.init l) = (TM0.init l : TM0.Cfg Γ₁ (TM1to0.Λ' M₁)) := rfl
  rw [← hi, h]
  exact Iff.rfl

/-! ## The input layout -/

/-- The bottom cell of Mathlib's initial tape: the bottom mark and `cons` on the main stack. -/
def a0 : Γ₁ := (true, Function.update (fun _ => none) K'.main (some Γ'.cons))

/-- A digit `1` on the main stack. -/
def a1 : Γ₁ := (false, Function.update (fun _ => none) K'.main (some Γ'.bit1))

/-- Mathlib's initial tape for the input `[2^{k+1} - 1]` is `a0 :: a1^{k+1}`. -/
theorem input_ones (k : ℕ) : input (ones k : ℕ) = a0 :: List.replicate (k + 1) a1 := by
  simp only [input, TM2to1.trInit, trList, trNat_ones, List.reverse_append,
    List.reverse_cons, List.reverse_nil, List.nil_append, List.reverse_replicate,
    List.singleton_append, List.map_cons, List.map_replicate, List.headI_cons, List.tail_cons]
  erw [List.map_cons, List.headI_cons, List.tail_cons, List.map_replicate]
  rfl

theorem a1_ne : a1 ≠ default := by
  intro h
  have h' := congrArg (fun x : Bool × (K' → Option Γ') => x.2 K'.main) h
  change (some Γ'.bit1 : Option Γ') = none at h'
  exact Option.some_ne_none _ h'

/-! ## The universal machine -/

/-- The fold of `M₀'` (`Compiler/Fold.lean`) with the input layout `a0 :: a1ⁿ`. -/
abbrev UF : OMachine (FState Q₀) (Γ₁ × Γ₁ × Bool) := fold M₀' a0 a1

theorem UF_ne : UF.blank ≠ UF.one := fun h => a1_ne (congrArg Prod.fst h).symm

/-- **The universal machine**: the fold of `M₀'`, numbered (`Compiler/Encode.lean`). -/
def univMachine : Machine := UF.toMachine (fold_halting_init M₀' a0 a1) UF_ne

/-- **`univMachine` halts on `k + 1` iff the code numbered `k` halts on `0`.** -/
theorem univMachine_haltsOn (k : ℕ) : univMachine.HaltsOn (k + 1) ↔ (univFun k).Dom := by
  rw [univMachine, OMachine.toMachine_haltsOn, fold_haltsOn, eval_restrict, ← input_ones,
    eval_dom, lenFun_ones]

/-- **`univMachine` follows the convention of Section 2.2**: it never moves left from cell `0`, so
its run never ends (on every input, at every time, the run is a configuration). -/
theorem univMachine_run_isSome (n t : ℕ) : (univMachine.run n t).isSome = true := by
  rw [univMachine, OMachine.run_cfgMap, Option.isSome_map]
  exact fold_run_isSome M₀' a0 a1 n t

/-- **Section 2.2: `univMachine` is universal**: `{n | 1 ≤ n ∧ univMachine halts on n}` is not
computable (Mathlib's halting problem at input `0` reduces to it through `c ↦ encode c + 1`). -/
theorem univMachine_universal : Universal univMachine := by
  intro h
  refine ComputablePred.halting_problem 0 (ComputablePred.computable_of_manyOneReducible
    ⟨fun c => Encodable.encode c + 1, (Primrec.succ.comp Primrec.encode).to_comp, fun c => ?_⟩ h)
  show (c.eval 0).Dom ↔ 1 ≤ Encodable.encode c + 1 ∧ univMachine.HaltsOn (Encodable.encode c + 1)
  rw [univMachine_haltsOn, univFun, Denumerable.ofNat_encode]
  exact ⟨fun hd => ⟨Nat.succ_pos _, hd⟩, fun hd => hd.2⟩

end UPD.Compiler

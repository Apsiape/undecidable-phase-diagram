/-
Copyright (c) 2026 Seth Douglas, Nidhal Mghirbi. All rights reserved.
Formalization of: S. Douglas and N. Mghirbi, "An uncomputable phase diagram at positive
temperature for one classical lattice model", v1.1.0, Zenodo DOI 10.5281/zenodo.24124685.

# Statement file

This file defines, transparently and with no proofs of substance, every object that occurs in
Theorem A (`thm:main`, Section 7, together with `prf:windows` and the properties of `Φ` listed
after the proof) and Corollary B (`cor:undecidable`), and states them as the propositions
`TheoremA` and `CorollaryB`. They are proved as `UPD.theorem_A` and `UPD.corollary_B` in
`Main.lean` (the pattern QB ruled for the forgetting core: the statement file holds the
propositions, the last file the theorems). Every definition carries a docstring citing the paper
label it mirrors. Fidelity choices are marked **[choice]** and are collected in `BLUEPRINT.md`,
Part D.

Printed statement (Theorem A, `thm:main`). Fix a universal Turing machine `U`. There are a finite
set `𝔖` and a translation-invariant nearest-neighbour interaction `Φ` on `𝔖^{ℤ²}`, with every
local energy in `{0, 1, +∞}` and with `U` hard-coded, such that the following holds. Put
`λ_K = 2 ∑_{j<K} 1/((2j+1) 3^{2j+1})`, `β_n = n λ_{n+3}` and `J_n = (β_n - 1/1000, β_n + 1/1000)`
for `n ≥ 1`; these are pairwise disjoint intervals of positive numbers with rational endpoints
computable from `n`. For every `n ≥ 1` and every real `β ∈ J_n`:
(i) if `U` does not halt on input `n`, then `βΦ` has exactly one translation-invariant Gibbs
measure; (ii) if `U` halts on input `n`, then `βΦ` has at least two translation-invariant Gibbs
measures. Moreover, for every `β > 0`, `βΦ` has uncountably many Gibbs measures that are not
translation invariant.

Printed statement (Corollary B, `cor:undecidable`). The set
`𝒰 = {β ∈ ℚ_{>0} : βΦ has exactly one translation-invariant Gibbs measure}` is not decidable.
The map `n ↦ β_n` is computable, and `β_n ∈ 𝒰` if and only if `U` does not halt on `n`.
-/
import Mathlib.Tactic.DeriveFintype
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Computability.Halting
import Mathlib.Data.Set.Countable
import Mathlib.Data.List.Nodup

set_option autoImplicit false

-- The `deriving Fintype` handler builds the instance through nested sigma types; the records of
-- Section 4 have up to 21 fields, which exceeds the default instance-size budget.
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 2000000

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace UPD

/-! ## Section 2.1: interactions with hard constraints and Gibbs measures -/

/-- Section 2. The lattice `ℤ²` of sites `ξ`. -/
abbrev Plane := ℤ × ℤ

/-- Section 2. The unit vector `e₁ = (1, 0)`. -/
def e1 : Plane := (1, 0)

/-- Section 2. The unit vector `e₂ = (0, 1)`. -/
def e2 : Plane := (0, 1)

/-- Section 2.1. Configurations `Ω = 𝔖^{ℤ²}` over a site alphabet `S`. -/
abbrev Config (S : Type) := Plane → S

/-- Section 2. The shift `T_a`: `(T_a ω)(ξ) = ω(ξ - a)`. On measures, `T_a μ = μ ∘ T_a⁻¹` is
`μ.map (shift a)`. -/
def shift {S : Type} (a : Plane) (ω : Config S) : Config S := fun ξ => ω (ξ - a)

/-- `set:def-interaction`. An interaction: a family `Φ_A : Ω → [0, +∞]` indexed by the finite sets
`A ⊆ ℤ²`. That `Φ_A(ω)` depends only on `ω_A` is the property `IsInteraction`. -/
abbrev Interaction (S : Type) := Finset Plane → Config S → ℝ≥0∞

/-- `set:def-interaction`. `Φ_A(ω)` depends only on `ω_A`. -/
def IsInteraction {S : Type} (Φ : Interaction S) : Prop :=
  ∀ (A : Finset Plane) (ω ω' : Config S), (∀ ξ ∈ A, ω ξ = ω' ξ) → Φ A ω = Φ A ω'

/-- `set:def-interaction`. Translation invariance: `Φ_{A+a}(T_a ω) = Φ_A(ω)`. -/
def IsTranslationInvariant {S : Type} (Φ : Interaction S) : Prop :=
  ∀ (A : Finset Plane) (a : Plane) (ω : Config S),
    Φ (A.image (fun ξ => ξ + a)) (shift a ω) = Φ A ω

/-- `set:def-interaction`. Nearest-neighbour: `Φ_A = 0` unless `A` is a single site or a pair
`{ξ, ξ + e_i}`. -/
def IsNearestNeighbour {S : Type} (Φ : Interaction S) : Prop :=
  ∀ A : Finset Plane, (¬ ∃ ξ, A = {ξ}) → (¬ ∃ ξ, A = {ξ, ξ + e1}) →
    (¬ ∃ ξ, A = {ξ, ξ + e2}) → ∀ ω, Φ A ω = 0

/-- `set:def-interaction`. `ω` is legal if `Φ_A(ω) < ∞` for every `A`; the legal configurations
form `X_Φ = {ω | IsLegal Φ ω}`. -/
def IsLegal {S : Type} (Φ : Interaction S) (ω : Config S) : Prop :=
  ∀ A : Finset Plane, Φ A ω < ⊤

/-- `set:def-interaction`. The energy `H_Λ(ω) = ∑_{A ∩ Λ ≠ ∅} Φ_A(ω) ∈ [0, +∞]`, a sum over all
finite sets `A` meeting `Λ` (an unconditional sum in `[0, +∞]`). -/
def energy {S : Type} (Φ : Interaction S) (Λ : Finset Plane) (ω : Config S) : ℝ≥0∞ :=
  ∑' A : {A : Finset Plane // (A ∩ Λ).Nonempty}, Φ A.1 ω

/-- `set:def-gibbs`. The Boltzmann factor `e^{-β H}` of an energy `H ∈ [0, +∞]`, with
`e^{-∞} = 0`. -/
def boltzmann (β : ℝ) (H : ℝ≥0∞) : ℝ :=
  if H = ⊤ then 0 else Real.exp (-(β * H.toReal))

/-- `set:def-gibbs`. The configuration equal to `ζ` on `Λ` and to `ω` off `Λ`. As `ζ` ranges over
`Λ → 𝔖`, it ranges once over the configurations `η` with `η_{Λᶜ} = ω_{Λᶜ}`. -/
def fill {S : Type} (ω : Config S) (Λ : Finset Plane) (ζ : Λ → S) : Config S :=
  fun ξ => if h : ξ ∈ Λ then ζ ⟨ξ, h⟩ else ω ξ

/-- `set:def-gibbs`. The partition function `Z_Λ(ω) = ∑_{η : η_{Λᶜ} = ω_{Λᶜ}} e^{-β H_Λ(η)}`. -/
def partitionFunction {S : Type} [Fintype S] (β : ℝ) (Φ : Interaction S) (Λ : Finset Plane)
    (ω : Config S) : ℝ :=
  ∑ ζ : Λ → S, boltzmann β (energy Φ Λ (fill ω Λ ζ))

/-- `set:def-gibbs`. The Gibbs kernel applied to a function:
`(γ_Λ F)(ω) = ∑_η γ_Λ(η | ω) F(η)` with
`γ_Λ(η | ω) = 𝟙[η_{Λᶜ} = ω_{Λᶜ}] e^{-β H_Λ(η)} / Z_Λ(ω)`.
**[choice]** It is defined at every `ω`; the paper evaluates it only at legal `ω`, where
`Z_Λ(ω) > 0`, and Gibbs measures give the legal configurations full measure. -/
def kernelApply {S : Type} [Fintype S] (β : ℝ) (Φ : Interaction S) (Λ : Finset Plane)
    (F : Config S → ℝ) (ω : Config S) : ℝ :=
  (∑ ζ : Λ → S, boltzmann β (energy Φ Λ (fill ω Λ ζ)) * F (fill ω Λ ζ)) /
    partitionFunction β Φ Λ ω

/-- `set:def-gibbs`. A Gibbs measure for `βΦ`: a probability measure `μ` on `Ω` with
`μ(X_Φ) = 1` such that `∫ F dμ = ∫ (γ_Λ F) dμ` for every finite `Λ` and every bounded measurable
`F`. `Ω` carries the product σ-algebra, which is the Borel σ-algebra of the product topology
(the alphabet is finite and discrete, the index set countable).
**[choice]** `F` is real-valued. -/
def IsGibbs {S : Type} [Fintype S] [MeasurableSpace S] (β : ℝ) (Φ : Interaction S)
    (μ : Measure (Config S)) : Prop :=
  IsProbabilityMeasure μ ∧ μ {ω | IsLegal Φ ω} = 1 ∧
    ∀ (Λ : Finset Plane) (F : Config S → ℝ), Measurable F → (∃ C : ℝ, ∀ ω, |F ω| ≤ C) →
      ∫ ω, F ω ∂μ = ∫ ω, kernelApply β Φ Λ F ω ∂μ

/-- `set:def-gibbs`. A measure is translation invariant if `T_a μ = μ` for all `a ∈ ℤ²`. -/
def IsTranslationInvariantMeasure {S : Type} [MeasurableSpace S] (μ : Measure (Config S)) :
    Prop :=
  ∀ a : Plane, μ.map (shift a) = μ

/-! ## Section 2.2: Turing machines -/

/-- Section 2.2. A deterministic Turing machine with a one-sided tape (cells `0, 1, 2, …`).
**[choice]** Finite encoding: the states are `Fin (numStates + 1)` with initial state `0`; the
tape symbols are `Fin (numSymbols + 2)`, with blank `0` and the symbol `1`; the halting states are
those with `halting q = true`; `trans q γ = (q', γ', D)`: write `γ'`, go to `q'`, move one cell
right if `D = true` and one cell left if `D = false`. The initial state is not halting (the paper's
machine `M` enters the state `(q⁰_U, run)`, which exists only for a non-halting `q⁰_U`).
Every machine of Section 2.2 with a non-halting initial state has such an encoding. -/
structure Machine where
  /-- the states are `Fin (numStates + 1)` -/
  numStates : ℕ
  /-- the tape symbols are `Fin (numSymbols + 2)` -/
  numSymbols : ℕ
  /-- the halting states -/
  halting : Fin (numStates + 1) → Bool
  /-- the transition function -/
  trans : Fin (numStates + 1) → Fin (numSymbols + 2) →
    Fin (numStates + 1) × Fin (numSymbols + 2) × Bool
  /-- the initial state `0` is not halting -/
  init_not_halting : halting 0 = false

namespace Machine

/-- The states of a machine. -/
abbrev State (U : Machine) := Fin (U.numStates + 1)

/-- The tape symbols of a machine; `0` is the blank `⊔` and `1` is the symbol `1`. -/
abbrev Symbol (U : Machine) := Fin (U.numSymbols + 2)

/-- A configuration: state, head cell, one-sided tape. -/
structure Cfg (U : Machine) where
  /-- the state -/
  state : U.State
  /-- the head cell -/
  head : ℕ
  /-- the tape -/
  tape : ℕ → U.Symbol

/-- Section 2.2. One step: write, change state, move one cell left or right.
**[choice]** A move left from cell `0` ends the run without halting (`none`); the paper's
convention is that the machine never makes such a move, and then this case never occurs. -/
def step (U : Machine) (c : U.Cfg) : Option U.Cfg :=
  let t := U.trans c.state (c.tape c.head)
  if t.2.2 then some ⟨t.1, c.head + 1, Function.update c.tape c.head t.2.1⟩
  else if c.head = 0 then none
  else some ⟨t.1, c.head - 1, Function.update c.tape c.head t.2.1⟩

/-- Section 2.2. The start on input `n`: initial state, head on cell `0`, cells `0, …, n-1` hold
the symbol `1`, all other cells are blank. -/
def start (U : Machine) (n : ℕ) : U.Cfg :=
  ⟨0, 0, fun j => if j < n then 1 else 0⟩

/-- The configuration after `t` steps on input `n` (`none` once the run has ended by a move left
from cell `0`). -/
def run (U : Machine) (n : ℕ) : ℕ → Option U.Cfg
  | 0 => some (U.start n)
  | t + 1 => (U.run n t).bind U.step

/-- Section 2.2. `U` halts on input `n` if, started on input `n`, it enters a halting state. -/
def HaltsOn (U : Machine) (n : ℕ) : Prop :=
  ∃ (t : ℕ) (c : U.Cfg), U.run n t = some c ∧ U.halting c.state = true

end Machine

/-! ## Section 3 and Appendix A: the scaffold (data) -/

namespace Scaffold

/-- App. A: the vertical atoms `r₀, r₂, g₀, g₂` (`r` red, `g` green). -/
inductive VAtom where
  | r0 | r2 | g0 | g2
  deriving DecidableEq, Repr, Fintype

/-- App. A: the horizontal atoms `r₁, r₃, g₁, g₃`. -/
inductive HAtom where
  | r1 | r3 | g1 | g3
  deriving DecidableEq, Repr, Fintype

/-- The atoms `r₀, r₂` are red. -/
def VAtom.IsRed : VAtom → Bool
  | .r0 => true | .r2 => true | .g0 => false | .g2 => false

/-- The atoms `r₁, r₃` are red. -/
def HAtom.IsRed : HAtom → Bool
  | .r1 => true | .r3 => true | .g1 => false | .g3 => false

/-- §3.2: the thin types `a, b, c, d`. -/
inductive Thin where
  | a | b | c | d
  deriving DecidableEq, Repr, Fintype

/-- §3.2: the four corners `∠a, ∠b, ∠c, ∠d`. -/
inductive Corner where
  | a | b | c | d
  deriving DecidableEq, Repr, Fintype

/-- §3.2: a thick type is a corner or one of the sixteen lines `⟨α, α'⟩`, with a vertical atom
`α` and a horizontal atom `α'`. -/
inductive Thick where
  | corner (k : Corner)
  | line (α : VAtom) (α' : HAtom)
  deriving DecidableEq, Repr, Fintype

/-- §3.2: the black types `A, B, C, D, E`. -/
inductive Black where
  | A | B | C | D | E
  deriving DecidableEq, Repr, Fintype

/-- `tab:edges`: north endpoints of the thin types. -/
def Thin.epN : Thin → VAtom
  | .a => .r0 | .b => .g0 | .c => .r2 | .d => .g2

/-- `tab:edges`: south endpoints of the thin types. -/
def Thin.epS : Thin → VAtom
  | .a => .g2 | .b => .r2 | .c => .g0 | .d => .r0

/-- `tab:edges`: east endpoints of the thin types. -/
def Thin.epE : Thin → HAtom
  | .a => .r1 | .b => .g1 | .c => .g3 | .d => .r3

/-- `tab:edges`: west endpoints of the thin types. -/
def Thin.epW : Thin → HAtom
  | .a => .g3 | .b => .r3 | .c => .r1 | .d => .g1

/-- `tab:edges`: north endpoints of the corners. -/
def Corner.epN : Corner → VAtom
  | .a => .g2 | .b => .r0 | .c => .r2 | .d => .g0

/-- `tab:edges`: south endpoints of the corners. -/
def Corner.epS : Corner → VAtom
  | .a => .r0 | .b => .g2 | .c => .g0 | .d => .r2

/-- `tab:edges`: east endpoints of the corners. -/
def Corner.epE : Corner → HAtom
  | .a => .r3 | .b => .r1 | .c => .g3 | .d => .g1

/-- `tab:edges`: west endpoints of the corners. -/
def Corner.epW : Corner → HAtom
  | .a => .g1 | .b => .g3 | .c => .r1 | .d => .r3

/-- `tab:edges`: north endpoint of a thick type; a line `⟨α, α'⟩` has `α`. -/
def Thick.epN : Thick → VAtom
  | .corner k => k.epN
  | .line α _ => α

/-- `tab:edges`: south endpoint of a thick type; a line `⟨α, α'⟩` has `α`. -/
def Thick.epS : Thick → VAtom
  | .corner k => k.epS
  | .line α _ => α

/-- `tab:edges`: east endpoint of a thick type; a line `⟨α, α'⟩` has `α'`. -/
def Thick.epE : Thick → HAtom
  | .corner k => k.epE
  | .line _ α' => α'

/-- `tab:edges`: west endpoint of a thick type; a line `⟨α, α'⟩` has `α'`. -/
def Thick.epW : Thick → HAtom
  | .corner k => k.epW
  | .line _ α' => α'

/-- The thick type is a corner. -/
def Thick.IsCorner : Thick → Bool
  | .corner _ => true
  | .line _ _ => false

/-- §3.2: a *red crossing* is a line whose two atoms are red. -/
def Thick.IsRedCrossing : Thick → Bool
  | .corner _ => false
  | .line α α' => α.IsRed && α'.IsRed

/-- `tab:edges`: north bits of the black types (`true` is `1`). -/
def Black.bitN : Black → Bool
  | .A => false | .B => true | .C => true | .D => true | .E => false

/-- `tab:edges`: south bits of the black types. -/
def Black.bitS : Black → Bool
  | .A => true | .B => false | .C => false | .D => true | .E => false

/-- `tab:edges`: east bits of the black types. -/
def Black.bitE : Black → Bool
  | .A => false | .B => false | .C => true | .D => true | .E => true

/-- `tab:edges`: west bits of the black types. -/
def Black.bitW : Black → Bool
  | .A => true | .B => false | .C => true | .D => false | .E => false

/-- §3.2: a triple `(θ, κ, ψ)` of a thin, a thick and a black type. -/
structure Formal where
  /-- the thin type `θ` -/
  thin : Thin
  /-- the thick type `κ` -/
  thick : Thick
  /-- the black type `ψ` -/
  black : Black
  deriving DecidableEq, Repr, Fintype

/-- `tab:alphabet`, row by row: the base set `𝕆`. A row `θ, line, ψ, condition` admits the lines
`⟨α, α'⟩` satisfying the condition; a row `θ, corner, A` admits the four corners. -/
def Formal.inO : Formal → Bool
  | ⟨.a, .corner _, .A⟩ => true
  | ⟨.a, .line α _, .B⟩ => α != .r0
  | ⟨.a, .line α _, .C⟩ => α != .r2
  | ⟨.a, .line _ α', .D⟩ => α' != .r3
  | ⟨.a, .line _ α', .E⟩ => α' != .r1
  | ⟨.b, .corner _, .A⟩ => true
  | ⟨.c, .line α _, .B⟩ => α != .r0
  | ⟨.c, .line α _, .C⟩ => α != .r2
  | ⟨.d, .line _ α', .D⟩ => α' != .r3
  | ⟨.d, .line _ α', .E⟩ => α' != .r1
  | _ => false

/-- `scf:def-base`: the colour of `(θ, κ, ψ)` on the north side, `(∂_N θ, ∂_N κ, ∂_N ψ)`. -/
def Formal.colN (t : Formal) : VAtom × VAtom × Bool := (t.thin.epN, t.thick.epN, t.black.bitN)

/-- `scf:def-base`: the colour on the south side. -/
def Formal.colS (t : Formal) : VAtom × VAtom × Bool := (t.thin.epS, t.thick.epS, t.black.bitS)

/-- `scf:def-base`: the colour on the east side. -/
def Formal.colE (t : Formal) : HAtom × HAtom × Bool := (t.thin.epE, t.thick.epE, t.black.bitE)

/-- `scf:def-base`: the colour on the west side. -/
def Formal.colW (t : Formal) : HAtom × HAtom × Bool := (t.thin.epW, t.thick.epW, t.black.bitW)

/-- `scf:def-ruler`: a tuple `(θ, κ, ψ, χ₁, χ₂)`: a triple and two bits (`false` is `0`). -/
structure Letter where
  /-- the base `(θ, κ, ψ)` -/
  base : Formal
  /-- the column bit `χ₁` -/
  b1 : Bool
  /-- the row bit `χ₂` -/
  b2 : Bool
  deriving DecidableEq, Repr, Fintype

/-- `scf:def-ruler`: the scaffold `𝔸`: `(θ, κ, ψ) ∈ 𝕆` and (R1) if `θ ∈ {b, c}` then `χ₁ = 0`;
(R2) if `θ ∈ {b, d}` then `χ₂ = 0`; (R3) if `κ` is a corner then `χ₁ = χ₂`; (R4) if `κ` is a red
crossing then `χ₁ ≠ χ₂`. -/
def Letter.InA (x : Letter) : Prop :=
  x.base.inO = true ∧
  ((x.base.thin = .b ∨ x.base.thin = .c) → x.b1 = false) ∧
  ((x.base.thin = .b ∨ x.base.thin = .d) → x.b2 = false) ∧
  (x.base.thick.IsCorner = true → x.b1 = x.b2) ∧
  (x.base.thick.IsRedCrossing = true → x.b1 ≠ x.b2)

instance : DecidablePred Letter.InA := fun x => by unfold Letter.InA; infer_instance

/-- `scf:def-ruler`: the north colour of a letter: that of its base and the column bit `χ₁`. -/
def Letter.colN (x : Letter) : (VAtom × VAtom × Bool) × Bool := (x.base.colN, x.b1)

/-- `scf:def-ruler`: the south colour: that of its base and the column bit `χ₁`. -/
def Letter.colS (x : Letter) : (VAtom × VAtom × Bool) × Bool := (x.base.colS, x.b1)

/-- `scf:def-ruler`: the east colour: that of its base and the row bit `χ₂`. -/
def Letter.colE (x : Letter) : (HAtom × HAtom × Bool) × Bool := (x.base.colE, x.b2)

/-- `scf:def-ruler`: the west colour: that of its base and the row bit `χ₂`. -/
def Letter.colW (x : Letter) : (HAtom × HAtom × Bool) × Bool := (x.base.colW, x.b2)

/-- The letters of `𝔸` (`|𝔸| = 276`, `tab:letters`). -/
abbrev LetterA := {x : Letter // x.InA}

/-- `scf:def-quarter`: a quarter `(ς, 𝔞) ∈ {0,1}² × 𝔸`, with quadrant `ς = (ς₁, ς₂)` and parent
`𝔞`. **[choice]** `ς₁, ς₂` are `Bool` (`false` is `0`). -/
structure Quarter where
  /-- the quadrant `ς = (ς₁, ς₂)` -/
  quad : Bool × Bool
  /-- the parent `𝔞` -/
  parent : LetterA
  deriving DecidableEq, Fintype

/-- `scf:def-quarter`: east and west colours of quarters. **[choice]** The marks `∘` and `•` are
the two summands: `(∘, 𝔞, b)` is `(inl 𝔞, b)` and `(•, 𝔞_X, b)` is `(inr 𝔞_X, b)`. -/
abbrev QColH := (Letter ⊕ ((HAtom × HAtom × Bool) × Bool)) × Bool

/-- `scf:def-quarter`: north and south colours of quarters (marks as in `QColH`). -/
abbrev QColV := (Letter ⊕ ((VAtom × VAtom × Bool) × Bool)) × Bool

/-- `scf:def-quarter`: east colour `(∘, 𝔞, ς₂)` if `ς₁ = 0` and `(•, 𝔞_E, ς₂)` if `ς₁ = 1`. -/
def Quarter.colE (q : Quarter) : QColH :=
  if q.quad.1 = false then (.inl q.parent.1, q.quad.2) else (.inr q.parent.1.colE, q.quad.2)

/-- `scf:def-quarter`: west colour `(∘, 𝔞, ς₂)` if `ς₁ = 1` and `(•, 𝔞_W, ς₂)` if `ς₁ = 0`. -/
def Quarter.colW (q : Quarter) : QColH :=
  if q.quad.1 = true then (.inl q.parent.1, q.quad.2) else (.inr q.parent.1.colW, q.quad.2)

/-- `scf:def-quarter`: north colour `(∘, 𝔞, ς₁)` if `ς₂ = 0` and `(•, 𝔞_N, ς₁)` if `ς₂ = 1`. -/
def Quarter.colN (q : Quarter) : QColV :=
  if q.quad.2 = false then (.inl q.parent.1, q.quad.1) else (.inr q.parent.1.colN, q.quad.1)

/-- `scf:def-quarter`: south colour `(∘, 𝔞, ς₁)` if `ς₂ = 1` and `(•, 𝔞_S, ς₁)` if `ς₂ = 0`. -/
def Quarter.colS (q : Quarter) : QColV :=
  if q.quad.2 = true then (.inl q.parent.1, q.quad.1) else (.inr q.parent.1.colS, q.quad.1)

/-- The thick type `κ` of the parent of a quarter. -/
def Quarter.thick (q : Quarter) : Thick := q.parent.1.base.thick

/-- `scf:def-walls`: the vertical red atom of a thick type, the red value among its north and
south endpoints, if any. **[choice]** The north endpoint is read first; the paper notes that on
each axis the red endpoints carry at most one atom value, so the order is immaterial. -/
def Thick.vRedAtom (κ : Thick) : Option VAtom :=
  if κ.epN.IsRed then some κ.epN else if κ.epS.IsRed then some κ.epS else none

/-- `scf:def-walls`: the horizontal red atom of a thick type, the red value among its east and
west endpoints, if any. -/
def Thick.hRedAtom (κ : Thick) : Option HAtom :=
  if κ.epE.IsRed then some κ.epE else if κ.epW.IsRed then some κ.epW else none

/-- `scf:def-walls`: the quarter lies on a *vertical red path*: `κ` has a vertical red atom,
`ς₁ = 1` if this atom is `r₀` and `ς₁ = 0` if it is `r₂`, and, when `κ` is a corner, `ς₂ = 1`
if its north endpoint is red and `ς₂ = 0` if its south endpoint is red. -/
def Quarter.OnVRedPath (q : Quarter) : Prop :=
  q.thick.vRedAtom.isSome ∧
  (q.thick.vRedAtom = some .r0 → q.quad.1 = true) ∧
  (q.thick.vRedAtom = some .r2 → q.quad.1 = false) ∧
  (q.thick.IsCorner = true →
    (q.thick.epN.IsRed = true → q.quad.2 = true) ∧ (q.thick.epS.IsRed = true → q.quad.2 = false))

/-- `scf:def-walls`: the quarter lies on a *horizontal red path*: `κ` has a horizontal red atom,
`ς₂ = 1` if this atom is `r₁` and `ς₂ = 0` if it is `r₃`, and, when `κ` is a corner, `ς₁ = 1`
if its east endpoint is red and `ς₁ = 0` if its west endpoint is red. -/
def Quarter.OnHRedPath (q : Quarter) : Prop :=
  q.thick.hRedAtom.isSome ∧
  (q.thick.hRedAtom = some .r1 → q.quad.2 = true) ∧
  (q.thick.hRedAtom = some .r3 → q.quad.2 = false) ∧
  (q.thick.IsCorner = true →
    (q.thick.epE.IsRed = true → q.quad.1 = true) ∧ (q.thick.epW.IsRed = true → q.quad.1 = false))

instance : DecidablePred Quarter.OnVRedPath := fun q => by
  unfold Quarter.OnVRedPath; infer_instance

instance : DecidablePred Quarter.OnHRedPath := fun q => by
  unfold Quarter.OnHRedPath; infer_instance

end Scaffold

open Scaffold

/-! ## Section 4: the interaction. Small value sets -/

/-- (F2): the sides `L, R` of vertical walls. -/
inductive LR where
  | L | R
  deriving DecidableEq, Repr, Fintype

/-- (F2): the sides `B, T` (bottom, top) of horizontal walls. -/
inductive BT where
  | B | T
  deriving DecidableEq, Repr, Fintype

/-- (F3): the entries `cell`, `wall` of event tags. -/
inductive Ev where
  | cell | wall
  deriving DecidableEq, Repr, Fintype

/-- (F7): a spin `σ ∈ {+1, -1}`. -/
inductive Spin where
  | plus | minus
  deriving DecidableEq, Repr, Fintype

/-- `int:sub-predicates`: `VW(𝔮) ∈ {-, L, R}`: `L` (`R`) if `𝔮` lies on a light vertical wall as a
left (right) side, `-` (`none`) otherwise. A quarter on a vertical red path is a left side if its
atom is `r₀` and a right side if it is `r₂`; the path is a light wall if moreover `χ₁(𝔞) = 1`. -/
def Scaffold.Quarter.VW (q : Quarter) : Option LR :=
  if q.OnVRedPath ∧ q.parent.1.b1 = true then
    (if q.thick.vRedAtom = some .r0 then some .L else some .R)
  else none

/-- `int:sub-predicates`: `HW(𝔮) ∈ {-, B, T}`: `B` (`T`) if `𝔮` lies on a light horizontal wall
as a bottom (top) side, `-` (`none`) otherwise. A quarter on a horizontal red path is a bottom side
if its atom is `r₁` and a top side if it is `r₃`; the path is a light wall if moreover
`χ₂(𝔞) = 1`. -/
def Scaffold.Quarter.HW (q : Quarter) : Option BT :=
  if q.OnHRedPath ∧ q.parent.1.b2 = true then
    (if q.thick.hRedAtom = some .r1 then some .B else some .T)
  else none

/-! ## Appendix C: the machine `M` built from `U` -/

section MachineM

variable (U : Machine)

/-- App. C: a tape symbol `(𝗁, 𝗓, 𝗎, 𝗉, 𝗇, 𝗆⁻, 𝗆⁺) ∈ Γ_M = {0,1} × {0,1} × Γ_U × {0,1} × {0,1,2} ×
{0,1} × {0,1}` of `M`. -/
structure TapeM where
  /-- the one-hot marker track `𝗁` -/
  h : Bool
  /-- the mark `𝗓` of cell `0` -/
  z : Bool
  /-- the tape `𝗎` of `U` -/
  u : U.Symbol
  /-- the marks `𝗉` -/
  p : Bool
  /-- the label in unary, `𝗇 ∈ {0, 1, 2}` -/
  n : Fin 3
  /-- the mask track `𝗆⁻` -/
  mm : Bool
  /-- the mask track `𝗆⁺` -/
  mp : Bool
  deriving DecidableEq, Fintype

/-- App. C: the states of `M`: `P₀, …, P₁₀`; `S₁, …, S₆`; `H₀, H₁`; `(q, run)` for the non-halting
states `q` of `U`; `E₀`, `E₁`, `E₂^{(c)}` (`c ∈ [1,20]`), `E₃`, `E₄^{(c)}` (`c ∈ [1,4]`),
`E₅^{(c)}` (`c ∈ [1,5]`), `E₆`; `q_acc`, `q_fail`.
**[choice]** `E2 i`, `E4 i`, `E5 i` stand for `E₂^{(i+1)}`, `E₄^{(i+1)}`, `E₅^{(i+1)}`; `H π`
stands for `H₀` (`π = false`) and `H₁` (`π = true`). -/
inductive StateM where
  | P (k : Fin 11)
  | S1 | S2 | S3 | S4 | S5 | S6
  | H (π : Bool)
  | run (q : {q : U.State // U.halting q = false})
  | E0 | E1
  | E2 (i : Fin 20)
  | E3
  | E4 (i : Fin 4)
  | E5 (i : Fin 5)
  | E6
  | acc | fail
  deriving DecidableEq, Fintype

/-- App. C: head moves `+1` (up), `-1` (down), `0` (stay). -/
inductive Mv where
  | up | down | stay
  deriving DecidableEq, Repr, Fintype

/-- `int:sub-fields`, App. C: the cell contents `𝒮_M = Γ_M × (Q_M ∪ {·})`; the second component
is `none` for the mark `·` (the head is elsewhere). -/
abbrev CellM := TapeM U × Option (StateM U)

/-- `tab:program`: the program of `M`. `programM U q g = some (q', g', D)`: in state `q` reading
`g`, write `g'`, move by `D`, enter `q'`. `none`: the pair is not covered by the table. Entries
separated by "/" in the table are alternative cases, matched in order. In the row of
`(q, run)`, `D = +1` if `U` moves right and `D = -1` if it moves left. -/
def programM : StateM U → TapeM U → Option (StateM U × TapeM U × Mv)
  | .P k, g =>
    if g.h = false then
      some (.P ⟨min (k.val + 1) 10, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩,
        (if 2 ≤ k.val then { g with p := true } else g), .up)
    else if k.val ≤ 9 then some (.fail, g, .stay)
    else some (.S1, g, .stay)
  | .S1, g =>
    if g.z = false then some (.S1, g, .down) else some (.H false, { g with n := 1 }, .stay)
  | .H π, g =>
    if g.h = false ∧ g.p = false then some (.H π, g, .up)
    else if π = false ∧ g.h = false ∧ g.p = true then some (.H true, g, .up)
    else if π = true ∧ g.h = false ∧ g.p = true then some (.H false, { g with p := false }, .up)
    else if g.h = true then some ((if π = false then .S2 else .S4), g, .stay)
    else none
  | .S2, g => if g.z = false then some (.S2, g, .down) else some (.S3, g, .stay)
  | .S3, g =>
    if g.n = 1 then some (.S3, g, .up)
    else if g.n = 0 then some (.S1, { g with n := 1 }, .stay)
    else none
  | .S4, g => if g.z = false then some (.S4, g, .down) else some (.S5, g, .stay)
  | .S5, g =>
    if g.n = 1 then some (.S5, { g with u := 1 }, .up)
    else if g.n = 0 then some (.S6, g, .stay)
    else none
  | .S6, g =>
    if g.z = false then some (.S6, g, .down)
    else some (.run ⟨0, U.init_not_halting⟩, g, .stay)
  | .run q, g =>
    let t := U.trans q.1 g.u
    some ((if h : U.halting t.1 = true then .E0 else .run ⟨t.1, by simpa using h⟩),
      { g with u := t.2.1 }, (if t.2.2 then .up else .down))
  | .E0, g => if g.z = false then some (.E0, g, .down) else some (.E1, g, .stay)
  | .E1, g =>
    if g.n = 2 then some (.E1, g, .up)
    else if g.n = 1 then some (.E2 19, { g with n := 2 }, .stay)
    else some (.E3, g, .stay)
  | .E2 i, g =>
    if g.mm = true then some (.E2 i, g, .up)
    else if 1 ≤ i.val then
      some (.E2 ⟨i.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩,
        { g with mm := true, mp := true }, .up)
    else some (.E0, { g with mm := true, mp := true }, .stay)
  | .E3, g =>
    if g.mp = true then some (.E3, g, .up) else some (.E4 3, { g with mp := true }, .up)
  | .E4 i, g =>
    if 1 ≤ i.val then
      some (.E4 ⟨i.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩,
        { g with mp := true }, .up)
    else some (.E5 4, { g with mp := true }, .down)
  | .E5 i, g =>
    if i.val = 4 then
      (if g.mm = false then some (.E5 i, g, .down)
       else some (.E5 3, { g with mm := false }, .down))
    else if 1 ≤ i.val then
      (if g.mm = true then
        some (.E5 ⟨i.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩,
          { g with mm := false }, .down)
       else none)
    else (if g.mm = true then some (.E6, { g with mm := false }, .stay) else none)
  | .E6, g => if g.z = false then some (.E6, g, .down) else some (.acc, g, .stay)
  | .acc, g => some (.acc, g, .stay)
  | .fail, g => some (.fail, g, .stay)

/-- App. C: the step `δ_M(q, g) = (q', g', D)` of `M`: the program of `tab:program`; every pair not
covered by the table, and every attempt to move down from a cell with `𝗓 = 1`, leads to `q_fail`
without writing or moving. -/
def deltaM (q : StateM U) (g : TapeM U) : StateM U × TapeM U × Mv :=
  match programM U q g with
  | none => (.fail, g, .stay)
  | some (q', g', D) => if D = .down ∧ g.z = true then (.fail, g, .stay) else (q', g', D)

/-- App. C, case (2) of `f_M`: the state `q'` brought by a head that moves up from the cell `a`
below, if any. -/
def fromBelow (a : Option (CellM U)) : Option (StateM U) :=
  match a with
  | some (ga, some qa) => if (deltaM U qa ga).2.2 = .up then some (deltaM U qa ga).1 else none
  | _ => none

/-- App. C, case (3) of `f_M`: the state `q'` brought by a head that moves down from the cell `c`
above, if any. -/
def fromAbove (c : Option (CellM U)) : Option (StateM U) :=
  match c with
  | some (gc, some qc) => if (deltaM U qc gc).2.2 = .down then some (deltaM U qc gc).1 else none
  | _ => none

/-- App. C: the local rule `f_M(a, b, c)`, `a, c ∈ 𝒮_M ∪ {⊥}` (`none` is `⊥`), `b ∈ 𝒮_M`, by the
first applicable case: (1) if `b = (g_b, q_b)` has a head and `δ_M(q_b, g_b) = (q', g', D)`:
`(g_b, q_fail)` if `D = +1` and `c = ⊥` or `D = -1` and `a = ⊥`; otherwise `(g', q')` if `D = 0`
and `(g', ·)` if `D ≠ 0`; (2) if `a` has a head that moves up into `b`'s cell in state `q'`:
`(g_b, q')`; (3) if `c` has a head that moves down into `b`'s cell in state `q'`: `(g_b, q')`;
(4) otherwise `(g_b, ·)`. -/
def fM (a : Option (CellM U)) (b : CellM U) (c : Option (CellM U)) : CellM U :=
  match b.2 with
  | some qb =>
    let r := deltaM U qb b.1
    if (r.2.2 = .up ∧ c = none) ∨ (r.2.2 = .down ∧ a = none) then (b.1, some .fail)
    else if r.2.2 = .stay then (r.2.1, some r.1)
    else (r.2.1, none)
  | none =>
    match fromBelow U a with
    | some q' => (b.1, some q')
    | none =>
      match fromAbove U c with
      | some q' => (b.1, some q')
      | none => (b.1, none)

/-- App. C: `init(h, z) = ((h, z, ⊔, 0, 0, 0, 0), q)` with `q = q_start = P₀` if `z = 1` and
`q = ·` if `z = 0`. -/
def initM (h z : Bool) : CellM U :=
  (⟨h, z, 0, false, 0, false, false⟩, if z then some (.P 0) else none)

/-- App. C: the mask bit `𝗆⁻(s)`: the track `𝗆⁻` of the tape symbol of `s`. -/
def maskMinus (s : CellM U) : Bool := s.1.mm

/-- App. C: the mask bit `𝗆⁺(s)`: the track `𝗆⁺` of the tape symbol of `s`. -/
def maskPlus (s : CellM U) : Bool := s.1.mp

/-- (C6): the cell content `s` carries the state `q_acc`. -/
def CarriesAcc (s : CellM U) : Bool := decide (s.2 = some .acc)

end MachineM

/-! ## Section 4.1: fields -/

section Fields

variable (U : Machine)

/-- (F4): a non-empty horizontal logical colour
`(ct, tb, hot, rdy, g⁻, g⁺) ∈ Λ_h⁺ = {0,1} × 𝒮_M × {0,1} × {0,1} × {0,1}²`. -/
structure HCol where
  /-- `ct` -/
  ct : Bool
  /-- `tb` -/
  tb : CellM U
  /-- `hot` -/
  hot : Bool
  /-- `rdy` -/
  rdy : Bool
  /-- `g⁻` -/
  gm : Bool
  /-- `g⁺` -/
  gp : Bool
  deriving DecidableEq, Fintype

/-- (F4): a non-empty vertical logical colour
`(cy, ay, rc, rdy, tb, x) ∈ Λ_v⁺ = {0,1} × {0,1} × [0,80] × {0,1} × 𝒮_M² × {0,1}⁴`.
**[choice]** `x` is a map `Fin 4 → Bool` with `x 0, x 1, x 2, x 3 = x_h⁻, x_h⁺, x_v⁻, x_v⁺`
(the order of `int:sub-charge`). -/
structure VCol where
  /-- `cy` -/
  cy : Bool
  /-- `ay` -/
  ay : Bool
  /-- `rc ∈ [0, 80]` -/
  rc : Fin 81
  /-- `rdy` -/
  rdy : Bool
  /-- `tb ∈ 𝒮_M²` -/
  tb : CellM U × CellM U
  /-- `x ∈ {0,1}⁴` -/
  x : Fin 4 → Bool
  deriving DecidableEq, Fintype

/-- (F5): a cell record `𝔨 ∈ 𝒦`: `ct_in, ct, cy, ay, sm, hot, rdy, g⁻, g⁺ ∈ {0,1}`,
`rc ∈ [0,80]`, `t_S, t_N ∈ 𝒮_M ∪ {⊥}` (`none` is `⊥`), `t_C ∈ 𝒮_M`, `x, y ∈ {0,1}⁴` (ordered as
in `VCol`). -/
structure CellRec where
  /-- `ct_in` -/
  ctIn : Bool
  /-- `ct` -/
  ct : Bool
  /-- `cy` -/
  cy : Bool
  /-- `ay` -/
  ay : Bool
  /-- `sm` -/
  sm : Bool
  /-- `hot` -/
  hot : Bool
  /-- `rdy` -/
  rdy : Bool
  /-- `g⁻` -/
  gm : Bool
  /-- `g⁺` -/
  gp : Bool
  /-- `rc ∈ [0, 80]` -/
  rc : Fin 81
  /-- `t_S` -/
  tS : Option (CellM U)
  /-- `t_N` -/
  tN : Option (CellM U)
  /-- `t_C` -/
  tC : CellM U
  /-- the switches `x = (x_h⁻, x_h⁺, x_v⁻, x_v⁺)` -/
  x : Fin 4 → Bool
  /-- the free bits `y = (y_h⁻, y_h⁺, y_v⁻, y_v⁺)` -/
  y : Fin 4 → Bool
  deriving DecidableEq

/-- `CellRec U` is the product of its fields (used only to transfer the finiteness instance). -/
def CellRec.equivProd : CellRec U ≃
    Bool × Bool × Bool × Bool × Bool × Bool × Bool × Bool × Bool × Fin 81 ×
      Option (CellM U) × Option (CellM U) × CellM U × (Fin 4 → Bool) × (Fin 4 → Bool) where
  toFun k := (k.ctIn, k.ct, k.cy, k.ay, k.sm, k.hot, k.rdy, k.gm, k.gp, k.rc, k.tS, k.tN, k.tC,
    k.x, k.y)
  invFun := fun ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩ =>
    ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩
  left_inv _ := rfl
  right_inv := fun ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ => rfl

instance : Fintype (CellRec U) := Fintype.ofEquiv _ (CellRec.equivProd U).symm

/-- `int:sub-fields`: a site value `ω_ξ ∈ 𝔖`, the tuple of the fields (F1)–(F8); the site alphabet
`𝔖` is the product of the value sets. **[choice]** The empty colour `∘`, the empty cell record
`∘`, the event tag `*`, the blank wire value `□` and `⊥` are `none`; bits are `Bool`. -/
structure SiteVal where
  /-- (F1) the quarter `𝔮 ∈ 𝔸^q` -/
  q : Quarter
  /-- (F2) the orientation tag `o^W ∈ {L,R}²` -/
  oW : LR × LR
  /-- (F2) the orientation tag `o^E ∈ {L,R}²` -/
  oE : LR × LR
  /-- (F2) the orientation tag `o^S ∈ {B,T}²` -/
  oS : BT × BT
  /-- (F2) the orientation tag `o^N ∈ {B,T}²` -/
  oN : BT × BT
  /-- (F3) the event tag `e^W ∈ {cell,wall}² ∪ {*}` -/
  eW : Option (Ev × Ev)
  /-- (F3) the event tag `e^E` -/
  eE : Option (Ev × Ev)
  /-- (F3) the event tag `e^S` -/
  eS : Option (Ev × Ev)
  /-- (F3) the event tag `e^N` -/
  eN : Option (Ev × Ev)
  /-- (F4) the logical colour `ℓ^W ∈ Λ_h` -/
  lW : Option (HCol U)
  /-- (F4) the logical colour `ℓ^E ∈ Λ_h` -/
  lE : Option (HCol U)
  /-- (F4) the logical colour `ℓ^S ∈ Λ_v` -/
  lS : Option (VCol U)
  /-- (F4) the logical colour `ℓ^N ∈ Λ_v` -/
  lN : Option (VCol U)
  /-- (F5) the cell record `𝔨 ∈ 𝒦 ∪ {∘}` -/
  k : Option (CellRec U)
  /-- (F6) the row marker `𝔯 ∈ {0,1}` -/
  rowM : Bool
  /-- (F6) the column marker `𝔠 ∈ {0,1}` -/
  colM : Bool
  /-- (F7) the spin `σ ∈ {+1,-1}` -/
  spin : Spin
  /-- (F8) the wire value `w^W ∈ {+1,-1,□}` -/
  wW : Option Spin
  /-- (F8) the wire value `w^E` -/
  wE : Option Spin
  /-- (F8) the wire value `w^S` -/
  wS : Option Spin
  /-- (F8) the wire value `w^N` -/
  wN : Option Spin
  deriving DecidableEq

/-- `SiteVal U` is the product of the value sets of its fields (`int:sub-fields`: "the site
alphabet `𝔖` is the set of all such tuples"); used to transfer the finiteness instance. -/
def SiteVal.equivProd : SiteVal U ≃
    Quarter × (LR × LR) × (LR × LR) × (BT × BT) × (BT × BT) ×
      Option (Ev × Ev) × Option (Ev × Ev) × Option (Ev × Ev) × Option (Ev × Ev) ×
      Option (HCol U) × Option (HCol U) × Option (VCol U) × Option (VCol U) ×
      Option (CellRec U) × Bool × Bool × Spin ×
      Option Spin × Option Spin × Option Spin × Option Spin where
  toFun s := (s.q, s.oW, s.oE, s.oS, s.oN, s.eW, s.eE, s.eS, s.eN, s.lW, s.lE, s.lS, s.lN, s.k,
    s.rowM, s.colM, s.spin, s.wW, s.wE, s.wS, s.wN)
  invFun := fun ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17,
      a18, a19, a20, a21⟩ =>
    ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20,
      a21⟩
  left_inv _ := rfl
  right_inv := fun ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ => rfl

/-- The site alphabet `𝔖` is finite. -/
instance : Fintype (SiteVal U) := Fintype.ofEquiv _ (SiteVal.equivProd U).symm

end Fields

/-- The site alphabet `𝔖` carries the discrete topology. -/
instance (U : Machine) : TopologicalSpace (SiteVal U) := ⊥

instance (U : Machine) : DiscreteTopology (SiteVal U) := ⟨rfl⟩

/-- The site alphabet `𝔖` carries the discrete σ-algebra. -/
instance (U : Machine) : MeasurableSpace (SiteVal U) := ⊤

instance (U : Machine) : MeasurableSingletonClass (SiteVal U) := ⟨fun _ => trivial⟩

instance (U : Machine) : BorelSpace (SiteVal U) := ⟨borel_eq_top_of_discrete.symm⟩

/-! ## Section 4.2: colours -/

namespace SiteVal

variable {U : Machine}

/-- `int:sub-fields` (colours): `c_E(ω_ξ) = (𝔮_E, o^E, e^E, ℓ^E, 𝔯, w^E)`. -/
def cE (s : SiteVal U) :
    QColH × (LR × LR) × Option (Ev × Ev) × Option (HCol U) × Bool × Option Spin :=
  (s.q.colE, s.oE, s.eE, s.lE, s.rowM, s.wE)

/-- `int:sub-fields` (colours): `c_W(ω_ξ) = (𝔮_W, o^W, e^W, ℓ^W, 𝔯, w^W)`. -/
def cW (s : SiteVal U) :
    QColH × (LR × LR) × Option (Ev × Ev) × Option (HCol U) × Bool × Option Spin :=
  (s.q.colW, s.oW, s.eW, s.lW, s.rowM, s.wW)

/-- `int:sub-fields` (colours): `c_N(ω_ξ) = (𝔮_N, o^N, e^N, ℓ^N, 𝔠, w^N)`. -/
def cN (s : SiteVal U) :
    QColV × (BT × BT) × Option (Ev × Ev) × Option (VCol U) × Bool × Option Spin :=
  (s.q.colN, s.oN, s.eN, s.lN, s.colM, s.wN)

/-- `int:sub-fields` (colours): `c_S(ω_ξ) = (𝔮_S, o^S, e^S, ℓ^S, 𝔠, w^S)`. -/
def cS (s : SiteVal U) :
    QColV × (BT × BT) × Option (Ev × Ev) × Option (VCol U) × Bool × Option Spin :=
  (s.q.colS, s.oS, s.eS, s.lS, s.colM, s.wS)

/-! ## Section 4.3: predicates read from a site value -/

/-- `int:sub-predicates`: a *horizontal carrier*: `VW = -` and `o^W = (L, R)`. -/
def IsHCarrier (s : SiteVal U) : Prop := s.q.VW = none ∧ s.oW = (.L, .R)

/-- `int:sub-predicates`: a *vertical carrier*: `HW = -` and `o^S = (B, T)`. -/
def IsVCarrier (s : SiteVal U) : Prop := s.q.HW = none ∧ s.oS = (.B, .T)

/-- `int:sub-predicates`: an *active* site is both a horizontal and a vertical carrier. -/
def IsActive (s : SiteVal U) : Prop := s.IsHCarrier ∧ s.IsVCarrier

/-- `int:sub-predicates`: a *horizontal* site is only a horizontal carrier. -/
def IsHorizontal (s : SiteVal U) : Prop := s.IsHCarrier ∧ ¬ s.IsVCarrier

/-- `int:sub-predicates`: a *vertical* site is only a vertical carrier. -/
def IsVertical (s : SiteVal U) : Prop := s.IsVCarrier ∧ ¬ s.IsHCarrier

/-- `int:sub-predicates`: the boundary flag `f_W = [e^W_- = wall]`.
**[choice]** Read as `0` when `e^W = *`; the flags are used only at active sites, where (E1)
makes the tag a pair. -/
def fW (s : SiteVal U) : Bool :=
  match s.eW with
  | some (a, _) => decide (a = .wall)
  | none => false

/-- `int:sub-predicates`: the boundary flag `f_E = [e^E_+ = wall]` (read as `0` when `e^E = *`). -/
def fE (s : SiteVal U) : Bool :=
  match s.eE with
  | some (_, b) => decide (b = .wall)
  | none => false

/-- `int:sub-predicates`: the boundary flag `f_S = [e^S_- = wall]` (read as `0` when `e^S = *`). -/
def fS (s : SiteVal U) : Bool :=
  match s.eS with
  | some (a, _) => decide (a = .wall)
  | none => false

/-- `int:sub-predicates`: the boundary flag `f_N = [e^N_+ = wall]` (read as `0` when `e^N = *`). -/
def fN (s : SiteVal U) : Bool :=
  match s.eN with
  | some (_, b) => decide (b = .wall)
  | none => false

/-- `int:sub-predicates`: a *root* is an active site with `f_W = f_S = 1`. -/
def IsRoot (s : SiteVal U) : Prop := s.IsActive ∧ s.fW = true ∧ s.fS = true

end SiteVal

/-- `int:sub-cells`: "a statement about a component of `ℓ^X` is required only when `ℓ^X ≠ ∘`":
`OnColour ℓ P` says that `P` holds of `ℓ` whenever `ℓ` is not `∘`. **[choice]** Every equation of
(C1)–(C8) that mentions a component of a logical colour is wrapped in `OnColour`. -/
def OnColour {α : Type} (l : Option α) (P : α → Prop) : Prop := ∀ c, l = some c → P c

/-- The first entry `e_-` of an event tag is `v`. **[choice]** "`e_- = v`" includes that the tag
is a pair (not `*`). -/
def Ev.FirstIs (e : Option (Ev × Ev)) (v : Ev) : Prop := ∃ b, e = some (v, b)

/-- The second entry `e_+` of an event tag is `v` (the tag is a pair). -/
def Ev.SecondIs (e : Option (Ev × Ev)) (v : Ev) : Prop := ∃ a, e = some (a, v)

/-! ## Section 4.4: routing, markers and wires -/

namespace SiteVal

variable {U : Machine}

/-- (O1): if `VW = -`, then `o^W = o^E`; if `VW = L`, then `o^W_+ = L` and `o^E_- = L`; if
`VW = R`, then `o^W_+ = R` and `o^E_- = R`. -/
def O1 (s : SiteVal U) : Prop :=
  (s.q.VW = none → s.oW = s.oE) ∧
  (s.q.VW = some .L → s.oW.2 = .L ∧ s.oE.1 = .L) ∧
  (s.q.VW = some .R → s.oW.2 = .R ∧ s.oE.1 = .R)

/-- (O2): if `HW = -`, then `o^S = o^N`; if `HW = B`, then `o^S_+ = B` and `o^N_- = B`; if
`HW = T`, then `o^S_+ = T` and `o^N_- = T`. -/
def O2 (s : SiteVal U) : Prop :=
  (s.q.HW = none → s.oS = s.oN) ∧
  (s.q.HW = some .B → s.oS.2 = .B ∧ s.oN.1 = .B) ∧
  (s.q.HW = some .T → s.oS.2 = .T ∧ s.oN.1 = .T)

/-- (E1): `e^X = *` iff `o^X ≠ (L, R)` for `X ∈ {W, E}`, and iff `o^X ≠ (B, T)` for
`X ∈ {S, N}`. -/
def E1 (s : SiteVal U) : Prop :=
  (s.eW = none ↔ s.oW ≠ (.L, .R)) ∧ (s.eE = none ↔ s.oE ≠ (.L, .R)) ∧
  (s.eS = none ↔ s.oS ≠ (.B, .T)) ∧ (s.eN = none ↔ s.oN ≠ (.B, .T))

/-- (E2): at a horizontal site, `e^W = e^E`; at an active site, `e^W_+ = cell` and
`e^E_- = cell`; if `VW = L` and `o^E = (L, R)`, then `e^E_- = wall`; if `VW = R` and
`o^W = (L, R)`, then `e^W_+ = wall`. -/
def E2 (s : SiteVal U) : Prop :=
  (s.IsHorizontal → s.eW = s.eE) ∧
  (s.IsActive → Ev.SecondIs s.eW .cell ∧ Ev.FirstIs s.eE .cell) ∧
  (s.q.VW = some .L ∧ s.oE = (.L, .R) → Ev.FirstIs s.eE .wall) ∧
  (s.q.VW = some .R ∧ s.oW = (.L, .R) → Ev.SecondIs s.eW .wall)

/-- (E3): at a vertical site, `e^S = e^N`; at an active site, `e^S_+ = cell` and
`e^N_- = cell`; if `HW = B` and `o^N = (B, T)`, then `e^N_- = wall`; if `HW = T` and
`o^S = (B, T)`, then `e^S_+ = wall`. -/
def E3 (s : SiteVal U) : Prop :=
  (s.IsVertical → s.eS = s.eN) ∧
  (s.IsActive → Ev.SecondIs s.eS .cell ∧ Ev.FirstIs s.eN .cell) ∧
  (s.q.HW = some .B ∧ s.oN = (.B, .T) → Ev.FirstIs s.eN .wall) ∧
  (s.q.HW = some .T ∧ s.oS = (.B, .T) → Ev.SecondIs s.eS .wall)

/-- (K1): at a site that is not a horizontal carrier, `ℓ^W = ℓ^E = ∘`; at a horizontal site,
`ℓ^W = ℓ^E`. -/
def K1 (s : SiteVal U) : Prop :=
  (¬ s.IsHCarrier → s.lW = none ∧ s.lE = none) ∧ (s.IsHorizontal → s.lW = s.lE)

/-- (K2): at a site that is not a vertical carrier, `ℓ^S = ℓ^N = ∘`; at a vertical site,
`ℓ^S = ℓ^N`. -/
def K2 (s : SiteVal U) : Prop :=
  (¬ s.IsVCarrier → s.lS = none ∧ s.lN = none) ∧ (s.IsVertical → s.lS = s.lN)

/-! ## Section 4.5: cells, the rules (C0)–(C9) for a cell record `𝔨 = k` -/

/-- (C0) Boundaries: `ℓ^X = ∘` iff `f_X = 1`, for `X = W, E, S, N`. -/
def C0 (s : SiteVal U) : Prop :=
  (s.lW = none ↔ s.fW = true) ∧ (s.lE = none ↔ s.fE = true) ∧
  (s.lS = none ↔ s.fS = true) ∧ (s.lN = none ↔ s.fN = true)

/-- (C1) Counter. If `f_W = 1`: `ct_in = ct = cy = 0`. If `f_W = 0`: `ct_in = ℓ^W_ct`;
`cy = 1` if `f_S = 1` and `cy = ℓ^S_cy` if `f_S = 0`; `ct = ct_in ⊕ cy`. In all cases
`ℓ^E_ct = ct` and `ℓ^N_cy = ct_in ∧ cy`. -/
def C1 (s : SiteVal U) (k : CellRec U) : Prop :=
  (s.fW = true → k.ctIn = false ∧ k.ct = false ∧ k.cy = false) ∧
  (s.fW = false →
    OnColour s.lW (fun l => k.ctIn = l.ct) ∧
    (s.fS = true → k.cy = true) ∧
    (s.fS = false → OnColour s.lS (fun l => k.cy = l.cy)) ∧
    k.ct = xor k.ctIn k.cy) ∧
  OnColour s.lE (fun l => l.ct = k.ct) ∧
  OnColour s.lN (fun l => l.cy = (k.ctIn && k.cy))

/-- (C2) Row counter. `rc = 0` if `f_S = 1`, and `rc = min(ℓ^S_rc + 1, 80)` if `f_S = 0`;
`ℓ^N_rc = rc`. **[choice]** The minimum is taken in `ℕ` (in `Fin 81`, `80 + 1` would wrap). -/
def C2 (s : SiteVal U) (k : CellRec U) : Prop :=
  (s.fS = true → k.rc = 0) ∧
  (s.fS = false → OnColour s.lS (fun l => k.rc.val = min (l.rc.val + 1) 80)) ∧
  OnColour s.lN (fun l => l.rc = k.rc)

/-- The majority `maj(a, b, c)` of three bits. -/
def maj (a b c : Bool) : Bool := (a && b) || (a && c) || (b && c)

/-- (C3) Adder. If `f_E = 0`: `ay = sm = 0` and `ℓ^N_ay = 0`. If `f_E = 1`: with
`k = [rc ≤ 1]`, `ay = 0` if `f_S = 1` and `ay = ℓ^S_ay` if `f_S = 0`; `sm = ct ⊕ k ⊕ ay`;
`ℓ^N_ay = maj(ct, k, ay)`. -/
def C3 (s : SiteVal U) (k : CellRec U) : Prop :=
  (s.fE = false → k.ay = false ∧ k.sm = false ∧ OnColour s.lN (fun l => l.ay = false)) ∧
  (s.fE = true →
    (s.fS = true → k.ay = false) ∧
    (s.fS = false → OnColour s.lS (fun l => k.ay = l.ay)) ∧
    k.sm = xor (xor k.ct (decide (k.rc.val ≤ 1))) k.ay ∧
    OnColour s.lN (fun l => l.ay = maj k.ct (decide (k.rc.val ≤ 1)) k.ay))

/-- (C4) One-hot marker. `hot = sm` if `f_E = 1`, and `hot = ℓ^E_hot` if `f_E = 0`;
`ℓ^W_hot = hot`. -/
def C4 (s : SiteVal U) (k : CellRec U) : Prop :=
  (s.fE = true → k.hot = k.sm) ∧
  (s.fE = false → OnColour s.lE (fun l => k.hot = l.hot)) ∧
  OnColour s.lW (fun l => l.hot = k.hot)

/-- (C5) Tableau of `M`. `t_S = ⊥` if `f_S = 1`, and `ℓ^S_tb = (t_S, t_C)` if `f_S = 0`;
`t_N = ⊥` if `f_N = 1`, and `ℓ^N_tb = (t_C, t_N)` if `f_N = 0`; `t_C = init(hot, f_S)` if
`f_W = 1`, and `t_C = ℓ^W_tb` if `f_W = 0`; `ℓ^E_tb = f_M(t_S, t_C, t_N)`.
**[choice]** `ℓ^S_tb = (t_S, t_C)` with `ℓ^S_tb ∈ 𝒮_M²` is read as `t_S = ℓ^S_tb.1` (so
`t_S ≠ ⊥`) and `t_C = ℓ^S_tb.2`; likewise for `ℓ^N_tb = (t_C, t_N)`. -/
def C5 (s : SiteVal U) (k : CellRec U) : Prop :=
  (s.fS = true → k.tS = none) ∧
  (s.fS = false → OnColour s.lS (fun l => k.tS = some l.tb.1 ∧ k.tC = l.tb.2)) ∧
  (s.fN = true → k.tN = none) ∧
  (s.fN = false → OnColour s.lN (fun l => l.tb.1 = k.tC ∧ k.tN = some l.tb.2)) ∧
  (s.fW = true → k.tC = initM U k.hot s.fS) ∧
  (s.fW = false → OnColour s.lW (fun l => k.tC = l.tb)) ∧
  OnColour s.lE (fun l => l.tb = fM U k.tS k.tC k.tN)

/-- (C6) Readiness. If `f_E = 1`: `rdy = [t_C carries q_acc]` if `f_S = 1`, `rdy = ℓ^S_rdy` if
`f_S = 0`, and `ℓ^N_rdy = rdy`. If `f_E = 0`: `rdy = ℓ^E_rdy` and `ℓ^N_rdy = 0`. In all cases
`ℓ^W_rdy = rdy`. -/
def C6 (s : SiteVal U) (k : CellRec U) : Prop :=
  (s.fE = true →
    (s.fS = true → k.rdy = CarriesAcc U k.tC) ∧
    (s.fS = false → OnColour s.lS (fun l => k.rdy = l.rdy)) ∧
    OnColour s.lN (fun l => l.rdy = k.rdy)) ∧
  (s.fE = false →
    OnColour s.lE (fun l => k.rdy = l.rdy) ∧ OnColour s.lN (fun l => l.rdy = false)) ∧
  OnColour s.lW (fun l => l.rdy = k.rdy)

/-- (C7) Masks. If `f_E = 1`: `g^± = rdy ∧ 𝗆^±(t_C)`. If `f_E = 0`: `g^± = ℓ^E_{g^±}`. In all
cases `ℓ^W_{g^±} = g^±`. -/
def C7 (s : SiteVal U) (k : CellRec U) : Prop :=
  (s.fE = true → k.gm = (k.rdy && maskMinus U k.tC) ∧ k.gp = (k.rdy && maskPlus U k.tC)) ∧
  (s.fE = false → OnColour s.lE (fun l => k.gm = l.gm ∧ k.gp = l.gp)) ∧
  OnColour s.lW (fun l => l.gm = k.gm ∧ l.gp = k.gp)

/-- (C8) Switches, for each of the four components `x_ι` separately. If `f_W = 0`: `x_ι = 0` and
`ℓ^N_{x_ι} = 0`. If `f_W = 1` and `f_S = 1`: `x_ι` is unconstrained if `rdy = 1`, and `x_ι = 0`
if `rdy = 0`. If `f_W = 1` and `f_S = 0`: `x_ι = ℓ^S_{x_ι}`. If `f_W = 1`: `ℓ^N_{x_ι} = x_ι`. -/
def C8 (s : SiteVal U) (k : CellRec U) : Prop :=
  ∀ ι : Fin 4,
    (s.fW = false → k.x ι = false ∧ OnColour s.lN (fun l => l.x ι = false)) ∧
    (s.fW = true ∧ s.fS = true → k.rdy = false → k.x ι = false) ∧
    (s.fW = true ∧ s.fS = false → OnColour s.lS (fun l => k.x ι = l.x ι)) ∧
    (s.fW = true → OnColour s.lN (fun l => l.x ι = k.x ι))

/-- The mask `g^-` (for `ι = 0, 2`, the components `x_h⁻, x_v⁻`) or `g^+` (for `ι = 1, 3`) that
goes with the free bit `y_ι` in (C9). -/
def gOf (k : CellRec U) (ι : Fin 4) : Bool := if ι.val % 2 = 0 then k.gm else k.gp

/-- (C9) Free bits. If `f_W = 0`: `y = 0`. If `f_W = 1`: for `k ∈ {h, v}` and each sign, `y_k^±`
is unconstrained if `x_k^± = g^± = 1`, and `y_k^± = 0` otherwise. -/
def C9 (s : SiteVal U) (k : CellRec U) : Prop :=
  (s.fW = false → ∀ ι, k.y ι = false) ∧
  (s.fW = true → ∀ ι, ¬ (k.x ι = true ∧ gOf k ι = true) → k.y ι = false)

/-- (K3): at a site that is not active, `𝔨 = ∘`; at an active site, `𝔨 ∈ 𝒦` and (C0)–(C9)
hold. -/
def K3 (s : SiteVal U) : Prop :=
  (¬ s.IsActive → s.k = none) ∧
  (s.IsActive → ∃ k, s.k = some k ∧ s.C0 ∧ s.C1 k ∧ s.C2 k ∧ s.C3 k ∧ s.C4 k ∧ s.C5 k ∧
    s.C6 k ∧ s.C7 k ∧ s.C8 k ∧ s.C9 k)

/-- (Q1): at an active site, `𝔯 = f_S` and `𝔠 = f_W`. -/
def Q1 (s : SiteVal U) : Prop := s.IsActive → s.rowM = s.fS ∧ s.colM = s.fW

/-- (Q2): if `HW ≠ -`, then `𝔯 = 0`; if `VW ≠ -`, then `𝔠 = 0`. -/
def Q2 (s : SiteVal U) : Prop :=
  (s.q.HW ≠ none → s.rowM = false) ∧ (s.q.VW ≠ none → s.colM = false)

/-- (P1): if `𝔯 = 0`, then `w^W = w^E = □`; if `𝔯 = 1`, then `w^W, w^E ∈ {+1, -1}`, and
`w^E = σ` at a root and `w^E = w^W` at every other site. -/
def P1 (s : SiteVal U) : Prop :=
  (s.rowM = false → s.wW = none ∧ s.wE = none) ∧
  (s.rowM = true → s.wW ≠ none ∧ s.wE ≠ none ∧
    (s.IsRoot → s.wE = some s.spin) ∧ (¬ s.IsRoot → s.wE = s.wW))

/-- (P2): if `𝔠 = 0`, then `w^S = w^N = □`; if `𝔠 = 1`, then `w^S, w^N ∈ {+1, -1}`, and
`w^N = σ` at a root and `w^N = w^S` at every other site. -/
def P2 (s : SiteVal U) : Prop :=
  (s.colM = false → s.wS = none ∧ s.wN = none) ∧
  (s.colM = true → s.wS ≠ none ∧ s.wN ≠ none ∧
    (s.IsRoot → s.wN = some s.spin) ∧ (¬ s.IsRoot → s.wN = s.wS))

/-- (P3): at a root with `rdy = 1`: if `(x_h⁻, x_h⁺) = (0, 1)` then `σ = w^W`; if
`(x_v⁻, x_v⁺) = (0, 1)` then `σ = w^S`. (`rdy` and `x` are those of the cell record.) -/
def P3 (s : SiteVal U) : Prop :=
  s.IsRoot → ∀ k, s.k = some k → k.rdy = true →
    ((k.x 0 = false ∧ k.x 1 = true) → s.wW = some s.spin) ∧
    ((k.x 2 = false ∧ k.x 3 = true) → s.wS = some s.spin)

/-- `int:def-phi`: the set `𝒯` of allowed site values: those satisfying (O1)–(P3) and
(C0)–(C9) (the latter at active sites, through (K3)). -/
def Allowed (s : SiteVal U) : Prop :=
  s.O1 ∧ s.O2 ∧ s.E1 ∧ s.E2 ∧ s.E3 ∧ s.K1 ∧ s.K2 ∧ s.K3 ∧ s.Q1 ∧ s.Q2 ∧ s.P1 ∧ s.P2 ∧ s.P3

/-- `int:sub-charge`: the charge `ch(ω_ξ) = x_{⌊rc/20⌋}` if the site is active, `f_W = 1` and
`rc ≤ 79`, and `0` otherwise (in particular `0` when the cell record is `∘`). -/
def charge (s : SiteVal U) : ℕ :=
  open Classical in
  match s.k with
  | some k =>
    if h : s.IsActive ∧ s.fW = true ∧ k.rc.val ≤ 79 then
      (if k.x ⟨k.rc.val / 20, by omega⟩ = true then 1 else 0)
    else 0
  | none => 0

end SiteVal

/-! ## Section 4.2: the interaction `Φ` (`int:def-phi`) -/

open Classical in
/-- `int:def-phi`: the single-site term `Φ_{ξ}(ω) = ch(ω_ξ)` if `ω_ξ ∈ 𝒯` and `+∞` otherwise. -/
def siteEnergy {U : Machine} (s : SiteVal U) : ℝ≥0∞ :=
  if s.Allowed then (s.charge : ℝ≥0∞) else ⊤

open Classical in
/-- `int:def-phi`: `Φ_{ξ, ξ+e₁}(ω) = 0` if `c_E(ω_ξ) = c_W(ω_{ξ+e₁})` and `+∞` otherwise. -/
def edgeEnergyH {U : Machine} (s t : SiteVal U) : ℝ≥0∞ := if s.cE = t.cW then 0 else ⊤

open Classical in
/-- `int:def-phi`: `Φ_{ξ, ξ+e₂}(ω) = 0` if `c_N(ω_ξ) = c_S(ω_{ξ+e₂})` and `+∞` otherwise. -/
def edgeEnergyV {U : Machine} (s t : SiteVal U) : ℝ≥0∞ := if s.cN = t.cS then 0 else ⊤

open Classical in
/-- `int:def-phi`: the interaction `Φ` on `Ω = 𝔖^{ℤ²}`: the single-site terms, the horizontal and
vertical pair terms, and `Φ_A = 0` for all other `A`. (In each case the site `ξ` is unique.) -/
def Phi (U : Machine) : Interaction (SiteVal U) := fun A ω =>
  if h : ∃ ξ, A = {ξ} then siteEnergy (ω h.choose)
  else if h : ∃ ξ, A = {ξ, ξ + e1} then edgeEnergyH (ω h.choose) (ω (h.choose + e1))
  else if h : ∃ ξ, A = {ξ, ξ + e2} then edgeEnergyV (ω h.choose) (ω (h.choose + e2))
  else 0

/-! ## Section 7.1: temperatures (`prf:windows`) -/

/-- `prf:windows`: `λ_K = 2 ∑_{j=0}^{K-1} 1 / ((2j+1) 3^{2j+1})`. -/
def lam (K : ℕ) : ℚ := 2 * ∑ j ∈ Finset.range K, 1 / ((2 * (j : ℚ) + 1) * 3 ^ (2 * j + 1))

/-- `prf:windows`: `β_n = n λ_{n+3}`. -/
def betaN (n : ℕ) : ℚ := n * lam (n + 3)

/-- `prf:windows`: the open interval `J_n = (β_n - 1/1000, β_n + 1/1000)` of real numbers. -/
def J (n : ℕ) : Set ℝ := Set.Ioo ((betaN n : ℝ) - 1 / 1000) ((betaN n : ℝ) + 1 / 1000)

/-! ## Theorem A and Corollary B -/

/-- `thm:main`: `μ` is a translation-invariant Gibbs measure for `βΦ`. -/
def IsTIGibbs (U : Machine) (β : ℝ) (μ : Measure (Config (SiteVal U))) : Prop :=
  IsGibbs β (Phi U) μ ∧ IsTranslationInvariantMeasure μ

/-- **Theorem A** (`thm:main` with `prf:windows` and the properties of `Φ` stated after the proof
of `thm:main`). For the interaction `Φ` of `int:def-phi` built from a machine `U`:
`Φ` is an interaction (`Φ_A` depends only on `ω_A`), translation invariant and nearest-neighbour,
with values in `{0, 1, +∞}`; the intervals `J_n`, `n ≥ 1`, consist of positive numbers and are
pairwise disjoint; for every `n ≥ 1` and every real `β ∈ J_n`, (i) if `U` does not halt on `n`,
then `βΦ` has exactly one translation-invariant Gibbs measure, and (ii) if `U` halts on `n`, then
`βΦ` has at least two; and for every `β > 0`, `βΦ` has uncountably many Gibbs measures that are
not translation invariant.
**[choice]** Stated for every machine `U` (the proof of `thm:main` does not use universality;
the site alphabet is finite as a type with a `Fintype` instance). -/
def TheoremA : Prop :=
  ∀ U : Machine,
    IsInteraction (Phi U) ∧ IsTranslationInvariant (Phi U) ∧ IsNearestNeighbour (Phi U) ∧
    (∀ (A : Finset Plane) (ω : Config (SiteVal U)),
      Phi U A ω = 0 ∨ Phi U A ω = 1 ∨ Phi U A ω = ⊤) ∧
    (∀ n : ℕ, 1 ≤ n → 0 < (betaN n : ℝ) - 1 / 1000) ∧
    (∀ n m : ℕ, 1 ≤ n → n < m → Disjoint (J n) (J m)) ∧
    (∀ n : ℕ, 1 ≤ n → ∀ β ∈ J n,
      (¬ U.HaltsOn n → ∃! μ : Measure (Config (SiteVal U)), IsTIGibbs U β μ) ∧
      (U.HaltsOn n → ∃ μ₁ μ₂ : Measure (Config (SiteVal U)),
        μ₁ ≠ μ₂ ∧ IsTIGibbs U β μ₁ ∧ IsTIGibbs U β μ₂)) ∧
    (∀ β : ℝ, 0 < β →
      ¬ {μ : Measure (Config (SiteVal U)) |
          IsGibbs β (Phi U) μ ∧ ¬ IsTranslationInvariantMeasure μ}.Countable)

/-- Section 2.2: `U` is universal: its halting set `ℋ_U = {n ≥ 1 : U halts on n}` is not
decidable. **[choice]** The paper fixes `U` with `ℋ_U` `Σ⁰₁`-complete, "in particular
undecidable"; only undecidability is used, so it is the hypothesis here (a weaker hypothesis, a
stronger corollary). That such machines exist is `ExistsUniversal`. -/
def Universal (U : Machine) : Prop := ¬ ComputablePred (fun n : ℕ => 1 ≤ n ∧ U.HaltsOn n)

/-- `cor:undecidable`: the set `𝒰 = {β ∈ ℚ_{>0} : βΦ has exactly one translation-invariant Gibbs
measure}`. -/
def UniqueSet (U : Machine) : Set ℚ :=
  {β | 0 < β ∧ ∃! μ : Measure (Config (SiteVal U)), IsTIGibbs U (β : ℝ) μ}

/-- **Corollary B** (`cor:undecidable`). For a universal machine `U`: the set `𝒰` is not
decidable; the map `n ↦ β_n` is computable; and `β_n ∈ 𝒰` iff `U` does not halt on `n`
(`n ≥ 1`).
**[choice]** A rational is presented by a pair `(p, q)` of natural numbers, `q > 0`, as `p / q`
(`𝒰 ⊆ ℚ_{>0}`): "`𝒰` is not decidable" says that no algorithm decides `p / q ∈ 𝒰` from `(p, q)`,
and "`n ↦ β_n` is computable" says that some computable map gives a pair presenting `β_n`. -/
def CorollaryB : Prop :=
  ∀ U : Machine, Universal U →
    ¬ ComputablePred (fun p : ℕ × ℕ => 0 < p.2 ∧ ((p.1 : ℚ) / p.2) ∈ UniqueSet U) ∧
    (∃ f : ℕ → ℕ × ℕ, Computable f ∧ ∀ n, 0 < (f n).2 ∧ ((f n).1 : ℚ) / (f n).2 = betaN n) ∧
    ∀ n : ℕ, 1 ≤ n → (betaN n ∈ UniqueSet U ↔ ¬ U.HaltsOn n)

/-- Section 2.2: a universal machine exists (so `CorollaryB` is not vacuous). -/
def ExistsUniversal : Prop := ∃ U : Machine, Universal U

end UPD

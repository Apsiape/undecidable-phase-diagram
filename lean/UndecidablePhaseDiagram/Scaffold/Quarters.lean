/-
# Section 3.4 and Appendix A: quarters, light walls, the frame windows

Ported from the forgetting core (`C:/Infanox/fixed-noise-ergodicity-lean`,
`FixedNoiseErgodicity/Family/Walls.lean`; same authors), namespace `FNE.Family` → `UPD.Scaffold`,
onto the quarter set of `Statements.lean` (`Scaffold.Quarter`, parents in `LetterA`, the marks
`∘`, `•` as `Sum.inl`, `Sum.inr`) and its walls (`Quarter.VW`, `Quarter.HW`).

* `scf:def-quarter`: matching of quarters (`Quarter.matchE_iff`, `Quarter.matchN_iff`: the first
  step of the proof of `scf:quarter`), the quartering `f^q(2x + ς) = (ς, f(x))` (`quartering`),
  and `f` legal iff `f^q` legal (`legalOn_quartering_iff`; the converse part of `scf:quarter`).
* `scf:def-walls`: the forgetting core's `vPath`, `hPath`, `vWall`, `hWall`, and the bridge to the
  statement-level walls: `Quarter.VW = vWall` and `Quarter.HW = hWall` up to the names of the sides
  (`VW_eq`, `HW_eq`).
* `scf:def-frames`: frames `I_d(m)` for offsets `a_d`; residue characterisations of membership
  and endpoints.
* `scf:walls` for a parent tower (`walls_col`, `walls_row`), generalized from the forgetting core's
  diagonal phase `(ϖ₀, ϖ₀)` to every phase `(ϖ₁, ϖ₂)`, with column and row frames `a`, `a'`
  (quarter phase `τ = 2ϖ`; the translation by `ε` is in `scf:quarter`).
-/
import UndecidablePhaseDiagram.Scaffold.Red

set_option autoImplicit false

namespace UPD.Scaffold

/-! ## Quarters (`scf:def-quarter`) -/

namespace Quarter

/-- `scf:def-quarter`: quarters match in direction `e₁` if `𝔮_E = 𝔮'_W`. -/
def MatchE (q q' : Quarter) : Prop := q.colE = q'.colW

/-- `scf:def-quarter`: quarters match in direction `e₂` if `𝔮_N = 𝔮'_S`. -/
def MatchN (q q' : Quarter) : Prop := q.colN = q'.colS

/-- Proof of `scf:quarter`: `(ς, 𝔞), (ς', 𝔞')` match horizontally iff `ς' ≡ ς + e₁ (mod 2)` and
either `ς₁ = 0` and `𝔞' = 𝔞`, or `ς₁ = 1` and `𝔞, 𝔞'` match horizontally in `𝔸`. -/
theorem matchE_iff (q q' : Quarter) :
    MatchE q q' ↔ q'.quad.1 = !q.quad.1 ∧ q'.quad.2 = q.quad.2 ∧
      (q.quad.1 = false ∧ q'.parent = q.parent ∨
        q.quad.1 = true ∧ Letter.MatchE q.parent.1 q'.parent.1) := by
  obtain ⟨⟨s1, s2⟩, a⟩ := q
  obtain ⟨⟨t1, t2⟩, b⟩ := q'
  cases s1 <;> cases t1 <;>
    simp [MatchE, colE, colW, Letter.MatchE, Subtype.ext_iff, eq_comm, and_comm]

/-- Proof of `scf:quarter`, vertically. -/
theorem matchN_iff (q q' : Quarter) :
    MatchN q q' ↔ q'.quad.2 = !q.quad.2 ∧ q'.quad.1 = q.quad.1 ∧
      (q.quad.2 = false ∧ q'.parent = q.parent ∨
        q.quad.2 = true ∧ Letter.MatchN q.parent.1 q'.parent.1) := by
  obtain ⟨⟨s1, s2⟩, a⟩ := q
  obtain ⟨⟨t1, t2⟩, b⟩ := q'
  cases s2 <;> cases t2 <;>
    simp [MatchN, colN, colS, Letter.MatchN, Subtype.ext_iff, eq_comm, and_comm]

end Quarter

/-- Letters of `𝔸` match when the letters do. -/
def LetterA.MatchE (a b : LetterA) : Prop := Letter.MatchE a.1 b.1

/-- Letters of `𝔸` match vertically when the letters do. -/
def LetterA.MatchN (a b : LetterA) : Prop := Letter.MatchN a.1 b.1

/-- A tiling of `𝔸` as a map `ℤ² → 𝔸` (values in the subtype). -/
theorem isLetterTiling_iff {f : Plane → LetterA} :
    IsLetterTiling (fun u => (f u).1) ↔ LegalOn LetterA.MatchE LetterA.MatchN Set.univ f :=
  ⟨fun h => h.2, fun h => ⟨fun u => (f u).2, h⟩⟩

/-- The quadrant `ς` of a quarter site `ξ = 2x + ς`. -/
def quad (ξ : Plane) : Bool × Bool := (decide (ξ.1 % 2 = 1), decide (ξ.2 % 2 = 1))

/-- The site `x = ⌊ξ/2⌋` of a quarter site `ξ = 2x + ς`. -/
def half (ξ : Plane) : Plane := (ξ.1 / 2, ξ.2 / 2)

/-- `scf:def-quarter`: the quartering `f^q(2x + ς) = (ς, f(x))` of a map `f : ℤ² → 𝔸`. -/
def quartering (f : Plane → LetterA) : Plane → Quarter := fun ξ => ⟨quad ξ, f (half ξ)⟩

theorem quartering_eq_subst2 (f : Plane → LetterA) :
    quartering f = subst2 (fun (a : LetterA) (s1 s2 : Bool) => (⟨(s1, s2), a⟩ : Quarter)) f :=
  rfl

/-- `scf:quarter` (converse part): a pattern `f` of `𝔸` on `U` is legal iff its quartering is
legal on `2U + [0,2)²`. -/
theorem legalOn_quartering_iff {U : Set Plane} {f : Plane → LetterA} :
    LegalOn Quarter.MatchE Quarter.MatchN (fine2 U) (quartering f) ↔
      LegalOn LetterA.MatchE LetterA.MatchN U f := by
  rw [quartering_eq_subst2]
  refine legalOn_subst2_iff _ (fun a s2 => ?_) (fun a s1 => ?_) (fun a a' => ?_) (fun a a' => ?_)
  · simp [Quarter.MatchE, Quarter.colE, Quarter.colW]
  · simp [Quarter.MatchN, Quarter.colN, Quarter.colS]
  · simp [Quarter.MatchE, Quarter.colE, Quarter.colW, LetterA.MatchE, Letter.MatchE]
  · simp [Quarter.MatchN, Quarter.colN, Quarter.colS, LetterA.MatchN, Letter.MatchN]

/-- `scf:quarter` (converse part): the quartering of a tiling of `𝔸` is a tiling of `𝔸^q`. -/
theorem legalOn_quartering {f : Plane → LetterA} (hf : IsLetterTiling (fun u => (f u).1)) :
    LegalOn Quarter.MatchE Quarter.MatchN Set.univ (quartering f) := by
  rw [← fine2_univ]
  exact legalOn_quartering_iff.2 (isLetterTiling_iff.1 hf)

/-! ## Walls (`scf:def-walls`) -/

/-- The side of a wall: `lo` is a left side (vertical walls) or a bottom side (horizontal walls),
`hi` a right side or a top side. -/
inductive Side where
  | lo
  | hi
  deriving DecidableEq

/-- `scf:def-walls`: the pair `(ς, 𝔞)` lies on a *vertical red path* if the thick type `κ` of `𝔞`
has a vertical red atom, `ς₁ = 1` if this atom is `r₀` and `ς₁ = 0` if it is `r₂`, and, when `κ`
is a corner, `ς₂ = 1` if its north endpoint is red and `ς₂ = 0` if its south endpoint is red. It
is a left side (`lo`) for `r₀` and a right side (`hi`) for `r₂`. -/
def vPath (s : Bool × Bool) (κ : Thick) : Option Side :=
  match κ.vRedAtom with
  | none => none
  | some α => if s.1 = decide (α = .r0) ∧ (κ.IsCorner = true → s.2 = κ.epN.IsRed) then
      some (if α = .r0 then .lo else .hi) else none

/-- `scf:def-walls`: the pair lies on a *horizontal red path* if `κ` has a horizontal red atom,
`ς₂ = 1` if this atom is `r₁` and `ς₂ = 0` if it is `r₃`, and, when `κ` is a corner, `ς₁ = 1` if
its east endpoint is red and `ς₁ = 0` if its west endpoint is red. It is a bottom side (`lo`)
for `r₁` and a top side (`hi`) for `r₃`. -/
def hPath (s : Bool × Bool) (κ : Thick) : Option Side :=
  match κ.hRedAtom with
  | none => none
  | some γ => if s.2 = decide (γ = .r1) ∧ (κ.IsCorner = true → s.1 = κ.epE.IsRed) then
      some (if γ = .r1 then .lo else .hi) else none

/-- `scf:def-walls`: the pair lies on a *light vertical wall* (and on which side): a vertical red
path with `χ₁(𝔞) = 1`. -/
def vWall (s : Bool × Bool) (x : Letter) : Option Side := if x.b1 then vPath s x.base.thick else none

/-- `scf:def-walls`: the pair lies on a *light horizontal wall*: a horizontal red path with
`χ₂(𝔞) = 1`. -/
def hWall (s : Bool × Bool) (x : Letter) : Option Side := if x.b2 then hPath s x.base.thick else none

/-! ## Frames (`scf:def-frames`) -/

/-- `scf:def-frames`: the left endpoint `a_d + (4m+1)4^d + 1` of the frame `I_d(m)`. -/
def frameLo (a : ℕ → ℤ) (d : ℕ) (m : ℤ) : ℤ := a d + (4 * m + 1) * 4 ^ d + 1

/-- `scf:def-frames`: the right endpoint `a_d + (4m+3)4^d` of the frame `I_d(m)`. -/
def frameHi (a : ℕ → ℤ) (d : ℕ) (m : ℤ) : ℤ := a d + (4 * m + 3) * 4 ^ d

/-- `scf:def-frames`: `z` lies in a frame of depth `d`. -/
def InFrame (a : ℕ → ℤ) (d : ℕ) (z : ℤ) : Prop := ∃ m : ℤ, frameLo a d m ≤ z ∧ z ≤ frameHi a d m

/-- `scf:def-frames`: `z` is the left endpoint of a frame of depth `d`. -/
def IsLeftEnd (a : ℕ → ℤ) (d : ℕ) (z : ℤ) : Prop := ∃ m : ℤ, z = frameLo a d m

/-- `scf:def-frames`: `z` is the right endpoint of a frame of depth `d`. -/
def IsRightEnd (a : ℕ → ℤ) (d : ℕ) (z : ℤ) : Prop := ∃ m : ℤ, z = frameHi a d m

/-- `z - a = ρ + 4p·m` with `0 ≤ ρ < 4p` determines `ρ = (z - a) mod 4p`. -/
theorem emod_of_decomp {y ρ p m : ℤ} (h : y = ρ + p * 4 * m) (h0 : 0 ≤ ρ) (h1 : ρ < p * 4) :
    y % (p * 4) = ρ := by
  rw [h, Int.add_mul_emod_self_left, Int.emod_eq_of_lt h0 h1]

theorem inFrame_iff (a : ℕ → ℤ) (d : ℕ) (z : ℤ) :
    InFrame a d z ↔ 4 ^ d + 1 ≤ (z - a d) % 4 ^ (d + 1) ∧ (z - a d) % 4 ^ (d + 1) ≤ 3 * 4 ^ d := by
  have hp : (0 : ℤ) < 4 ^ d := by positivity
  simp only [InFrame, frameLo, frameHi, pow_succ]
  generalize (4 : ℤ) ^ d = p at hp ⊢
  constructor
  · rintro ⟨m, h1, h2⟩
    rw [emod_of_decomp (ρ := z - a d - p * 4 * m) (m := m) (by ring) (by nlinarith)
      (by nlinarith)]
    constructor <;> nlinarith
  · rintro ⟨h1, h2⟩
    have := Int.mul_ediv_add_emod (z - a d) (p * 4)
    exact ⟨(z - a d) / (p * 4), by nlinarith, by nlinarith⟩

theorem isLeftEnd_iff (a : ℕ → ℤ) (d : ℕ) (z : ℤ) :
    IsLeftEnd a d z ↔ (z - a d) % 4 ^ (d + 1) = 4 ^ d + 1 := by
  have hp : (0 : ℤ) < 4 ^ d := by positivity
  simp only [IsLeftEnd, frameLo, pow_succ]
  generalize (4 : ℤ) ^ d = p at hp ⊢
  constructor
  · rintro ⟨m, rfl⟩
    exact emod_of_decomp (m := m) (by ring) (by linarith) (by linarith)
  · intro h
    have := Int.mul_ediv_add_emod (z - a d) (p * 4)
    exact ⟨(z - a d) / (p * 4), by rw [h] at this; linarith⟩

theorem isRightEnd_iff (a : ℕ → ℤ) (d : ℕ) (z : ℤ) :
    IsRightEnd a d z ↔ (z - a d) % 4 ^ (d + 1) = 3 * 4 ^ d := by
  have hp : (0 : ℤ) < 4 ^ d := by positivity
  simp only [IsRightEnd, frameHi, pow_succ]
  generalize (4 : ℤ) ^ d = p at hp ⊢
  constructor
  · rintro ⟨m, rfl⟩
    exact emod_of_decomp (m := m) (by ring) (by linarith) (by linarith)
  · intro h
    have := Int.mul_ediv_add_emod (z - a d) (p * 4)
    exact ⟨(z - a d) / (p * 4), by rw [h] at this; linarith⟩

/-! ## `scf:walls` -/

/-- `ξ = 2⌊ξ/2⌋ + (ξ mod 2)`: `(ξ - 2W) mod 2M = 2((⌊ξ/2⌋ - W) mod M) + (ξ mod 2)`. -/
theorem emod_half (ξ W M : ℤ) (hM : 0 < M) :
    (ξ - 2 * W) % (2 * M) = 2 * ((ξ / 2 - W) % M) + ξ % 2 := by
  have h1 := Int.mul_ediv_add_emod ξ 2
  have h2 := Int.mul_ediv_add_emod (ξ / 2 - W) M
  have h3 := Int.emod_nonneg (ξ / 2 - W) hM.ne'
  have h4 := Int.emod_lt_of_pos (ξ / 2 - W) hM
  have h5 : 0 ≤ ξ % 2 := Int.emod_nonneg ξ (by norm_num)
  have h6 : ξ % 2 < 2 := Int.emod_lt_of_pos ξ (by norm_num)
  have e : ξ - 2 * W = 2 * ((ξ / 2 - W) % M) + ξ % 2 + 2 * M * ((ξ / 2 - W) / M) := by linarith
  rw [e, Int.add_mul_emod_self_left]
  exact Int.emod_eq_of_lt (by linarith) (by linarith)

/-- `scf:walls` (proof): the quarter coordinate `ŝ = (ξ - 2ϖ₀) mod 2^{r+3}` is `2 s(⌊ξ/2⌋) + ς`. -/
theorem two_sres_add (c : ℕ → Bool) (r : ℕ) (ξ : ℤ) :
    2 * sres c r (ξ / 2) + bitZ (decide (ξ % 2 = 1)) = (ξ - 2 * wsum c (r + 2)) % 2 ^ (r + 3) := by
  rw [sres, bitZ_decide_emod_two, show (2 : ℤ) ^ (r + 3) = 2 * 2 ^ (r + 2) by ring,
    emod_half _ _ _ (by positivity)]

/-- `scf:walls` (proof), the core: from the data of `app:red` for a column of rank `r`
(`p = 2^r`), the pair `(ς, κ)` lies on a vertical red path with side `side` iff
`ŝ₁ = 2s₁ + ς₁ ∈ {2p + 1, 6p}` (left side for `2p + 1`) and `ŝ₂ = 2s₂ + ς₂ ∈ [2p + 1, 6p]`. -/
theorem vPath_iff {κ : Thick} {p s1 s2 : ℤ} (hp : 0 < p) (hs1 : s1 = p ∨ s1 = 3 * p)
    (hv : κ.vRedAtom = if p ≤ s2 ∧ s2 ≤ 3 * p then some (if s1 = p then .r0 else .r2) else none)
    (hN : s2 = p → ∃ k, κ = .corner k ∧ k.epN.IsRed)
    (hS : s2 = 3 * p → ∃ k, κ = .corner k ∧ k.epS.IsRed)
    (hl : p < s2 → s2 < 3 * p → ¬ κ.IsCorner = true) (e1 e2 : Bool) (side : Side) :
    vPath (e1, e2) κ = some side ↔
      ((2 * s1 + bitZ e1 = 2 * p + 1 ∧ side = .lo) ∨ (2 * s1 + bitZ e1 = 6 * p ∧ side = .hi)) ∧
      2 * p + 1 ≤ 2 * s2 + bitZ e2 ∧ 2 * s2 + bitZ e2 ≤ 6 * p := by
  unfold vPath
  rw [hv]
  by_cases hin : p ≤ s2 ∧ s2 ≤ 3 * p
  · rw [if_pos hin]
    have hC : (κ.IsCorner = true → e2 = κ.epN.IsRed) ↔
        ((s2 = p → e2 = true) ∧ (s2 = 3 * p → e2 = false)) := by
      by_cases h1 : s2 = p
      · obtain ⟨k, rfl, hk⟩ := hN h1
        have : p ≠ 3 * p := by omega
        simp [Thick.IsCorner, Thick.epN, hk, h1, this]
      · by_cases h3 : s2 = 3 * p
        · obtain ⟨k, rfl, hk⟩ := hS h3
          have hn := Thick.corner_not_epN hk
          simp only [Thick.epN] at hn
          have : 3 * p ≠ p := by omega
          simp [Thick.IsCorner, Thick.epN, hn, h3, this]
        · have := hl (by omega) (by omega)
          simp [this, h1, h3]
    simp only [hC]
    rcases hs1 with h1 | h1 <;> subst h1 <;> cases side <;> cases e1 <;> cases e2 <;>
      simp [bitZ] <;> omega
  · rw [if_neg hin]
    constructor
    · intro h; cases h
    · rintro ⟨-, h2, h3⟩
      exfalso; apply hin
      have := bitZ_nonneg e2; have := bitZ_le_one e2
      constructor <;> omega

/-- `scf:walls` (proof), the core for rows: the pair lies on a horizontal red path with side
`side` iff `ŝ₂ ∈ {2p + 1, 6p}` (bottom side for `2p + 1`) and `ŝ₁ ∈ [2p + 1, 6p]`. -/
theorem hPath_iff {κ : Thick} {p s1 s2 : ℤ} (hp : 0 < p) (hs2 : s2 = p ∨ s2 = 3 * p)
    (hv : κ.hRedAtom = if p ≤ s1 ∧ s1 ≤ 3 * p then some (if s2 = p then .r1 else .r3) else none)
    (hE : s1 = p → ∃ k, κ = .corner k ∧ k.epE.IsRed)
    (hW : s1 = 3 * p → ∃ k, κ = .corner k ∧ k.epW.IsRed)
    (hl : p < s1 → s1 < 3 * p → ¬ κ.IsCorner = true) (e1 e2 : Bool) (side : Side) :
    hPath (e1, e2) κ = some side ↔
      ((2 * s2 + bitZ e2 = 2 * p + 1 ∧ side = .lo) ∨ (2 * s2 + bitZ e2 = 6 * p ∧ side = .hi)) ∧
      2 * p + 1 ≤ 2 * s1 + bitZ e1 ∧ 2 * s1 + bitZ e1 ≤ 6 * p := by
  unfold hPath
  rw [hv]
  by_cases hin : p ≤ s1 ∧ s1 ≤ 3 * p
  · rw [if_pos hin]
    have hC : (κ.IsCorner = true → e1 = κ.epE.IsRed) ↔
        ((s1 = p → e1 = true) ∧ (s1 = 3 * p → e1 = false)) := by
      by_cases h1 : s1 = p
      · obtain ⟨k, rfl, hk⟩ := hE h1
        have : p ≠ 3 * p := by omega
        simp [Thick.IsCorner, Thick.epE, hk, h1, this]
      · by_cases h3 : s1 = 3 * p
        · obtain ⟨k, rfl, hk⟩ := hW h3
          have hn := Thick.corner_not_epE hk
          simp only [Thick.epE] at hn
          have : 3 * p ≠ p := by omega
          simp [Thick.IsCorner, Thick.epE, hn, h3, this]
        · have := hl (by omega) (by omega)
          simp [this, h1, h3]
    simp only [hC]
    rcases hs2 with h1 | h1 <;> subst h1 <;> cases side <;> cases e1 <;> cases e2 <;>
      simp [bitZ] <;> omega
  · rw [if_neg hin]
    constructor
    · intro h; cases h
    · rintro ⟨-, h2, h3⟩
      exfalso; apply hin
      have := bitZ_nonneg e1; have := bitZ_le_one e1
      constructor <;> omega

/-- `4^{k+1} = 2 · 2^{2k+1}`. -/
theorem four_pow_succ (k : ℕ) : (4 : ℤ) ^ (k + 1) = 2 * 2 ^ (2 * k + 1) := by
  rw [show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_mul]; ring_nf

/-- `4^{k+2} = 2^{(2k+1)+3}`. -/
theorem four_pow_succ_succ (k : ℕ) : (4 : ℤ) ^ (k + 1 + 1) = 2 ^ (2 * k + 1 + 3) := by
  rw [show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_mul]; ring_nf

/-- With frames `a_d ≡ 2ϖ₀ (mod 4^{d+1})`, for `r = 2k + 1` and `d = k + 1`:
`(z - 2ϖ₀) mod 2^{r+3} = (z - a_d) mod 4^{d+1}`. -/
theorem res_frame {c : ℕ → Bool} {a : ℕ → ℤ}
    (ha : ∀ d, a d % 4 ^ (d + 1) = 2 * wsum c (2 * d + 1) % 4 ^ (d + 1)) (k : ℕ) (z : ℤ) :
    (z - 2 * wsum c (2 * k + 1 + 2)) % 2 ^ (2 * k + 1 + 3) = (z - a (k + 1)) % 4 ^ (k + 1 + 1) := by
  rw [← four_pow_succ_succ, Int.sub_emod, show 2 * k + 1 + 2 = 2 * (k + 1) + 1 by ring, ← ha,
    ← Int.sub_emod]

/-- `scf:walls` (proof, converse): with frames `a_d ≡ 2ϖ₀ (mod 4^{d+1})`, if `ξ₁` is an endpoint
of a frame of depth `d = k + 1`, the column `⌊ξ₁/2⌋` has rank `2d - 1 = 2k + 1`. -/
theorem rank_of_endpoint {c : ℕ → Bool} {a : ℕ → ℤ}
    (ha : ∀ d, a d % 4 ^ (d + 1) = 2 * wsum c (2 * d + 1) % 4 ^ (d + 1)) {k : ℕ} {ξ : ℤ}
    (h : IsLeftEnd a (k + 1) ξ ∨ IsRightEnd a (k + 1) ξ) : IsRank c (ξ / 2) (2 * k + 1) := by
  rw [isLeftEnd_iff, isRightEnd_iff, ← res_frame ha, ← two_sres_add, four_pow_succ] at h
  have hq : (0 : ℤ) < 2 ^ (2 * k + 1) := by positivity
  apply isRank_of_emod (l := 2 * k + 1 + 2) (by omega)
  have hb0 := bitZ_nonneg (decide (ξ % 2 = 1)); have hb1 := bitZ_le_one (decide (ξ % 2 = 1))
  -- `s := (⌊ξ/2⌋ - ϖ₀) mod 2^{2k+3}` is `q` or `3q`, with `q = 2^{2k+1}`
  have hs : sres c (2 * k + 1) (ξ / 2) = 2 ^ (2 * k + 1) ∨
      sres c (2 * k + 1) (ξ / 2) = 3 * 2 ^ (2 * k + 1) := by
    generalize (2 : ℤ) ^ (2 * k + 1) = q at h hq
    generalize sres c (2 * k + 1) (ξ / 2) = s at h
    omega
  rw [sres] at hs
  have hdvd : (2 : ℤ) ^ (2 * k + 1 + 1) ∣ 2 ^ (2 * k + 1 + 2) := pow_dvd_pow 2 (by omega)
  rw [← Int.emod_emod_of_dvd _ hdvd]
  have e2 : (2 : ℤ) ^ (2 * k + 1 + 1) = 2 * 2 ^ (2 * k + 1) := by ring
  rw [e2]
  rcases hs with hs | hs <;> rw [hs]
  · exact Int.emod_eq_of_lt (by positivity) (by linarith)
  · have : (3 * 2 ^ (2 * k + 1) : ℤ) = 2 ^ (2 * k + 1) + 2 * 2 ^ (2 * k + 1) * 1 := by ring
    rw [this, Int.add_mul_emod_self_left]
    exact Int.emod_eq_of_lt (by positivity) (by linarith)

/-- **`scf:walls`** (vertical walls), for a parent tower. Let `(f_m)` be a tower of height `h` with
digits `υ` (phase `ϖ = (ϖ₁, ϖ₂)`), take column frames with `a_d ≡ 2ϖ₁ (mod 4^{d+1})` and row frames
with `a'_d ≡ 2ϖ₂ (mod 4^{d+1})` (the frames of the quarter phase `τ = 2ϖ`, quarter shift `ε = 0`),
and let the column `⌊ξ₁/2⌋` have rank `r ≤ h - 2`. Then the quarter of `f_0` at `ξ` lies on a light
vertical wall with side `side` iff there is `d ≥ 1` such that `ξ₁` is the left (for `lo`) or right
(for `hi`) endpoint of a column frame of depth `d` and `ξ₂` lies in a row frame of depth `d`; the
rank is then `2d - 1` (`rank_of_endpoint`). (Generalized from the forgetting core's diagonal phase
`(ϖ₀, ϖ₀)`.) -/
theorem walls_col {υ : ℕ → Bool × Bool} {f : ℕ → Plane → Letter} {h : ℕ} (hf : TowerRel υ f h)
    {a a' : ℕ → ℤ} (ha : ∀ d, a d % 4 ^ (d + 1) = 2 * wsum (col υ) (2 * d + 1) % 4 ^ (d + 1))
    (ha' : ∀ d, a' d % 4 ^ (d + 1) = 2 * wsum (row υ) (2 * d + 1) % 4 ^ (d + 1))
    {ξ : Plane} {r : ℕ} (hr : IsRank (col υ) (ξ.1 / 2) r) (hrh : r + 2 ≤ h) (side : Side) :
    vWall (quad ξ) (f 0 (half ξ)) = some side ↔
      ∃ d, 1 ≤ d ∧ ((side = .lo ∧ IsLeftEnd a d ξ.1) ∨ (side = .hi ∧ IsRightEnd a d ξ.1)) ∧
        InFrame a' d ξ.2 := by
  have hr' : IsRank (col υ) (half ξ).1 r := hr
  obtain ⟨hs, hv, hN, hS, hl⟩ := red_col hf hrh hr'
  have hb := rank_bits_col hf (by omega : r < h) hr'
  have hp : (0 : ℤ) < 2 ^ r := by positivity
  have key : vPath (quad ξ) (f 0 (half ξ)).base.thick = some side ↔
      (((ξ.1 - 2 * wsum (col υ) (r + 2)) % 2 ^ (r + 3) = 2 * 2 ^ r + 1 ∧ side = .lo) ∨
        ((ξ.1 - 2 * wsum (col υ) (r + 2)) % 2 ^ (r + 3) = 6 * 2 ^ r ∧ side = .hi)) ∧
      2 * 2 ^ r + 1 ≤ (ξ.2 - 2 * wsum (row υ) (r + 2)) % 2 ^ (r + 3) ∧
      (ξ.2 - 2 * wsum (row υ) (r + 2)) % 2 ^ (r + 3) ≤ 6 * 2 ^ r := by
    rw [← two_sres_add, ← two_sres_add]
    exact vPath_iff hp hs hv hN hS hl (quad ξ).1 (quad ξ).2 side
  have hrank : ∀ d, 1 ≤ d → (IsLeftEnd a d ξ.1 ∨ IsRightEnd a d ξ.1) → r = 2 * (d - 1) + 1 := by
    intro d hd hend
    obtain ⟨j, rfl⟩ : ∃ j, d = j + 1 := ⟨d - 1, by omega⟩
    have := hr.unique (rank_of_endpoint ha hend)
    omega
  unfold vWall
  rw [hb]
  by_cases hodd : r % 2 = 1
  · rw [if_pos (decide_eq_true hodd), key]
    obtain ⟨k, rfl⟩ : ∃ k, r = 2 * k + 1 := ⟨r / 2, by omega⟩
    have hT : ((((ξ.1 - 2 * wsum (col υ) (2 * k + 1 + 2)) % 2 ^ (2 * k + 1 + 3) = 2 * 2 ^ (2 * k + 1) + 1 ∧
          side = .lo) ∨
        ((ξ.1 - 2 * wsum (col υ) (2 * k + 1 + 2)) % 2 ^ (2 * k + 1 + 3) = 6 * 2 ^ (2 * k + 1) ∧
          side = .hi)) ∧
        2 * 2 ^ (2 * k + 1) + 1 ≤ (ξ.2 - 2 * wsum (row υ) (2 * k + 1 + 2)) % 2 ^ (2 * k + 1 + 3) ∧
        (ξ.2 - 2 * wsum (row υ) (2 * k + 1 + 2)) % 2 ^ (2 * k + 1 + 3) ≤ 6 * 2 ^ (2 * k + 1)) ↔
        ((side = .lo ∧ IsLeftEnd a (k + 1) ξ.1) ∨ (side = .hi ∧ IsRightEnd a (k + 1) ξ.1)) ∧
          InFrame a' (k + 1) ξ.2 := by
      rw [isLeftEnd_iff, isRightEnd_iff, inFrame_iff, ← res_frame ha, ← res_frame ha',
        four_pow_succ]
      generalize (ξ.1 - 2 * wsum (col υ) (2 * k + 1 + 2)) % 2 ^ (2 * k + 1 + 3) = ρ1
      generalize (ξ.2 - 2 * wsum (row υ) (2 * k + 1 + 2)) % 2 ^ (2 * k + 1 + 3) = ρ2
      generalize (2 : ℤ) ^ (2 * k + 1) = q
      cases side <;> simp <;> omega
    rw [hT]
    constructor
    · intro h'; exact ⟨k + 1, by omega, h'⟩
    · rintro ⟨d, hd, hend, hin⟩
      have := hrank d hd (hend.imp And.right And.right)
      obtain rfl : d = k + 1 := by omega
      exact ⟨hend, hin⟩
  · rw [if_neg (by simpa using hodd)]
    constructor
    · intro h'; cases h'
    · rintro ⟨d, hd, hend, -⟩
      have := hrank d hd (hend.imp And.right And.right)
      omega

/-- **`scf:walls`** (horizontal walls), for a parent tower: if the row `⌊ξ₂/2⌋` has rank
`r ≤ h - 2`, the quarter of `f_0` at `ξ` lies on a light horizontal wall with side `side` iff there
is `d ≥ 1` such that `ξ₂` is the left (bottom side, `lo`) or right (top side, `hi`) endpoint of a row
frame of depth `d` and `ξ₁` lies in a column frame of depth `d`. -/
theorem walls_row {υ : ℕ → Bool × Bool} {f : ℕ → Plane → Letter} {h : ℕ} (hf : TowerRel υ f h)
    {a a' : ℕ → ℤ} (ha : ∀ d, a d % 4 ^ (d + 1) = 2 * wsum (col υ) (2 * d + 1) % 4 ^ (d + 1))
    (ha' : ∀ d, a' d % 4 ^ (d + 1) = 2 * wsum (row υ) (2 * d + 1) % 4 ^ (d + 1))
    {ξ : Plane} {r : ℕ} (hr : IsRank (row υ) (ξ.2 / 2) r) (hrh : r + 2 ≤ h) (side : Side) :
    hWall (quad ξ) (f 0 (half ξ)) = some side ↔
      ∃ d, 1 ≤ d ∧ ((side = .lo ∧ IsLeftEnd a' d ξ.2) ∨ (side = .hi ∧ IsRightEnd a' d ξ.2)) ∧
        InFrame a d ξ.1 := by
  have hr' : IsRank (row υ) (half ξ).2 r := hr
  obtain ⟨hs, hv, hN, hS, hl⟩ := red_row hf hrh hr'
  have hb := rank_bits_row hf (by omega : r < h) hr'
  have hp : (0 : ℤ) < 2 ^ r := by positivity
  have key : hPath (quad ξ) (f 0 (half ξ)).base.thick = some side ↔
      (((ξ.2 - 2 * wsum (row υ) (r + 2)) % 2 ^ (r + 3) = 2 * 2 ^ r + 1 ∧ side = .lo) ∨
        ((ξ.2 - 2 * wsum (row υ) (r + 2)) % 2 ^ (r + 3) = 6 * 2 ^ r ∧ side = .hi)) ∧
      2 * 2 ^ r + 1 ≤ (ξ.1 - 2 * wsum (col υ) (r + 2)) % 2 ^ (r + 3) ∧
      (ξ.1 - 2 * wsum (col υ) (r + 2)) % 2 ^ (r + 3) ≤ 6 * 2 ^ r := by
    rw [← two_sres_add, ← two_sres_add]
    exact hPath_iff hp hs hv hN hS hl (quad ξ).1 (quad ξ).2 side
  have hrank : ∀ d, 1 ≤ d → (IsLeftEnd a' d ξ.2 ∨ IsRightEnd a' d ξ.2) → r = 2 * (d - 1) + 1 := by
    intro d hd hend
    obtain ⟨j, rfl⟩ : ∃ j, d = j + 1 := ⟨d - 1, by omega⟩
    have := hr.unique (rank_of_endpoint ha' hend)
    omega
  unfold hWall
  rw [hb]
  by_cases hodd : r % 2 = 1
  · rw [if_pos (decide_eq_true hodd), key]
    obtain ⟨k, rfl⟩ : ∃ k, r = 2 * k + 1 := ⟨r / 2, by omega⟩
    have hT : ((((ξ.2 - 2 * wsum (row υ) (2 * k + 1 + 2)) % 2 ^ (2 * k + 1 + 3) = 2 * 2 ^ (2 * k + 1) + 1 ∧
          side = .lo) ∨
        ((ξ.2 - 2 * wsum (row υ) (2 * k + 1 + 2)) % 2 ^ (2 * k + 1 + 3) = 6 * 2 ^ (2 * k + 1) ∧
          side = .hi)) ∧
        2 * 2 ^ (2 * k + 1) + 1 ≤ (ξ.1 - 2 * wsum (col υ) (2 * k + 1 + 2)) % 2 ^ (2 * k + 1 + 3) ∧
        (ξ.1 - 2 * wsum (col υ) (2 * k + 1 + 2)) % 2 ^ (2 * k + 1 + 3) ≤ 6 * 2 ^ (2 * k + 1)) ↔
        ((side = .lo ∧ IsLeftEnd a' (k + 1) ξ.2) ∨ (side = .hi ∧ IsRightEnd a' (k + 1) ξ.2)) ∧
          InFrame a (k + 1) ξ.1 := by
      rw [isLeftEnd_iff, isRightEnd_iff, inFrame_iff, ← res_frame ha', ← res_frame ha,
        four_pow_succ]
      generalize (ξ.2 - 2 * wsum (row υ) (2 * k + 1 + 2)) % 2 ^ (2 * k + 1 + 3) = ρ1
      generalize (ξ.1 - 2 * wsum (col υ) (2 * k + 1 + 2)) % 2 ^ (2 * k + 1 + 3) = ρ2
      generalize (2 : ℤ) ^ (2 * k + 1) = q
      cases side <;> simp <;> omega
    rw [hT]
    constructor
    · intro h'; exact ⟨k + 1, by omega, h'⟩
    · rintro ⟨d, hd, hend, hin⟩
      have := hrank d hd (hend.imp And.right And.right)
      obtain rfl : d = k + 1 := by omega
      exact ⟨hend, hin⟩
  · rw [if_neg (by simpa using hodd)]
    constructor
    · intro h'; cases h'
    · rintro ⟨d, hd, hend, -⟩
      have := hrank d hd (hend.imp And.right And.right)
      omega


/-! ## The statement-level walls (`int:sub-predicates`) -/

/-- The side of a light vertical wall in the names of `int:sub-predicates`: `L` for a left side,
`R` for a right side. -/
def Side.toLR : Side → LR
  | .lo => .L
  | .hi => .R

/-- The side of a light horizontal wall: `B` for a bottom side, `T` for a top side. -/
def Side.toBT : Side → BT
  | .lo => .B
  | .hi => .T

/-- The statement-level `VW` (`int:sub-predicates`, from `scf:def-walls` as written in
`Statements.lean`) is the forgetting core's `vWall`, with the sides renamed. -/
theorem VW_eq (q : Quarter) : q.VW = (vWall q.quad q.parent.1).map Side.toLR := by
  obtain ⟨⟨s1, s2⟩, ⟨⟨⟨θ, κ, ψ⟩, b1, b2⟩, hA⟩⟩ := q
  simp only [Quarter.VW, Quarter.OnVRedPath, Quarter.thick, vWall]
  cases b1 <;> cases s1 <;> cases s2 <;> rcases κ with k | ⟨α, γ⟩ <;> (try cases k) <;>
    (try cases α) <;>
    simp [vPath, Thick.vRedAtom, Thick.epN, Thick.epS, Thick.IsCorner, Corner.epN, Corner.epS,
      VAtom.IsRed, Side.toLR]

/-- The statement-level `HW` is the forgetting core's `hWall`, with the sides renamed. -/
theorem HW_eq (q : Quarter) : q.HW = (hWall q.quad q.parent.1).map Side.toBT := by
  obtain ⟨⟨s1, s2⟩, ⟨⟨⟨θ, κ, ψ⟩, b1, b2⟩, hA⟩⟩ := q
  simp only [Quarter.HW, Quarter.OnHRedPath, Quarter.thick, hWall]
  cases b2 <;> cases s1 <;> cases s2 <;> rcases κ with k | ⟨α, γ⟩ <;> (try cases k) <;>
    (try cases γ) <;>
    simp [hPath, Thick.hRedAtom, Thick.epE, Thick.epW, Thick.IsCorner, Corner.epE, Corner.epW,
      HAtom.IsRed, Side.toBT]

/-- The walls of a quartering are read off the parent letter at `⌊ξ/2⌋` and the quadrant of `ξ`. -/
theorem VW_quartering (f : Plane → LetterA) (ξ : Plane) :
    (quartering f ξ).VW = (vWall (quad ξ) (f (half ξ)).1).map Side.toLR :=
  VW_eq _

theorem HW_quartering (f : Plane → LetterA) (ξ : Plane) :
    (quartering f ξ).HW = (hWall (quad ξ) (f (half ξ)).1).map Side.toBT :=
  HW_eq _

end UPD.Scaffold

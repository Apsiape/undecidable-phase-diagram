/-
# Section 5.1: corridors and carriers (`prop:routing`)

New in this project. The standing assumption of Section 5 (`Setting ω τ`): `ω` is a legal
configuration whose quarters form a tiling of `𝔸^q` with typical quarter phase `τ`. Column frames
have offsets `a1 τ = phaseOffsets (col τ)`, row frames `a2 τ = phaseOffsets (row τ)`; the owner
depths are `own1`, `own2`.

* Legal configurations: every site value is allowed (`allowed_of_legal`) and neighbouring colours
  match (`matchH_of_legal`, `matchV_of_legal`), field by field.
* `scf:walls` in the form used here (`VW_L`, `VW_R`, `HW_B`, `HW_T`).
* The rows and columns of `ω` as lines (`hline`, `vline`; `Background/Line.lean`), with their
  event tags (`hevline`, `vevline`).
* **`prop:routing`**: (a) `routing_a` (rows), `routing_a_v` (columns), with the existence of the
  nearest walls (`exists_walls_h`, `exists_walls_v`); (b) `routing_b_h`, `routing_b_v`;
  (c) `routing_c`.
-/
import UndecidablePhaseDiagram.Background.Line
import UndecidablePhaseDiagram.Interaction.Basic

set_option autoImplicit false

namespace UPD.BG

open UPD.Scaffold

variable {U : Machine}

/-! ## Legal configurations -/

theorem allowed_of_legal {ω : Config (SiteVal U)} (h : IsLegal (Phi U) ω) (ξ : Plane) :
    (ω ξ).Allowed := by
  have := h {ξ}
  rw [Phi_singleton] at this
  unfold siteEnergy at this
  by_contra hc
  rw [if_neg hc] at this
  exact lt_irrefl _ this

theorem matchH_of_legal {ω : Config (SiteVal U)} (h : IsLegal (Phi U) ω) (ξ : Plane) :
    (ω ξ).cE = (ω (ξ + e1)).cW := by
  have := h {ξ, ξ + e1}
  rw [Phi_pairH] at this
  unfold edgeEnergyH at this
  by_contra hc
  rw [if_neg hc] at this
  exact lt_irrefl _ this

theorem matchV_of_legal {ω : Config (SiteVal U)} (h : IsLegal (Phi U) ω) (ξ : Plane) :
    (ω ξ).cN = (ω (ξ + e2)).cS := by
  have := h {ξ, ξ + e2}
  rw [Phi_pairV] at this
  unfold edgeEnergyV at this
  by_contra hc
  rw [if_neg hc] at this
  exact lt_irrefl _ this

theorem add_e1 (z y : ℤ) : ((z, y) : Plane) + e1 = (z + 1, y) := by simp [e1]

theorem add_e2 (x z : ℤ) : ((x, z) : Plane) + e2 = (x, z + 1) := by simp [e2]

/-! ## The setting of Section 5 -/

/-- Column frame offsets `a^{(1)}_d = τ₁ mod 4^{d+1}`. -/
abbrev a1 (τ : ℕ → Bool × Bool) : ℕ → ℤ := phaseOffsets (col τ)

/-- Row frame offsets `a^{(2)}_d = τ₂ mod 4^{d+1}`. -/
abbrev a2 (τ : ℕ → Bool × Bool) : ℕ → ℤ := phaseOffsets (row τ)

/-- The standing assumption of Section 5: `ω` is a legal configuration whose quarters form a tiling
`Y` of `𝔸^q` with typical quarter phase `τ`. -/
structure Setting (ω : Config (SiteVal U)) (τ : ℕ → Bool × Bool) : Prop where
  legal : IsLegal (Phi U) ω
  phase : IsQPhase (fun ξ => (ω ξ).q) τ
  typical : Typical τ

namespace Setting

variable {ω : Config (SiteVal U)} {τ : ℕ → Bool × Bool} (hs : Setting ω τ)
include hs

theorem allowed (ξ : Plane) : (ω ξ).Allowed := allowed_of_legal hs.legal ξ

theorem O1 (ξ : Plane) : (ω ξ).O1 := (hs.allowed ξ).1
theorem O2 (ξ : Plane) : (ω ξ).O2 := (hs.allowed ξ).2.1
theorem E1 (ξ : Plane) : (ω ξ).E1 := (hs.allowed ξ).2.2.1
theorem E2 (ξ : Plane) : (ω ξ).E2 := (hs.allowed ξ).2.2.2.1
theorem E3 (ξ : Plane) : (ω ξ).E3 := (hs.allowed ξ).2.2.2.2.1
theorem K1 (ξ : Plane) : (ω ξ).K1 := (hs.allowed ξ).2.2.2.2.2.1
theorem K2 (ξ : Plane) : (ω ξ).K2 := (hs.allowed ξ).2.2.2.2.2.2.1
theorem K3 (ξ : Plane) : (ω ξ).K3 := (hs.allowed ξ).2.2.2.2.2.2.2.1
theorem Q1 (ξ : Plane) : (ω ξ).Q1 := (hs.allowed ξ).2.2.2.2.2.2.2.2.1
theorem Q2 (ξ : Plane) : (ω ξ).Q2 := (hs.allowed ξ).2.2.2.2.2.2.2.2.2.1
theorem P1 (ξ : Plane) : (ω ξ).P1 := (hs.allowed ξ).2.2.2.2.2.2.2.2.2.2.1
theorem P2 (ξ : Plane) : (ω ξ).P2 := (hs.allowed ξ).2.2.2.2.2.2.2.2.2.2.2.1
theorem P3 (ξ : Plane) : (ω ξ).P3 := (hs.allowed ξ).2.2.2.2.2.2.2.2.2.2.2.2

theorem mH (z y : ℤ) : (ω (z, y)).cE = (ω (z + 1, y)).cW := by
  have := matchH_of_legal hs.legal (z, y); rwa [add_e1] at this

theorem mV (x z : ℤ) : (ω (x, z)).cN = (ω (x, z + 1)).cS := by
  have := matchV_of_legal hs.legal (x, z); rwa [add_e2] at this

theorem qE_eq (z y : ℤ) : (ω (z, y)).q.colE = (ω (z + 1, y)).q.colW := congrArg (·.1) (hs.mH z y)
theorem oE_eq (z y : ℤ) : (ω (z, y)).oE = (ω (z + 1, y)).oW := congrArg (·.2.1) (hs.mH z y)
theorem eE_eq (z y : ℤ) : (ω (z, y)).eE = (ω (z + 1, y)).eW := congrArg (·.2.2.1) (hs.mH z y)
theorem lE_eq (z y : ℤ) : (ω (z, y)).lE = (ω (z + 1, y)).lW := congrArg (·.2.2.2.1) (hs.mH z y)
theorem rowM_eq (z y : ℤ) : (ω (z, y)).rowM = (ω (z + 1, y)).rowM :=
  congrArg (·.2.2.2.2.1) (hs.mH z y)
theorem wE_eq (z y : ℤ) : (ω (z, y)).wE = (ω (z + 1, y)).wW :=
  congrArg (·.2.2.2.2.2) (hs.mH z y)

theorem qN_eq (x z : ℤ) : (ω (x, z)).q.colN = (ω (x, z + 1)).q.colS := congrArg (·.1) (hs.mV x z)
theorem oN_eq (x z : ℤ) : (ω (x, z)).oN = (ω (x, z + 1)).oS := congrArg (·.2.1) (hs.mV x z)
theorem eN_eq (x z : ℤ) : (ω (x, z)).eN = (ω (x, z + 1)).eS := congrArg (·.2.2.1) (hs.mV x z)
theorem lN_eq (x z : ℤ) : (ω (x, z)).lN = (ω (x, z + 1)).lS := congrArg (·.2.2.2.1) (hs.mV x z)
theorem colM_eq (x z : ℤ) : (ω (x, z)).colM = (ω (x, z + 1)).colM :=
  congrArg (·.2.2.2.2.1) (hs.mV x z)
theorem wN_eq (x z : ℤ) : (ω (x, z)).wN = (ω (x, z + 1)).wS :=
  congrArg (·.2.2.2.2.2) (hs.mV x z)

/-- The tag west of a site is the tag east of its west neighbour. -/
theorem oW_eq (z y : ℤ) : (ω (z, y)).oW = (ω (z - 1, y)).oE := by
  rw [hs.oE_eq, sub_add_cancel]

theorem oS_eq (x z : ℤ) : (ω (x, z)).oS = (ω (x, z - 1)).oN := by
  rw [hs.oN_eq, sub_add_cancel]

/-! ### `scf:walls` for the quarters of `ω` -/

theorem VW_L (z y : ℤ) : (ω (z, y)).q.VW = some .L ↔
    ∃ e, 1 ≤ e ∧ IsLeftEnd (a1 τ) e z ∧ InFrame (a2 τ) e y := by
  have h := walls_VW hs.phase hs.typical.2.1 (z, y) .lo
  refine h.trans ⟨?_, ?_⟩
  · rintro ⟨d, hd, (⟨-, h1⟩ | ⟨h1, -⟩), hy⟩
    · exact ⟨d, hd, h1, hy⟩
    · exact absurd h1 (by decide)
  · rintro ⟨d, hd, h1, hy⟩; exact ⟨d, hd, Or.inl ⟨rfl, h1⟩, hy⟩

theorem VW_R (z y : ℤ) : (ω (z, y)).q.VW = some .R ↔
    ∃ e, 1 ≤ e ∧ IsRightEnd (a1 τ) e z ∧ InFrame (a2 τ) e y := by
  have h := walls_VW hs.phase hs.typical.2.1 (z, y) .hi
  refine h.trans ⟨?_, ?_⟩
  · rintro ⟨d, hd, (⟨h1, -⟩ | ⟨-, h1⟩), hy⟩
    · exact absurd h1 (by decide)
    · exact ⟨d, hd, h1, hy⟩
  · rintro ⟨d, hd, h1, hy⟩; exact ⟨d, hd, Or.inr ⟨rfl, h1⟩, hy⟩

theorem HW_B (x z : ℤ) : (ω (x, z)).q.HW = some .B ↔
    ∃ e, 1 ≤ e ∧ IsLeftEnd (a2 τ) e z ∧ InFrame (a1 τ) e x := by
  have h := walls_HW hs.phase hs.typical.2.2.1 (x, z) .lo
  refine h.trans ⟨?_, ?_⟩
  · rintro ⟨d, hd, (⟨-, h1⟩ | ⟨h1, -⟩), hy⟩
    · exact ⟨d, hd, h1, hy⟩
    · exact absurd h1 (by decide)
  · rintro ⟨d, hd, h1, hy⟩; exact ⟨d, hd, Or.inl ⟨rfl, h1⟩, hy⟩

theorem HW_T (x z : ℤ) : (ω (x, z)).q.HW = some .T ↔
    ∃ e, 1 ≤ e ∧ IsRightEnd (a2 τ) e z ∧ InFrame (a1 τ) e x := by
  have h := walls_HW hs.phase hs.typical.2.2.1 (x, z) .hi
  refine h.trans ⟨?_, ?_⟩
  · rintro ⟨d, hd, (⟨h1, -⟩ | ⟨-, h1⟩), hy⟩
    · exact absurd h1 (by decide)
    · exact ⟨d, hd, h1, hy⟩
  · rintro ⟨d, hd, h1, hy⟩; exact ⟨d, hd, Or.inr ⟨rfl, h1⟩, hy⟩

/-! ### Rows and columns as lines -/

omit hs in
theorem LR_two (s : LR) : s = .L ∨ s = .R := by cases s <;> simp

omit hs in
theorem BT_two (s : BT) : s = .B ∨ s = .T := by cases s <;> simp

/-- The row `y` of `ω` as a line: walls `VW`, tags `o^E`. -/
def hline (y : ℤ) : Line LR where
  L := .L
  R := .R
  hLR := by decide
  two := LR_two
  a := a1 τ
  b := a2 τ
  ha := frameOffsets_phase _
  hb := hs.typical.inFrame_row
  y := y
  W := fun z => (ω (z, y)).q.VW
  wallL := fun z => hs.VW_L z y
  wallR := fun z => hs.VW_R z y
  o := fun z => (ω (z, y)).oE
  copy := fun z hW => ((hs.O1 (z + 1, y)).1 hW).symm.trans (hs.oE_eq z y).symm
  left := fun z s hW => by
    rcases LR_two s with rfl | rfl
    · exact ((hs.O1 (z, y)).2.1 hW).2
    · exact ((hs.O1 (z, y)).2.2 hW).2
  right := fun z s hW => by
    rw [hs.oE_eq]
    rcases LR_two s with rfl | rfl
    · exact ((hs.O1 (z + 1, y)).2.1 hW).1
    · exact ((hs.O1 (z + 1, y)).2.2 hW).1

/-- The column `x` of `ω` as a line: walls `HW`, tags `o^N`. -/
def vline (x : ℤ) : Line BT where
  L := .B
  R := .T
  hLR := by decide
  two := BT_two
  a := a2 τ
  b := a1 τ
  ha := frameOffsets_phase _
  hb := hs.typical.inFrame_col
  y := x
  W := fun z => (ω (x, z)).q.HW
  wallL := fun z => hs.HW_B x z
  wallR := fun z => hs.HW_T x z
  o := fun z => (ω (x, z)).oN
  copy := fun z hW => ((hs.O2 (x, z + 1)).1 hW).symm.trans (hs.oN_eq x z).symm
  left := fun z s hW => by
    rcases BT_two s with rfl | rfl
    · exact ((hs.O2 (x, z)).2.1 hW).2
    · exact ((hs.O2 (x, z)).2.2 hW).2
  right := fun z s hW => by
    rw [hs.oN_eq]
    rcases BT_two s with rfl | rfl
    · exact ((hs.O2 (x, z + 1)).2.1 hW).1
    · exact ((hs.O2 (x, z + 1)).2.2 hW).1

/-- The owner depth `own₁` of a column coordinate. -/
noncomputable abbrev own1 (z : ℤ) : ℕ := own (a1 τ) hs.typical.inFrame_col z

/-- The owner depth `own₂` of a row coordinate. -/
noncomputable abbrev own2 (y : ℤ) : ℕ := own (a2 τ) hs.typical.inFrame_row y

theorem hline_d0 (y : ℤ) : (hs.hline y).d0 = hs.own2 y := rfl

theorem vline_d0 (x : ℤ) : (hs.vline x).d0 = hs.own1 x := rfl

/-! ## `prop:routing` -/

/-- **`prop:routing`(a)** (rows). Let `w₋ ≤ ξ₁` be the largest wall of row `ξ₂` at or west of
`ξ`, and `w₊ ≥ ξ₁ + 1` the smallest wall at or east of `ξ + e₁`. Then
`o^E(ξ) = o^W(ξ + e₁)` is the pair of the sides of `w₋` and `w₊`. -/
theorem routing_a {ξ : Plane} {wl wr : ℤ} {sl sr : LR}
    (hl : wl ≤ ξ.1) (hwl : (ω (wl, ξ.2)).q.VW = some sl)
    (hl' : ∀ x, wl < x → x ≤ ξ.1 → (ω (x, ξ.2)).q.VW = none)
    (hr : ξ.1 + 1 ≤ wr) (hwr : (ω (wr, ξ.2)).q.VW = some sr)
    (hr' : ∀ x, ξ.1 + 1 ≤ x → x < wr → (ω (x, ξ.2)).q.VW = none) :
    (ω ξ).oE = (sl, sr) ∧ (ω (ξ + e1)).oW = (sl, sr) := by
  obtain ⟨z, y⟩ := ξ
  have h := (hs.hline y).routing (z := z) hl hwl hl' (by simpa using hr) hwr
    (fun x h1 h2 => hr' x (by simpa using h1) h2)
  refine ⟨h, ?_⟩
  rw [add_e1, ← hs.oE_eq]; exact h

/-- **`prop:routing`(a)** (columns): the vertical tags are described in the same way. -/
theorem routing_a_v {ξ : Plane} {wl wr : ℤ} {sl sr : BT}
    (hl : wl ≤ ξ.2) (hwl : (ω (ξ.1, wl)).q.HW = some sl)
    (hl' : ∀ x, wl < x → x ≤ ξ.2 → (ω (ξ.1, x)).q.HW = none)
    (hr : ξ.2 + 1 ≤ wr) (hwr : (ω (ξ.1, wr)).q.HW = some sr)
    (hr' : ∀ x, ξ.2 + 1 ≤ x → x < wr → (ω (ξ.1, x)).q.HW = none) :
    (ω ξ).oN = (sl, sr) ∧ (ω (ξ + e2)).oS = (sl, sr) := by
  obtain ⟨x, z⟩ := ξ
  have h := (hs.vline x).routing (z := z) hl hwl hl' (by simpa using hr) hwr
    (fun x h1 h2 => hr' x (by simpa using h1) h2)
  refine ⟨h, ?_⟩
  rw [add_e2, ← hs.oN_eq]; exact h

/-- The walls of a row are unbounded on both sides, so the walls `w₋`, `w₊` of `prop:routing`(a)
exist for every site. -/
theorem exists_walls_h (ξ : Plane) : ∃ wl wr : ℤ, ∃ sl sr : LR,
    wl ≤ ξ.1 ∧ (ω (wl, ξ.2)).q.VW = some sl ∧ (∀ x, wl < x → x ≤ ξ.1 → (ω (x, ξ.2)).q.VW = none) ∧
    ξ.1 + 1 ≤ wr ∧ (ω (wr, ξ.2)).q.VW = some sr ∧
      (∀ x, ξ.1 + 1 ≤ x → x < wr → (ω (x, ξ.2)).q.VW = none) := by
  obtain ⟨z, y⟩ := ξ
  set l := hs.hline y
  obtain ⟨wl, ⟨hl1, hl2⟩, hlmax⟩ := Int.exists_greatest_of_bdd
    (P := fun x => x ≤ z ∧ l.W x ≠ none) ⟨z, fun x hx => hx.1⟩
    (by obtain ⟨w, hw, hw'⟩ := l.exists_wall_lt (z + 1); exact ⟨w, by omega, hw'⟩)
  obtain ⟨wr, ⟨hr1, hr2⟩, hrmin⟩ := Int.exists_least_of_bdd
    (P := fun x => z + 1 ≤ x ∧ l.W x ≠ none) ⟨z + 1, fun x hx => hx.1⟩
    (by obtain ⟨w, hw, hw'⟩ := l.exists_wall_gt z; exact ⟨w, by omega, hw'⟩)
  obtain ⟨sl, hsl⟩ := Option.ne_none_iff_exists'.1 hl2
  obtain ⟨sr, hsr⟩ := Option.ne_none_iff_exists'.1 hr2
  refine ⟨wl, wr, sl, sr, hl1, hsl, fun x h1 h2 => ?_, hr1, hsr, fun x h1 h2 => ?_⟩
  · by_contra hx; have := hlmax x ⟨h2, hx⟩; omega
  · by_contra hx; have := hrmin x ⟨h1, hx⟩; omega

theorem exists_walls_v (ξ : Plane) : ∃ wl wr : ℤ, ∃ sl sr : BT,
    wl ≤ ξ.2 ∧ (ω (ξ.1, wl)).q.HW = some sl ∧ (∀ x, wl < x → x ≤ ξ.2 → (ω (ξ.1, x)).q.HW = none) ∧
    ξ.2 + 1 ≤ wr ∧ (ω (ξ.1, wr)).q.HW = some sr ∧
      (∀ x, ξ.2 + 1 ≤ x → x < wr → (ω (ξ.1, x)).q.HW = none) := by
  obtain ⟨x0, z⟩ := ξ
  set l := hs.vline x0
  obtain ⟨wl, ⟨hl1, hl2⟩, hlmax⟩ := Int.exists_greatest_of_bdd
    (P := fun x => x ≤ z ∧ l.W x ≠ none) ⟨z, fun x hx => hx.1⟩
    (by obtain ⟨w, hw, hw'⟩ := l.exists_wall_lt (z + 1); exact ⟨w, by omega, hw'⟩)
  obtain ⟨wr, ⟨hr1, hr2⟩, hrmin⟩ := Int.exists_least_of_bdd
    (P := fun x => z + 1 ≤ x ∧ l.W x ≠ none) ⟨z + 1, fun x hx => hx.1⟩
    (by obtain ⟨w, hw, hw'⟩ := l.exists_wall_gt z; exact ⟨w, by omega, hw'⟩)
  obtain ⟨sl, hsl⟩ := Option.ne_none_iff_exists'.1 hl2
  obtain ⟨sr, hsr⟩ := Option.ne_none_iff_exists'.1 hr2
  refine ⟨wl, wr, sl, sr, hl1, hsl, fun x h1 h2 => ?_, hr1, hsr, fun x h1 h2 => ?_⟩
  · by_contra hx; have := hlmax x ⟨h2, hx⟩; omega
  · by_contra hx; have := hrmin x ⟨h1, hx⟩; omega

/-- **`prop:routing`(b)** (rows): `ξ` is a horizontal carrier iff `ξ₁` lies in the interior of a
column frame of depth `own₂(ξ₂)`. -/
theorem routing_b_h (ξ : Plane) : (ω ξ).IsHCarrier ↔
    ∃ m, frameLo (a1 τ) (hs.own2 ξ.2) m < ξ.1 ∧ ξ.1 < frameHi (a1 τ) (hs.own2 ξ.2) m := by
  obtain ⟨z, y⟩ := ξ
  set l := hs.hline y
  have ho : (ω (z, y)).oW = l.o (z - 1) := hs.oW_eq z y
  constructor
  · rintro ⟨hW, hoW⟩
    rw [ho] at hoW
    exact (l.carrier_iff hW).1 hoW
  · rintro ⟨m, h1, h2⟩
    have hW : l.W z = none := l.interior_none h1 h2
    exact ⟨hW, by rw [ho]; exact (l.carrier_iff hW).2 ⟨m, h1, h2⟩⟩

/-- **`prop:routing`(b)** (columns): `ξ` is a vertical carrier iff `ξ₂` lies in the interior of a
row frame of depth `own₁(ξ₁)`. -/
theorem routing_b_v (ξ : Plane) : (ω ξ).IsVCarrier ↔
    ∃ m, frameLo (a2 τ) (hs.own1 ξ.1) m < ξ.2 ∧ ξ.2 < frameHi (a2 τ) (hs.own1 ξ.1) m := by
  obtain ⟨x, z⟩ := ξ
  set l := hs.vline x
  have ho : (ω (x, z)).oS = l.o (z - 1) := hs.oS_eq x z
  constructor
  · rintro ⟨hW, hoS⟩
    rw [ho] at hoS
    exact (l.carrier_iff hW).1 hoS
  · rintro ⟨m, h1, h2⟩
    have hW : l.W z = none := l.interior_none h1 h2
    exact ⟨hW, by rw [ho]; exact (l.carrier_iff hW).2 ⟨m, h1, h2⟩⟩

end Setting

/-! ## Owner depths of free coordinates -/

/-- A free coordinate of depth `d` has owner depth `d`. -/
theorem own_eq_of_isFree {a : ℕ → ℤ} {h : ∀ z, ∃ d, 1 ≤ d ∧ InFrame a d z} {d : ℕ} {m z : ℤ}
    (hd : 1 ≤ d) (hz : IsFree a d m z) : own a h z = d := by
  apply le_antisymm (own_le a h hd ⟨m, hz.1.le, hz.2.1.le⟩)
  by_contra hlt
  push Not at hlt
  exact hz.2.2 _ (own_spec a h z).1 hlt (own_spec a h z).2

/-- An interior point of a frame of its owner depth is free. -/
theorem isFree_own {a : ℕ → ℤ} {h : ∀ z, ∃ d, 1 ≤ d ∧ InFrame a d z} {m z : ℤ}
    (h1 : frameLo a (own a h z) m < z) (h2 : z < frameHi a (own a h z) m) :
    IsFree a (own a h z) m z := by
  refine ⟨h1, h2, fun e he hlt hin => ?_⟩
  exact Nat.find_min (h z) hlt ⟨he, hin⟩

namespace Setting

variable {ω : Config (SiteVal U)} {τ : ℕ → Bool × Bool} (hs : Setting ω τ)
include hs

/-- **`prop:routing`(c)**: `ξ` is active iff `ξ ∈ 𝓕^{(1)}_d(m₁) × 𝓕^{(2)}_d(m₂)` for some
`d ≥ 1` and `m₁, m₂ ∈ ℤ`. -/
theorem routing_c (ξ : Plane) : (ω ξ).IsActive ↔
    ∃ d m1 m2, 1 ≤ d ∧ IsFree (a1 τ) d m1 ξ.1 ∧ IsFree (a2 τ) d m2 ξ.2 := by
  constructor
  · rintro ⟨hH, hV⟩
    obtain ⟨m1, h1, h1'⟩ := (hs.routing_b_h ξ).1 hH
    obtain ⟨m2, h2, h2'⟩ := (hs.routing_b_v ξ).1 hV
    have hle1 : hs.own1 ξ.1 ≤ hs.own2 ξ.2 :=
      own_le _ _ (own_spec (a2 τ) hs.typical.inFrame_row ξ.2).1 ⟨m1, h1.le, h1'.le⟩
    have hle2 : hs.own2 ξ.2 ≤ hs.own1 ξ.1 :=
      own_le _ _ (own_spec (a1 τ) hs.typical.inFrame_col ξ.1).1 ⟨m2, h2.le, h2'.le⟩
    have heq : hs.own2 ξ.2 = hs.own1 ξ.1 := le_antisymm hle2 hle1
    rw [heq] at h1 h1'
    refine ⟨hs.own1 ξ.1, m1, m2, (own_spec (a1 τ) hs.typical.inFrame_col ξ.1).1,
      isFree_own (a := a1 τ) (h := hs.typical.inFrame_col) h1 h1', ?_⟩
    rw [← heq] at h2 h2'
    have := isFree_own (a := a2 τ) (h := hs.typical.inFrame_row) h2 h2'
    rwa [show own (a2 τ) hs.typical.inFrame_row ξ.2 = hs.own1 ξ.1 from heq] at this
  · rintro ⟨d, m1, m2, hd, h1, h2⟩
    have e1 : hs.own1 ξ.1 = d := own_eq_of_isFree hd h1
    have e2 : hs.own2 ξ.2 = d := own_eq_of_isFree hd h2
    refine ⟨(hs.routing_b_h ξ).2 ⟨m1, ?_, ?_⟩, (hs.routing_b_v ξ).2 ⟨m2, ?_, ?_⟩⟩
    · rw [e2]; exact h1.1
    · rw [e2]; exact h1.2.1
    · rw [e1]; exact h2.1
    · rw [e1]; exact h2.2.1

/-! ## Event tags along rows and columns -/

/-- The row `y` with its event tags `e^E`, `e^W` and its active sites. -/
def hevline (y : ℤ) : EvLine LR where
  toLine := hs.hline y
  eR := fun z => (ω (z, y)).eE
  eL := fun z => (ω (z, y)).eW
  act := fun z => (ω (z, y)).IsActive
  ev_match := fun z => hs.eE_eq z y
  ev_copy := fun z hW ho hna => by
    have hH : (ω (z, y)).IsHCarrier := ⟨hW, by rw [hs.oW_eq]; exact ho⟩
    exact (hs.E2 (z, y)).1 ⟨hH, fun hV => hna ⟨hH, hV⟩⟩
  ev_actL := fun z ha => ((hs.E2 (z, y)).2.1 ha).1
  ev_actR := fun z ha => ((hs.E2 (z, y)).2.1 ha).2
  ev_wallL := fun z hW ho => (hs.E2 (z, y)).2.2.1 ⟨hW, ho⟩
  ev_wallR := fun z hW ho => (hs.E2 (z, y)).2.2.2 ⟨hW, by rw [hs.oW_eq]; exact ho⟩

/-- The column `x` with its event tags `e^N`, `e^S` and its active sites. -/
def vevline (x : ℤ) : EvLine BT where
  toLine := hs.vline x
  eR := fun z => (ω (x, z)).eN
  eL := fun z => (ω (x, z)).eS
  act := fun z => (ω (x, z)).IsActive
  ev_match := fun z => hs.eN_eq x z
  ev_copy := fun z hW ho hna => by
    have hV : (ω (x, z)).IsVCarrier := ⟨hW, by rw [hs.oS_eq]; exact ho⟩
    exact (hs.E3 (x, z)).1 ⟨hV, fun hH => hna ⟨hH, hV⟩⟩
  ev_actL := fun z ha => ((hs.E3 (x, z)).2.1 ha).1
  ev_actR := fun z ha => ((hs.E3 (x, z)).2.1 ha).2
  ev_wallL := fun z hW ho => (hs.E3 (x, z)).2.2.1 ⟨hW, ho⟩
  ev_wallR := fun z hW ho => (hs.E3 (x, z)).2.2.2 ⟨hW, by rw [hs.oS_eq]; exact ho⟩

end Setting

end UPD.BG

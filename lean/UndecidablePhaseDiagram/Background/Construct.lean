/-
# Section 5.4: the background exists (`prop:background`(b))

New in this project. "(b) For every typical `τ`, the configuration with background `𝔟_τ`,
arbitrary spins, wire values given by (P1) and (P2) from the spins at the roots, and all switches
and free bits equal to `0`, is legal."

The configuration is defined site by site from the classification used in the uniqueness proof
(`Background/Unique.lean`):

* nearest walls along a line (`wdL`, `wdR`) and the tags `wtag` (`prop:routing`(a) as a
  definition); a line given by its walls (`WLine`) becomes a `Line` (`WLine.toLine`), so the
  results of `Background/Line.lean` (carriers, frames) apply to the constructed tags;
* event tags `evTag` (the formula of `EvLine.ev_det`); with any notion of activity contained in
  the carriers, a `WLine` becomes an `EvLine` (`WLine.toEvLine`);
* the configuration `cfg U τ σ` (spins `σ`): quarters `Y_τ`, tags, event tags, logical colours
  `hcolFormula`/`vcolFormula` on the channels of the grids, cell records `cellFormula`, markers
  by `bg:markers`(a), wires from the spins at the roots, switches and free bits `0`;
* **`cfg_legal`**: for typical `τ` it is legal.
-/
import UndecidablePhaseDiagram.Background.Freeze
import UndecidablePhaseDiagram.Scaffold.TILaw

set_option autoImplicit false

namespace UPD.BG

open UPD.Scaffold

/-! ## Nearest walls along a line -/

section NearestWalls

variable {S : Type} (W : ℤ → Option S)

open Classical in
/-- The distance from `z` down to the nearest wall at or below `z` (`0` if there is none). -/
noncomputable def wdL (z : ℤ) : ℕ :=
  if h : ∃ n : ℕ, W (z - n) ≠ none then Nat.find h else 0

open Classical in
/-- The distance from `z + 1` up to the nearest wall at or above `z + 1` (`0` if there is none). -/
noncomputable def wdR (z : ℤ) : ℕ :=
  if h : ∃ n : ℕ, W (z + 1 + n) ≠ none then Nat.find h else 0

/-- `prop:routing`(a) as a definition: the tag of the edge `(z, z + 1)` is the pair of the sides
of the nearest walls (`dflt` where there is none). -/
noncomputable def wtag (dflt : S) (z : ℤ) : S × S :=
  ((W (z - wdL W z)).getD dflt, (W (z + 1 + wdR W z)).getD dflt)

variable {W}

theorem wdL_spec {z : ℤ} (h : ∃ n : ℕ, W (z - n) ≠ none) :
    W (z - wdL W z) ≠ none ∧ ∀ k : ℕ, k < wdL W z → W (z - k) = none := by
  classical
  rw [wdL, dif_pos h]
  exact ⟨Nat.find_spec h, fun k hk => by by_contra hc; exact Nat.find_min h hk hc⟩

theorem wdR_spec {z : ℤ} (h : ∃ n : ℕ, W (z + 1 + n) ≠ none) :
    W (z + 1 + wdR W z) ≠ none ∧ ∀ k : ℕ, k < wdR W z → W (z + 1 + k) = none := by
  classical
  rw [wdR, dif_pos h]
  exact ⟨Nat.find_spec h, fun k hk => by by_contra hc; exact Nat.find_min h hk hc⟩

theorem wdL_eq {z : ℤ} {n : ℕ} (hn : W (z - n) ≠ none) (hk : ∀ k : ℕ, k < n → W (z - k) = none) :
    wdL W z = n := by
  obtain ⟨h1, h2⟩ := wdL_spec ⟨n, hn⟩
  rcases lt_trichotomy (wdL W z) n with hlt | heq | hgt
  · exact absurd (hk _ hlt) h1
  · exact heq
  · exact absurd (h2 n hgt) hn

theorem wdR_eq {z : ℤ} {n : ℕ} (hn : W (z + 1 + n) ≠ none)
    (hk : ∀ k : ℕ, k < n → W (z + 1 + k) = none) : wdR W z = n := by
  obtain ⟨h1, h2⟩ := wdR_spec ⟨n, hn⟩
  rcases lt_trichotomy (wdR W z) n with hlt | heq | hgt
  · exact absurd (hk _ hlt) h1
  · exact heq
  · exact absurd (h2 n hgt) hn

theorem wdL_zero {z : ℤ} (h : W z ≠ none) : wdL W z = 0 :=
  wdL_eq (by simpa using h) (fun k hk => absurd hk (Nat.not_lt_zero k))

theorem wdR_zero {z : ℤ} (h : W (z + 1) ≠ none) : wdR W z = 0 :=
  wdR_eq (by simpa using h) (fun k hk => absurd hk (Nat.not_lt_zero k))

variable (hlo : ∀ z, ∃ n : ℕ, W (z - n) ≠ none) (hhi : ∀ z, ∃ n : ℕ, W (z + 1 + n) ≠ none)
include hlo hhi

omit hhi in
theorem wdL_succ {z : ℤ} (hz : W (z + 1) = none) : wdL W (z + 1) = wdL W z + 1 := by
  obtain ⟨h1, h2⟩ := wdL_spec (hlo z)
  refine wdL_eq ?_ ?_
  · rw [show z + 1 - ((wdL W z + 1 : ℕ) : ℤ) = z - wdL W z by push_cast; ring]; exact h1
  · intro k hk
    rcases k with _ | k
    · simpa using hz
    · rw [show z + 1 - ((k + 1 : ℕ) : ℤ) = z - k by push_cast; ring]; exact h2 k (by omega)

omit hlo in
theorem wdR_pred {z : ℤ} (hz : W (z + 1) = none) : wdR W z = wdR W (z + 1) + 1 := by
  obtain ⟨h1, h2⟩ := wdR_spec (hhi (z + 1))
  refine wdR_eq ?_ ?_
  · rw [show z + 1 + ((wdR W (z + 1) + 1 : ℕ) : ℤ) = z + 1 + 1 + wdR W (z + 1) by push_cast; ring]
    exact h1
  · intro k hk
    rcases k with _ | k
    · simpa using hz
    · rw [show z + 1 + ((k + 1 : ℕ) : ℤ) = z + 1 + 1 + k by push_cast; ring]; exact h2 k (by omega)

/-- (O1) at a non-wall, with matching: the tag is copied. -/
theorem wtag_copy (dflt : S) {z : ℤ} (hz : W (z + 1) = none) : wtag W dflt (z + 1) = wtag W dflt z := by
  unfold wtag
  rw [wdL_succ hlo hz, wdR_pred hhi hz,
    show z + 1 - ((wdL W z + 1 : ℕ) : ℤ) = z - wdL W z by push_cast; ring,
    show z + 1 + ((wdR W (z + 1) + 1 : ℕ) : ℤ) = z + 1 + 1 + wdR W (z + 1) by push_cast; ring]

omit hlo hhi in
/-- (O1) at a wall: the first entry of the tag east of it is its side. -/
theorem wtag_left (dflt : S) {z : ℤ} {s : S} (h : W z = some s) : (wtag W dflt z).1 = s := by
  simp [wtag, wdL_zero (W := W) (z := z) (by simp [h]), h]

omit hlo hhi in
/-- (O1) at a wall, with matching: the second entry of the tag west of it is its side. -/
theorem wtag_right (dflt : S) {z : ℤ} {s : S} (h : W (z + 1) = some s) : (wtag W dflt z).2 = s := by
  simp [wtag, wdR_zero (W := W) (z := z) (by simp [h]), h]

end NearestWalls

/-! ## Lines given by their walls -/

/-- The data of a `Line` without the tags: the walls, with their frame description
(`scf:walls`). -/
structure WLine (S : Type) where
  /-- the left (bottom) side -/
  L : S
  /-- the right (top) side -/
  R : S
  hLR : L ≠ R
  two : ∀ s : S, s = L ∨ s = R
  /-- offsets of the frames along the line -/
  a : ℕ → ℤ
  /-- offsets of the frames across the line -/
  b : ℕ → ℤ
  ha : FrameOffsets a
  hb : ∀ z, ∃ d, 1 ≤ d ∧ InFrame b d z
  /-- the cross coordinate of the line -/
  y : ℤ
  /-- the walls -/
  W : ℤ → Option S
  wallL : ∀ z, W z = some L ↔ ∃ e, 1 ≤ e ∧ IsLeftEnd a e z ∧ InFrame b e y
  wallR : ∀ z, W z = some R ↔ ∃ e, 1 ≤ e ∧ IsRightEnd a e z ∧ InFrame b e y

namespace WLine

variable {S : Type} (w : WLine S)

theorem below (z : ℤ) : ∃ n : ℕ, w.W (z - n) ≠ none := by
  obtain ⟨m, hm⟩ := Line.frameLo_lt w.a (own w.b w.hb w.y) z
  refine ⟨(z - frameLo w.a (own w.b w.hb w.y) m).toNat, ?_⟩
  rw [show z - ((z - frameLo w.a (own w.b w.hb w.y) m).toNat : ℤ) =
      frameLo w.a (own w.b w.hb w.y) m by omega,
    (w.wallL _).2 ⟨_, (own_spec w.b w.hb w.y).1, ⟨m, rfl⟩, (own_spec w.b w.hb w.y).2⟩]
  simp

theorem above (z : ℤ) : ∃ n : ℕ, w.W (z + 1 + n) ≠ none := by
  obtain ⟨m, hm⟩ := Line.lt_frameHi w.a (own w.b w.hb w.y) z
  refine ⟨(frameHi w.a (own w.b w.hb w.y) m - z - 1).toNat, ?_⟩
  rw [show z + 1 + ((frameHi w.a (own w.b w.hb w.y) m - z - 1).toNat : ℤ) =
      frameHi w.a (own w.b w.hb w.y) m by omega,
    (w.wallR _).2 ⟨_, (own_spec w.b w.hb w.y).1, ⟨m, rfl⟩, (own_spec w.b w.hb w.y).2⟩]
  simp

/-- A line given by its walls, with the tags `wtag` of `prop:routing`(a). -/
noncomputable def toLine : Line S where
  L := w.L
  R := w.R
  hLR := w.hLR
  two := w.two
  a := w.a
  b := w.b
  ha := w.ha
  hb := w.hb
  y := w.y
  W := w.W
  wallL := w.wallL
  wallR := w.wallR
  o := wtag w.W w.L
  copy := fun _ hW => wtag_copy w.below w.above _ hW
  left := fun _ _ hW => wtag_left _ hW
  right := fun _ _ hW => wtag_right _ hW

theorem toLine_o : w.toLine.o = wtag w.W w.L := rfl

end WLine

/-! ## Event tags -/

open Classical in
/-- The event tag of the edge `(z, z + 1)` (the formula of `EvLine.ev_det`): `*` off the tags
`(L, R)`; otherwise the first entry is `cell` iff there is an active site between the nearest wall
at or below `z` and `z`, the second iff there is one between `z + 1` and the nearest wall above. -/
noncomputable def evTag {S : Type} (W : ℤ → Option S) (L R : S) (act : ℤ → Prop) (z : ℤ) :
    Option (Ev × Ev) :=
  if wtag W L z = (L, R) then
    some ((if ∃ x, z - (wdL W z : ℤ) < x ∧ x ≤ z ∧ act x then Ev.cell else Ev.wall),
      (if ∃ x, z < x ∧ x < z + 1 + (wdR W z : ℤ) ∧ act x then Ev.cell else Ev.wall))
  else none

namespace WLine

variable {S : Type} (w : WLine S) (act : ℤ → Prop)

theorem evTag_copy {z : ℤ} (hW : w.W (z + 1) = none) (hna : ¬ act (z + 1)) :
    evTag w.W w.L w.R act (z + 1) = evTag w.W w.L w.R act z := by
  classical
  have hc := wtag_copy w.below w.above w.L hW
  have hl := wdL_succ w.below hW
  have hr := wdR_pred w.above hW
  unfold evTag
  rw [hc]
  by_cases h : wtag w.W w.L z = (w.L, w.R)
  · rw [if_pos h, if_pos h]
    have e1 : (∃ x, z + 1 - (wdL w.W (z + 1) : ℤ) < x ∧ x ≤ z + 1 ∧ act x) ↔
        (∃ x, z - (wdL w.W z : ℤ) < x ∧ x ≤ z ∧ act x) := by
      rw [hl]; push_cast
      constructor
      · rintro ⟨x, h1, h2, h3⟩
        refine ⟨x, by omega, ?_, h3⟩
        by_contra hc'; exact hna (by rw [show z + 1 = x by omega]; exact h3)
      · rintro ⟨x, h1, h2, h3⟩; exact ⟨x, by omega, by omega, h3⟩
    have e2 : (∃ x, z + 1 < x ∧ x < z + 1 + 1 + (wdR w.W (z + 1) : ℤ) ∧ act x) ↔
        (∃ x, z < x ∧ x < z + 1 + (wdR w.W z : ℤ) ∧ act x) := by
      rw [hr]; push_cast
      constructor
      · rintro ⟨x, h1, h2, h3⟩; exact ⟨x, by omega, by omega, h3⟩
      · rintro ⟨x, h1, h2, h3⟩
        refine ⟨x, ?_, by omega, h3⟩
        by_contra hc'; exact hna (by rw [show z + 1 = x by omega]; exact h3)
    simp only [Option.some.injEq, Prod.mk.injEq]
    exact ⟨if_congr e1 rfl rfl, if_congr e2 rfl rfl⟩
  · rw [if_neg h, if_neg h]

theorem wdL_pos {z : ℤ} (h : w.W z = none) : 1 ≤ wdL w.W z := by
  rcases Nat.eq_zero_or_pos (wdL w.W z) with h0 | h0
  · have := (wdL_spec (w.below z)).1
    rw [h0, Nat.cast_zero, sub_zero] at this; exact absurd h this
  · exact h0

theorem wdR_pos {z : ℤ} (h : w.W (z + 1) = none) : 1 ≤ wdR w.W z := by
  rcases Nat.eq_zero_or_pos (wdR w.W z) with h0 | h0
  · have := (wdR_spec (w.above z)).1
    rw [h0, Nat.cast_zero, add_zero] at this; exact absurd h this
  · exact h0

/-- `act` lies inside the carriers: an active site is no wall and has the tag `(L, R)` west of
it. -/
def ActOK : Prop := ∀ z, act z → w.W z = none ∧ wtag w.W w.L (z - 1) = (w.L, w.R)

variable {act}

theorem evTag_actL (hact : w.ActOK act) {z : ℤ} (ha : act z) :
    Ev.SecondIs (evTag w.W w.L w.R act (z - 1)) .cell := by
  classical
  obtain ⟨hW, ho⟩ := hact z ha
  have hR := w.wdR_pos (z := z - 1) (by rw [sub_add_cancel]; exact hW)
  rw [evTag, if_pos ho]
  have hx : ∃ x, z - 1 < x ∧ x < z - 1 + 1 + (wdR w.W (z - 1) : ℤ) ∧ act x :=
    ⟨z, by omega, by omega, ha⟩
  exact ⟨_, by rw [if_pos hx]⟩

theorem evTag_actR (hact : w.ActOK act) {z : ℤ} (ha : act z) :
    Ev.FirstIs (evTag w.W w.L w.R act z) .cell := by
  classical
  obtain ⟨hW, ho⟩ := hact z ha
  have hc := wtag_copy w.below w.above w.L (z := z - 1) (by rw [sub_add_cancel]; exact hW)
  rw [sub_add_cancel] at hc
  have hL := w.wdL_pos hW
  rw [evTag, if_pos (hc.trans ho)]
  have hx : ∃ x, z - (wdL w.W z : ℤ) < x ∧ x ≤ z ∧ act x := ⟨z, by omega, le_rfl, ha⟩
  exact ⟨_, by rw [if_pos hx]⟩

theorem evTag_wallL {z : ℤ} (hW : w.W z = some w.L) (ho : wtag w.W w.L z = (w.L, w.R)) :
    Ev.FirstIs (evTag w.W w.L w.R act z) .wall := by
  classical
  have h0 := wdL_zero (W := w.W) (z := z) (by simp [hW])
  rw [evTag, if_pos ho]
  have hx : ¬ ∃ x, z - (wdL w.W z : ℤ) < x ∧ x ≤ z ∧ act x := by
    rintro ⟨x, h1, h2, -⟩; rw [h0] at h1; push_cast at h1; omega
  exact ⟨_, by rw [if_neg hx]⟩

theorem evTag_wallR {z : ℤ} (hW : w.W z = some w.R) (ho : wtag w.W w.L (z - 1) = (w.L, w.R)) :
    Ev.SecondIs (evTag w.W w.L w.R act (z - 1)) .wall := by
  classical
  have h0 := wdR_zero (W := w.W) (z := z - 1) (by rw [sub_add_cancel]; simp [hW])
  rw [evTag, if_pos ho]
  have hx : ¬ ∃ x, z - 1 < x ∧ x < z - 1 + 1 + (wdR w.W (z - 1) : ℤ) ∧ act x := by
    rintro ⟨x, h1, h2, -⟩; rw [h0] at h2; push_cast at h2; omega
  exact ⟨_, by rw [if_neg hx]⟩

/-- A line given by its walls, with the event tags `evTag` of a notion of activity inside the
carriers. -/
noncomputable def toEvLine (hact : w.ActOK act) : EvLine S where
  toLine := w.toLine
  eR := evTag w.W w.L w.R act
  eL := fun z => evTag w.W w.L w.R act (z - 1)
  act := act
  ev_match := fun z => by simp only [add_sub_cancel_right]
  ev_copy := fun z hW _ hna => by
    have := w.evTag_copy act (z := z - 1) (by rw [sub_add_cancel]; exact hW)
      (by rw [sub_add_cancel]; exact hna)
    rw [sub_add_cancel] at this
    exact this.symm
  ev_actL := fun _ ha => w.evTag_actL hact ha
  ev_actR := fun _ ha => w.evTag_actR hact ha
  ev_wallL := fun _ hW ho => w.evTag_wallL hW ho
  ev_wallR := fun _ hW ho => w.evTag_wallR hW ho

theorem toEvLine_toLine (hact : w.ActOK act) : (w.toEvLine hact).toLine = w.toLine := rfl

end WLine

/-! ## The configuration -/

section Defs

variable (U : Machine) (τ : ℕ → Bool × Bool)

/-- The walls `VW` of the row `y` of `Y_τ`. -/
noncomputable def rowW (y : ℤ) : ℤ → Option LR := fun z => (qtilingOf τ (z, y)).VW

/-- The walls `HW` of the column `x` of `Y_τ`. -/
noncomputable def colW (x : ℤ) : ℤ → Option BT := fun z => (qtilingOf τ (x, z)).HW

/-- `o^E` at `ξ` (`prop:routing`(a)). -/
noncomputable def oEc (ξ : Plane) : LR × LR := wtag (rowW τ ξ.2) .L ξ.1

/-- `o^N` at `ξ`. -/
noncomputable def oNc (ξ : Plane) : BT × BT := wtag (colW τ ξ.1) .B ξ.2

/-- The active sites, through frames (`prop:routing`(c)). -/
def actF (ξ : Plane) : Prop :=
  ∃ d m1 m2, 1 ≤ d ∧ IsFree (a1 τ) d m1 ξ.1 ∧ IsFree (a2 τ) d m2 ξ.2

/-- `e^E` at `ξ`. -/
noncomputable def eEc (ξ : Plane) : Option (Ev × Ev) :=
  evTag (rowW τ ξ.2) .L .R (fun x => actF τ (x, ξ.2)) ξ.1

/-- `e^N` at `ξ`. -/
noncomputable def eNc (ξ : Plane) : Option (Ev × Ev) :=
  evTag (colW τ ξ.1) .B .T (fun z => actF τ (ξ.1, z)) ξ.2

/-- The horizontal channel of `ξ(i, j)` in `G_d`: `ξ` lies on the row of `ξ(i, j)`, with
`ζ_i ≤ ξ₁ < ζ_{i+1}` (`p = (d, i, j)`). -/
def HSeg (p : ℕ × ℕ × ℕ) (ξ : Plane) : Prop :=
  1 ≤ p.1 ∧ p.2.1 + 1 < MachineM.Nd p.1 ∧ p.2.2 < MachineM.Nd p.1 ∧ ∃ m1 m2 : ℤ,
    ξ.2 = zeta (a2 τ) p.1 m2 p.2.2 ∧ zeta (a1 τ) p.1 m1 p.2.1 ≤ ξ.1 ∧
      ξ.1 < zeta (a1 τ) p.1 m1 (p.2.1 + 1)

/-- The vertical channel of `ξ(i, j)` in `G_d`: `ξ` lies on the column of `ξ(i, j)`, with
`ζ_j ≤ ξ₂ < ζ_{j+1}`. -/
def VSeg (p : ℕ × ℕ × ℕ) (ξ : Plane) : Prop :=
  1 ≤ p.1 ∧ p.2.1 < MachineM.Nd p.1 ∧ p.2.2 + 1 < MachineM.Nd p.1 ∧ ∃ m1 m2 : ℤ,
    ξ.1 = zeta (a1 τ) p.1 m1 p.2.1 ∧ zeta (a2 τ) p.1 m2 p.2.2 ≤ ξ.2 ∧
      ξ.2 < zeta (a2 τ) p.1 m2 (p.2.2 + 1)

/-- `ξ = ξ(i, j)` in a grid `G_d`. -/
def GPos (p : ℕ × ℕ × ℕ) (ξ : Plane) : Prop :=
  1 ≤ p.1 ∧ p.2.1 < MachineM.Nd p.1 ∧ p.2.2 < MachineM.Nd p.1 ∧
    ∃ m1 m2 : ℤ, ξ = gsite τ p.1 m1 m2 p.2.1 p.2.2

open Classical in
/-- `ℓ^E` at `ξ`: `hcolFormula` on the horizontal channels, `∘` elsewhere. -/
noncomputable def lEc (ξ : Plane) : Option (HCol U) :=
  if h : ∃ p, HSeg τ p ξ then some (hcolFormula U h.choose.1 h.choose.2.1 h.choose.2.2) else none

open Classical in
/-- `ℓ^N` at `ξ`: `vcolFormula` with `x = 0` on the vertical channels, `∘` elsewhere. -/
noncomputable def lNc (ξ : Plane) : Option (VCol U) :=
  if h : ∃ p, VSeg τ p ξ then
    some ((vcolFormula U h.choose.1 h.choose.2.1 h.choose.2.2).withX fun _ => false)
  else none

open Classical in
/-- `𝔨` at `ξ`: `cellFormula` with `x = y = 0` at the sites of the grids, `∘` elsewhere. -/
noncomputable def kF (ξ : Plane) : Option (CellRec U) :=
  if h : ∃ p, GPos τ p ξ then
    some ((cellFormula U h.choose.1 h.choose.2.1 h.choose.2.2).withXY (fun _ => false)
      fun _ => false)
  else none

open Classical in
/-- `𝔯` at `ξ` (`bg:markers`(a)). -/
noncomputable def rowMc (ξ : Plane) : Bool := decide (∃ d m, 1 ≤ d ∧ ξ.2 = rfree (a2 τ) d m)

open Classical in
/-- `𝔠` at `ξ` (`bg:markers`(a)). -/
noncomputable def colMc (ξ : Plane) : Bool := decide (∃ d m, 1 ≤ d ∧ ξ.1 = rfree (a1 τ) d m)

open Classical in
/-- The depth of a root row. -/
noncomputable def rowDepth (y : ℤ) : ℕ :=
  if h : ∃ d, ∃ m, 1 ≤ d ∧ y = rfree (a2 τ) d m then Nat.find h else 0

open Classical in
/-- The depth of a root column. -/
noncomputable def colDepth (x : ℤ) : ℕ :=
  if h : ∃ d, ∃ m, 1 ≤ d ∧ x = rfree (a1 τ) d m then Nat.find h else 0

/-- The nearest root coordinate at or below `z`: `r_d(m)` with `r_d(m) ≤ z < r_d(m + 1)`. -/
def rootBelow (a : ℕ → ℤ) (d : ℕ) (z : ℤ) : ℤ := rfree a d ((z - rfree a d 0) / 4 ^ (d + 1))

/-- `w^E` at `ξ`: on a marked row, the spin at the nearest root at or west of `ξ` (P1). -/
noncomputable def wEc (σ : Plane → Spin) (ξ : Plane) : Option Spin :=
  if rowMc τ ξ = true then some (σ (rootBelow (a1 τ) (rowDepth τ ξ.2) ξ.1, ξ.2)) else none

/-- `w^N` at `ξ`: on a marked column, the spin at the nearest root at or south of `ξ` (P2). -/
noncomputable def wNc (σ : Plane → Spin) (ξ : Plane) : Option Spin :=
  if colMc τ ξ = true then some (σ (ξ.1, rootBelow (a2 τ) (colDepth τ ξ.1) ξ.2)) else none

/-- **`prop:background`(b)**: the configuration with the background of `τ`, spins `σ`, wire
values from the spins at the roots, and all switches and free bits `0`. The fields on the west
(south) side are those on the east (north) side of the west (south) neighbour, so matching holds
by construction. -/
noncomputable def cfg (σ : Plane → Spin) (ξ : Plane) : SiteVal U where
  q := qtilingOf τ ξ
  oW := oEc τ (ξ.1 - 1, ξ.2)
  oE := oEc τ ξ
  oS := oNc τ (ξ.1, ξ.2 - 1)
  oN := oNc τ ξ
  eW := eEc τ (ξ.1 - 1, ξ.2)
  eE := eEc τ ξ
  eS := eNc τ (ξ.1, ξ.2 - 1)
  eN := eNc τ ξ
  lW := lEc U τ (ξ.1 - 1, ξ.2)
  lE := lEc U τ ξ
  lS := lNc U τ (ξ.1, ξ.2 - 1)
  lN := lNc U τ ξ
  k := kF U τ ξ
  rowM := rowMc τ ξ
  colM := colMc τ ξ
  spin := σ ξ
  wW := wEc τ σ (ξ.1 - 1, ξ.2)
  wE := wEc τ σ ξ
  wS := wNc τ σ (ξ.1, ξ.2 - 1)
  wN := wNc τ σ ξ

end Defs

/-! ## Walls, lines and carriers of the construction -/

section Typical

variable {U : Machine} {τ : ℕ → Bool × Bool} (hτ : Typical τ)
include hτ

theorem qphase_cfg : IsQTiling (qtilingOf τ) ∧ IsQPhase (qtilingOf τ) τ := qtilingOf_spec hτ.1

theorem rowW_L (z y : ℤ) : rowW τ y z = some .L ↔
    ∃ e, 1 ≤ e ∧ IsLeftEnd (a1 τ) e z ∧ InFrame (a2 τ) e y := by
  have h := walls_VW (qphase_cfg hτ).2 hτ.2.1 (z, y) .lo
  refine h.trans ⟨?_, ?_⟩
  · rintro ⟨d, hd, (⟨-, h1⟩ | ⟨h1, -⟩), hy⟩
    · exact ⟨d, hd, h1, hy⟩
    · exact absurd h1 (by decide)
  · rintro ⟨d, hd, h1, hy⟩; exact ⟨d, hd, Or.inl ⟨rfl, h1⟩, hy⟩

theorem rowW_R (z y : ℤ) : rowW τ y z = some .R ↔
    ∃ e, 1 ≤ e ∧ IsRightEnd (a1 τ) e z ∧ InFrame (a2 τ) e y := by
  have h := walls_VW (qphase_cfg hτ).2 hτ.2.1 (z, y) .hi
  refine h.trans ⟨?_, ?_⟩
  · rintro ⟨d, hd, (⟨h1, -⟩ | ⟨-, h1⟩), hy⟩
    · exact absurd h1 (by decide)
    · exact ⟨d, hd, h1, hy⟩
  · rintro ⟨d, hd, h1, hy⟩; exact ⟨d, hd, Or.inr ⟨rfl, h1⟩, hy⟩

theorem colW_B (x z : ℤ) : colW τ x z = some .B ↔
    ∃ e, 1 ≤ e ∧ IsLeftEnd (a2 τ) e z ∧ InFrame (a1 τ) e x := by
  have h := walls_HW (qphase_cfg hτ).2 hτ.2.2.1 (x, z) .lo
  refine h.trans ⟨?_, ?_⟩
  · rintro ⟨d, hd, (⟨-, h1⟩ | ⟨h1, -⟩), hy⟩
    · exact ⟨d, hd, h1, hy⟩
    · exact absurd h1 (by decide)
  · rintro ⟨d, hd, h1, hy⟩; exact ⟨d, hd, Or.inl ⟨rfl, h1⟩, hy⟩

theorem colW_T (x z : ℤ) : colW τ x z = some .T ↔
    ∃ e, 1 ≤ e ∧ IsRightEnd (a2 τ) e z ∧ InFrame (a1 τ) e x := by
  have h := walls_HW (qphase_cfg hτ).2 hτ.2.2.1 (x, z) .hi
  refine h.trans ⟨?_, ?_⟩
  · rintro ⟨d, hd, (⟨h1, -⟩ | ⟨-, h1⟩), hy⟩
    · exact absurd h1 (by decide)
    · exact ⟨d, hd, h1, hy⟩
  · rintro ⟨d, hd, h1, hy⟩; exact ⟨d, hd, Or.inr ⟨rfl, h1⟩, hy⟩

/-- The row `y` of the construction, given by its walls. -/
noncomputable def rowLine (y : ℤ) : WLine LR where
  L := .L
  R := .R
  hLR := by decide
  two := Setting.LR_two
  a := a1 τ
  b := a2 τ
  ha := frameOffsets_phase _
  hb := hτ.inFrame_row
  y := y
  W := rowW τ y
  wallL := fun z => rowW_L hτ z y
  wallR := fun z => rowW_R hτ z y

/-- The column `x` of the construction, given by its walls. -/
noncomputable def colLine (x : ℤ) : WLine BT where
  L := .B
  R := .T
  hLR := by decide
  two := Setting.BT_two
  a := a2 τ
  b := a1 τ
  ha := frameOffsets_phase _
  hb := hτ.inFrame_col
  y := x
  W := colW τ x
  wallL := fun z => colW_B hτ x z
  wallR := fun z => colW_T hτ x z

variable (σ : Plane → Spin)

/-- `prop:routing`(b) for the construction (rows). -/
theorem cfg_hcarrier (ξ : Plane) : (cfg U τ σ ξ).IsHCarrier ↔
    ∃ m, frameLo (a1 τ) (own (a2 τ) hτ.inFrame_row ξ.2) m < ξ.1 ∧
      ξ.1 < frameHi (a1 τ) (own (a2 τ) hτ.inFrame_row ξ.2) m := by
  obtain ⟨z, y⟩ := ξ
  constructor
  · rintro ⟨hW, hoW⟩
    exact ((rowLine hτ y).toLine.carrier_iff hW).1 hoW
  · rintro ⟨m, h1, h2⟩
    have hW : (rowLine hτ y).toLine.W z = none := (rowLine hτ y).toLine.interior_none h1 h2
    exact ⟨hW, ((rowLine hτ y).toLine.carrier_iff hW).2 ⟨m, h1, h2⟩⟩

/-- `prop:routing`(b) for the construction (columns). -/
theorem cfg_vcarrier (ξ : Plane) : (cfg U τ σ ξ).IsVCarrier ↔
    ∃ m, frameLo (a2 τ) (own (a1 τ) hτ.inFrame_col ξ.1) m < ξ.2 ∧
      ξ.2 < frameHi (a2 τ) (own (a1 τ) hτ.inFrame_col ξ.1) m := by
  obtain ⟨x, z⟩ := ξ
  constructor
  · rintro ⟨hW, hoS⟩
    exact ((colLine hτ x).toLine.carrier_iff hW).1 hoS
  · rintro ⟨m, h1, h2⟩
    have hW : (colLine hτ x).toLine.W z = none := (colLine hτ x).toLine.interior_none h1 h2
    exact ⟨hW, ((colLine hτ x).toLine.carrier_iff hW).2 ⟨m, h1, h2⟩⟩

/-- `prop:routing`(c) for the construction. -/
theorem cfg_active (ξ : Plane) : (cfg U τ σ ξ).IsActive ↔ actF τ ξ := by
  constructor
  · rintro ⟨hH, hV⟩
    obtain ⟨m1, h1, h1'⟩ := (cfg_hcarrier hτ σ ξ).1 hH
    obtain ⟨m2, h2, h2'⟩ := (cfg_vcarrier hτ σ ξ).1 hV
    have hle1 : own (a1 τ) hτ.inFrame_col ξ.1 ≤ own (a2 τ) hτ.inFrame_row ξ.2 :=
      own_le _ _ (own_spec (a2 τ) hτ.inFrame_row ξ.2).1 ⟨m1, h1.le, h1'.le⟩
    have hle2 : own (a2 τ) hτ.inFrame_row ξ.2 ≤ own (a1 τ) hτ.inFrame_col ξ.1 :=
      own_le _ _ (own_spec (a1 τ) hτ.inFrame_col ξ.1).1 ⟨m2, h2.le, h2'.le⟩
    have heq : own (a2 τ) hτ.inFrame_row ξ.2 = own (a1 τ) hτ.inFrame_col ξ.1 :=
      le_antisymm hle2 hle1
    rw [heq] at h1 h1'
    refine ⟨own (a1 τ) hτ.inFrame_col ξ.1, m1, m2, (own_spec (a1 τ) hτ.inFrame_col ξ.1).1,
      isFree_own (a := a1 τ) (h := hτ.inFrame_col) h1 h1', ?_⟩
    rw [← heq] at h2 h2'
    have := isFree_own (a := a2 τ) (h := hτ.inFrame_row) h2 h2'
    rwa [heq] at this
  · rintro ⟨d, m1, m2, hd, h1, h2⟩
    have e1 : own (a1 τ) hτ.inFrame_col ξ.1 = d := own_eq_of_isFree hd h1
    have e2 : own (a2 τ) hτ.inFrame_row ξ.2 = d := own_eq_of_isFree hd h2
    refine ⟨(cfg_hcarrier hτ σ ξ).2 ⟨m1, ?_, ?_⟩, (cfg_vcarrier hτ σ ξ).2 ⟨m2, ?_, ?_⟩⟩
    · rw [e2]; exact h1.1
    · rw [e2]; exact h1.2.1
    · rw [e1]; exact h2.1
    · rw [e1]; exact h2.2.1

end Typical

/-! ## Event tags and boundary flags of the construction -/

section Typical

variable {U : Machine} {τ : ℕ → Bool × Bool} (hτ : Typical τ)
include hτ

theorem rowAct (y : ℤ) : (rowLine hτ y).ActOK (fun x => actF τ (x, y)) := by
  rintro x ⟨d, m1, m2, hd, h1, h2⟩
  have e2 : own (a2 τ) hτ.inFrame_row y = d := own_eq_of_isFree hd h2
  have hlo : frameLo (a1 τ) (rowLine hτ y).toLine.d0 m1 < x := by
    show frameLo (a1 τ) (own (a2 τ) hτ.inFrame_row y) m1 < x
    rw [e2]; exact h1.1
  have hhi : x < frameHi (a1 τ) (rowLine hτ y).toLine.d0 m1 := by
    show x < frameHi (a1 τ) (own (a2 τ) hτ.inFrame_row y) m1
    rw [e2]; exact h1.2.1
  have hW := (rowLine hτ y).toLine.interior_none hlo hhi
  exact ⟨hW, ((rowLine hτ y).toLine.carrier_iff hW).2 ⟨m1, hlo, hhi⟩⟩

theorem colAct (x : ℤ) : (colLine hτ x).ActOK (fun z => actF τ (x, z)) := by
  rintro z ⟨d, m1, m2, hd, h1, h2⟩
  have e1 : own (a1 τ) hτ.inFrame_col x = d := own_eq_of_isFree hd h1
  have hlo : frameLo (a2 τ) (colLine hτ x).toLine.d0 m2 < z := by
    show frameLo (a2 τ) (own (a1 τ) hτ.inFrame_col x) m2 < z
    rw [e1]; exact h2.1
  have hhi : z < frameHi (a2 τ) (colLine hτ x).toLine.d0 m2 := by
    show z < frameHi (a2 τ) (own (a1 τ) hτ.inFrame_col x) m2
    rw [e1]; exact h2.2.1
  have hW := (colLine hτ x).toLine.interior_none hlo hhi
  exact ⟨hW, ((colLine hτ x).toLine.carrier_iff hW).2 ⟨m2, hlo, hhi⟩⟩

/-- The row `y` of the construction with its event tags. -/
noncomputable def rowEv (y : ℤ) : EvLine LR := (rowLine hτ y).toEvLine (rowAct hτ y)

/-- The column `x` of the construction with its event tags. -/
noncomputable def colEv (x : ℤ) : EvLine BT := (colLine hτ x).toEvLine (colAct hτ x)

variable (σ : Plane → Spin)

/-- `bg:grids`(c) for the construction, position-free. -/
theorem cfg_flags {d : ℕ} (hd : 1 ≤ d) {m1 m2 x y : ℤ} (h1 : IsFree (a1 τ) d m1 x)
    (h2 : IsFree (a2 τ) d m2 y) :
    (cfg U τ σ (x, y)).fW = decide (x = rfree (a1 τ) d m1) ∧
    (cfg U τ σ (x, y)).fE = decide (x = frameHi (a1 τ) d m1 - 1) ∧
    (cfg U τ σ (x, y)).fS = decide (y = rfree (a2 τ) d m2) ∧
    (cfg U τ σ (x, y)).fN = decide (y = frameHi (a2 τ) d m2 - 1) := by
  have ha1 : FrameOffsets (a1 τ) := frameOffsets_phase _
  have ha2 : FrameOffsets (a2 τ) := frameOffsets_phase _
  have hd0h : (rowEv hτ y).toLine.d0 = d := own_eq_of_isFree hd h2
  have hd0v : (colEv hτ x).toLine.d0 = d := own_eq_of_isFree hd h1
  have actH : ∀ z, IsFree (a1 τ) d m1 z → (rowEv hτ y).act z := fun z hz => ⟨d, m1, m2, hd, hz, h2⟩
  have actV : ∀ z, IsFree (a2 τ) d m2 z → (colEv hτ x).act z := fun z hz => ⟨d, m1, m2, hd, h1, hz⟩
  obtain ⟨fw1, fw2⟩ := (rowEv hτ y).first_wall (m := m1)
    (by rw [hd0h]; exact actH _ (isFree_rfree ha1 hd m1))
  obtain ⟨fe1, fe2⟩ := (rowEv hτ y).second_wall (m := m1)
    (by rw [hd0h]; exact actH _ (isFree_frameHi_sub_one ha1 hd m1))
  obtain ⟨fs1, fs2⟩ := (colEv hτ x).first_wall (m := m2)
    (by rw [hd0v]; exact actV _ (isFree_rfree ha2 hd m2))
  obtain ⟨fn1, fn2⟩ := (colEv hτ x).second_wall (m := m2)
    (by rw [hd0v]; exact actV _ (isFree_frameHi_sub_one ha2 hd m2))
  rw [hd0h] at fw1 fw2 fe1 fe2
  rw [hd0v] at fs1 fs2 fn1 fn2
  change Ev.FirstIs (eEc τ (frameLo (a1 τ) d m1, y)) .wall at fw1
  change ∀ z, frameLo (a1 τ) d m1 < z → z < frameHi (a1 τ) d m1 →
    ¬ Ev.FirstIs (eEc τ (z, y)) .wall at fw2
  change Ev.SecondIs (eEc τ (frameHi (a1 τ) d m1 - 1, y)) .wall at fe1
  change ∀ z, frameLo (a1 τ) d m1 < z → z < frameHi (a1 τ) d m1 →
    ¬ Ev.SecondIs (eEc τ (z - 1, y)) .wall at fe2
  change Ev.FirstIs (eNc τ (x, frameLo (a2 τ) d m2)) .wall at fs1
  change ∀ z, frameLo (a2 τ) d m2 < z → z < frameHi (a2 τ) d m2 →
    ¬ Ev.FirstIs (eNc τ (x, z)) .wall at fs2
  change Ev.SecondIs (eNc τ (x, frameHi (a2 τ) d m2 - 1)) .wall at fn1
  change ∀ z, frameLo (a2 τ) d m2 < z → z < frameHi (a2 τ) d m2 →
    ¬ Ev.SecondIs (eNc τ (x, z - 1)) .wall at fn2
  obtain ⟨hx1, hx2, -⟩ := h1
  obtain ⟨hy1, hy2, -⟩ := h2
  refine ⟨?_, ?_, ?_, ?_⟩
  · show SiteVal.fW (cfg U τ σ (x, y)) = _
    rw [Bool.eq_iff_iff, SiteValFlags.fW_iff, decide_eq_true_iff]
    show Ev.FirstIs (eEc τ (x - 1, y)) .wall ↔ _
    by_cases hx : x = rfree (a1 τ) d m1
    · rw [hx]; simp only [rfree, add_sub_cancel_right, iff_true]; exact fw1
    · simp only [hx, iff_false]
      exact fw2 _ (by simp only [rfree] at hx; omega) (by omega)
  · rw [Bool.eq_iff_iff, SiteValFlags.fE_iff, decide_eq_true_iff]
    show Ev.SecondIs (eEc τ (x, y)) .wall ↔ _
    by_cases hx : x = frameHi (a1 τ) d m1 - 1
    · rw [hx]; simp only [iff_true]; exact fe1
    · simp only [hx, iff_false]
      have := fe2 (x + 1) (by omega) (by omega)
      rwa [add_sub_cancel_right] at this
  · rw [Bool.eq_iff_iff, SiteValFlags.fS_iff, decide_eq_true_iff]
    show Ev.FirstIs (eNc τ (x, y - 1)) .wall ↔ _
    by_cases hy : y = rfree (a2 τ) d m2
    · rw [hy]; simp only [rfree, add_sub_cancel_right, iff_true]; exact fs1
    · simp only [hy, iff_false]
      exact fs2 _ (by simp only [rfree] at hy; omega) (by omega)
  · rw [Bool.eq_iff_iff, SiteValFlags.fN_iff, decide_eq_true_iff]
    show Ev.SecondIs (eNc τ (x, y)) .wall ↔ _
    by_cases hy : y = frameHi (a2 τ) d m2 - 1
    · rw [hy]; simp only [iff_true]; exact fn1
    · simp only [hy, iff_false]
      have := fn2 (y + 1) (by omega) (by omega)
      rwa [add_sub_cancel_right] at this

/-- `bg:grids`(c) for the construction, at logical positions. -/
theorem cfg_grids_c {d : ℕ} (hd : 1 ≤ d) (m1 m2 : ℤ) {i j : ℕ} (hi : i < MachineM.Nd d)
    (hj : j < MachineM.Nd d) :
    (cfg U τ σ (gsite τ d m1 m2 i j)).fW = decide (i = 0) ∧
    (cfg U τ σ (gsite τ d m1 m2 i j)).fE = decide (i = MachineM.Nd d - 1) ∧
    (cfg U τ σ (gsite τ d m1 m2 i j)).fS = decide (j = 0) ∧
    (cfg U τ σ (gsite τ d m1 m2 i j)).fN = decide (j = MachineM.Nd d - 1) := by
  have ha1 : FrameOffsets (a1 τ) := frameOffsets_phase _
  have ha2 : FrameOffsets (a2 τ) := frameOffsets_phase _
  have h0 : 0 < MachineM.Nd d := by have := MachineM.two_le_Nd d; omega
  obtain ⟨f1, f2, f3, f4⟩ := cfg_flags hτ σ hd (zeta_free ha1 hd m1 hi) (zeta_free ha2 hd m2 hj)
  simp only [gsite] at f1 f2 f3 f4 ⊢
  rw [f1, f2, f3, f4, ← zeta_zero ha1 hd m1, ← zeta_last ha1 hd m1, ← zeta_zero ha2 hd m2,
    ← zeta_last ha2 hd m2]
  exact ⟨decide_eq_decide.2 (zeta_inj ha1 hd m1 hi h0),
    decide_eq_decide.2 (zeta_inj ha1 hd m1 hi (by omega)),
    decide_eq_decide.2 (zeta_inj ha2 hd m2 hj h0),
    decide_eq_decide.2 (zeta_inj ha2 hd m2 hj (by omega))⟩

end Typical

/-! ## Channels and grid positions -/

/-- Free coordinates determine their depth and frame. -/
theorem free_unique {a : ℕ → ℤ} {d d' : ℕ} {m m' y : ℤ} (hd : 1 ≤ d) (hd' : 1 ≤ d')
    (h : IsFree a d m y) (h' : IsFree a d' m' y) : d = d' ∧ m = m' := by
  have e : d = d' := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact h'.2.2 d hd hlt ⟨m, h.1.le, h.2.1.le⟩
    · exact h.2.2 d' hd' hlt ⟨m', h'.1.le, h'.2.1.le⟩
  subst e
  exact ⟨rfl, frame_window_unique ⟨h.1.le, h.2.1.le⟩ ⟨h'.1.le, h'.2.1.le⟩⟩

section Positions

variable {τ : ℕ → Bool × Bool}

/-- A horizontal channel through a site of the frame `I_d(m₁)` on a free row of depth `d`. -/
theorem HSeg_inv {d d' i' j' j : ℕ} {m1 m2 x y : ℤ} (hd : 1 ≤ d) (hj : j < MachineM.Nd d)
    (hy : y = zeta (a2 τ) d m2 j) (hx : frameLo (a1 τ) d m1 ≤ x ∧ x ≤ frameHi (a1 τ) d m1)
    (h : HSeg τ (d', i', j') (x, y)) :
    d' = d ∧ j' = j ∧ i' + 1 < MachineM.Nd d ∧ zeta (a1 τ) d m1 i' ≤ x ∧
      x < zeta (a1 τ) d m1 (i' + 1) := by
  have ha1 : FrameOffsets (a1 τ) := frameOffsets_phase _
  have ha2 : FrameOffsets (a2 τ) := frameOffsets_phase _
  obtain ⟨hd', hi', hj', m1', m2', ey, ex1, ex2⟩ := h
  simp only at hd' hi' hj' ey ex1 ex2
  have fy := zeta_free ha2 hd m2 hj
  have fy' := zeta_free ha2 hd' m2' hj'
  rw [← hy] at fy
  rw [← ey] at fy'
  obtain ⟨rfl, rfl⟩ := free_unique hd' hd fy' fy
  have ej : j' = j := (zeta_inj ha2 hd' m2' hj' hj).1 (ey.symm.trans hy)
  have fi := zeta_free ha1 hd' m1' (show i' < MachineM.Nd d' by omega)
  have fi1 := zeta_free ha1 hd' m1' hi'
  have em : m1' = m1 := frame_window_unique (a := a1 τ) (z := x)
    ⟨by have := fi.1; omega, by have := fi1.2.1; omega⟩ hx
  subst em
  exact ⟨rfl, ej, hi', ex1, ex2⟩

/-- A vertical channel through a site of the frame `I_d(m₂)` on a free column of depth `d`. -/
theorem VSeg_inv {d d' i' j' i : ℕ} {m1 m2 x y : ℤ} (hd : 1 ≤ d) (hi : i < MachineM.Nd d)
    (hx : x = zeta (a1 τ) d m1 i) (hy : frameLo (a2 τ) d m2 ≤ y ∧ y ≤ frameHi (a2 τ) d m2)
    (h : VSeg τ (d', i', j') (x, y)) :
    d' = d ∧ i' = i ∧ j' + 1 < MachineM.Nd d ∧ zeta (a2 τ) d m2 j' ≤ y ∧
      y < zeta (a2 τ) d m2 (j' + 1) := by
  have ha1 : FrameOffsets (a1 τ) := frameOffsets_phase _
  have ha2 : FrameOffsets (a2 τ) := frameOffsets_phase _
  obtain ⟨hd', hi', hj', m1', m2', ex, ey1, ey2⟩ := h
  simp only at hd' hi' hj' ex ey1 ey2
  have fx := zeta_free ha1 hd m1 hi
  have fx' := zeta_free ha1 hd' m1' hi'
  rw [← hx] at fx
  rw [← ex] at fx'
  obtain ⟨rfl, rfl⟩ := free_unique hd' hd fx' fx
  have ei : i' = i := (zeta_inj ha1 hd' m1' hi' hi).1 (ex.symm.trans hx)
  have fj := zeta_free ha2 hd' m2' (show j' < MachineM.Nd d' by omega)
  have fj1 := zeta_free ha2 hd' m2' hj'
  have em : m2' = m2 := frame_window_unique (a := a2 τ) (z := y)
    ⟨by have := fj.1; omega, by have := fj1.2.1; omega⟩ hy
  subst em
  exact ⟨rfl, ei, hj', ey1, ey2⟩

theorem HSeg_unique {p p' : ℕ × ℕ × ℕ} {ξ : Plane} (h : HSeg τ p ξ) (h' : HSeg τ p' ξ) :
    p = p' := by
  have ha1 : FrameOffsets (a1 τ) := frameOffsets_phase _
  obtain ⟨d, i, j⟩ := p
  obtain ⟨d', i', j'⟩ := p'
  obtain ⟨x, y⟩ := ξ
  obtain ⟨hd, hi, hj, m1, m2, ey, ex1, ex2⟩ := h
  simp only at hd hi hj ey ex1 ex2
  have fi := zeta_free ha1 hd m1 (show i < MachineM.Nd d by omega)
  have fi1 := zeta_free ha1 hd m1 hi
  obtain ⟨rfl, rfl, hi', e1, e2⟩ := HSeg_inv (m1 := m1) hd hj ey
    ⟨by have := fi.1; omega, by have := fi1.2.1; omega⟩ h'
  have a1 : i < i' + 1 := (zeta_lt_iff ha1 hd m1 (by omega) hi').1 (by omega)
  have a2 : i' < i + 1 := (zeta_lt_iff ha1 hd m1 (by omega) hi).1 (by omega)
  have : i = i' := by omega
  subst this; rfl

theorem VSeg_unique {p p' : ℕ × ℕ × ℕ} {ξ : Plane} (h : VSeg τ p ξ) (h' : VSeg τ p' ξ) :
    p = p' := by
  have ha2 : FrameOffsets (a2 τ) := frameOffsets_phase _
  obtain ⟨d, i, j⟩ := p
  obtain ⟨d', i', j'⟩ := p'
  obtain ⟨x, y⟩ := ξ
  obtain ⟨hd, hi, hj, m1, m2, ex, ey1, ey2⟩ := h
  simp only at hd hi hj ex ey1 ey2
  have fj := zeta_free ha2 hd m2 (show j < MachineM.Nd d by omega)
  have fj1 := zeta_free ha2 hd m2 hj
  obtain ⟨rfl, rfl, hj', e1, e2⟩ := VSeg_inv (m2 := m2) hd hi ex
    ⟨by have := fj.1; omega, by have := fj1.2.1; omega⟩ h'
  have a1 : j < j' + 1 := (zeta_lt_iff ha2 hd m2 (by omega) hj').1 (by omega)
  have a2 : j' < j + 1 := (zeta_lt_iff ha2 hd m2 (by omega) hj).1 (by omega)
  have : j = j' := by omega
  subst this; rfl

theorem GPos_unique {p p' : ℕ × ℕ × ℕ} {ξ : Plane} (h : GPos τ p ξ) (h' : GPos τ p' ξ) :
    p = p' := by
  have ha1 : FrameOffsets (a1 τ) := frameOffsets_phase _
  have ha2 : FrameOffsets (a2 τ) := frameOffsets_phase _
  obtain ⟨d, i, j⟩ := p
  obtain ⟨d', i', j'⟩ := p'
  obtain ⟨hd, hi, hj, m1, m2, rfl⟩ := h
  obtain ⟨hd', hi', hj', m1', m2', e⟩ := h'
  simp only [gsite, Prod.mk.injEq] at hd hi hj hd' hi' hj' e
  obtain ⟨e1, e2⟩ := e
  have f1 := zeta_free ha1 hd m1 hi
  have f1' := zeta_free ha1 hd' m1' hi'
  have f2 := zeta_free ha2 hd m2 hj
  have f2' := zeta_free ha2 hd' m2' hj'
  rw [e1] at f1
  rw [e2] at f2
  obtain ⟨rfl, rfl⟩ := free_unique hd hd' f1 f1'
  obtain ⟨-, rfl⟩ := free_unique hd hd' f2 f2'
  have ei := (zeta_inj ha1 hd m1 hi hi').1 e1
  have ej := (zeta_inj ha2 hd m2 hj hj').1 e2
  subst ei; subst ej; rfl

variable (U : Machine)

theorem lEc_of {p : ℕ × ℕ × ℕ} {ξ : Plane} (h : HSeg τ p ξ) :
    lEc U τ ξ = some (hcolFormula U p.1 p.2.1 p.2.2) := by
  have hex : ∃ p, HSeg τ p ξ := ⟨p, h⟩
  rw [lEc, dif_pos hex, HSeg_unique hex.choose_spec h]

theorem lEc_none {ξ : Plane} (h : ¬ ∃ p, HSeg τ p ξ) : lEc U τ ξ = none := by
  rw [lEc, dif_neg h]

theorem lNc_of {p : ℕ × ℕ × ℕ} {ξ : Plane} (h : VSeg τ p ξ) :
    lNc U τ ξ = some ((vcolFormula U p.1 p.2.1 p.2.2).withX fun _ => false) := by
  have hex : ∃ p, VSeg τ p ξ := ⟨p, h⟩
  rw [lNc, dif_pos hex, VSeg_unique hex.choose_spec h]

theorem lNc_none {ξ : Plane} (h : ¬ ∃ p, VSeg τ p ξ) : lNc U τ ξ = none := by
  rw [lNc, dif_neg h]

theorem kF_of {p : ℕ × ℕ × ℕ} {ξ : Plane} (h : GPos τ p ξ) :
    kF U τ ξ = some ((cellFormula U p.1 p.2.1 p.2.2).withXY (fun _ => false) fun _ => false) := by
  have hex : ∃ p, GPos τ p ξ := ⟨p, h⟩
  rw [kF, dif_pos hex, GPos_unique hex.choose_spec h]

theorem kF_none {ξ : Plane} (h : ¬ ∃ p, GPos τ p ξ) : kF U τ ξ = none := by
  rw [kF, dif_neg h]

theorem kF_xy {ξ : Plane} {k : CellRec U} (h : kF U τ ξ = some k) :
    k.x = (fun _ => false) ∧ k.y = fun _ => false := by
  unfold kF at h
  split_ifs at h with hex
  · rw [Option.some.injEq] at h; subst h; exact ⟨rfl, rfl⟩

/-! ### The colours and records at the sites of a grid -/

variable {d : ℕ} (hd : 1 ≤ d) (m1 m2 : ℤ) {i j : ℕ} (hi : i < MachineM.Nd d)
  (hj : j < MachineM.Nd d)
include hd hi hj

theorem lE_gsite :
    lEc U τ (gsite τ d m1 m2 i j) =
      if i + 1 < MachineM.Nd d then some (hcolFormula U d i j) else none := by
  have ha1 : FrameOffsets (a1 τ) := frameOffsets_phase _
  split_ifs with h
  · exact lEc_of U (p := (d, i, j)) ⟨hd, h, hj, m1, m2, rfl, le_rfl,
      (zeta_lt_iff ha1 hd m1 hi h).2 (by omega)⟩
  · refine lEc_none U ?_
    rintro ⟨⟨d', i', j'⟩, hs⟩
    have fi := zeta_free ha1 hd m1 hi
    obtain ⟨rfl, -, hi', e1, e2⟩ := HSeg_inv hd hj rfl ⟨fi.1.le, fi.2.1.le⟩ hs
    have : i < i' + 1 := (zeta_lt_iff ha1 hd m1 hi hi').1 e2
    omega

end Positions

section Positions2

variable {τ : ℕ → Bool × Bool} (U : Machine) {d : ℕ} (hd : 1 ≤ d) (m1 m2 : ℤ) {i j : ℕ}
  (hi : i < MachineM.Nd d) (hj : j < MachineM.Nd d)
include hd hi hj

theorem lW_gsite :
    lEc U τ ((gsite τ d m1 m2 i j).1 - 1, (gsite τ d m1 m2 i j).2) =
      if i = 0 then none else some (hcolFormula U d (i - 1) j) := by
  have ha1 : FrameOffsets (a1 τ) := frameOffsets_phase _
  split_ifs with h
  · refine lEc_none U ?_
    rintro ⟨⟨d', i', j'⟩, hs⟩
    subst h
    simp only [gsite, zeta_zero ha1 hd m1] at hs
    have hlh := frameLo_lt_frameHi (a1 τ) d m1
    obtain ⟨rfl, -, hi', e1, -⟩ := HSeg_inv (m1 := m1) hd hj rfl
      ⟨by simp [rfree], by simp only [rfree]; omega⟩ hs
    have := (zeta_free (i := i') ha1 hd m1 (by omega)).1
    simp only [rfree] at e1; omega
  · have hpos : 0 < i := Nat.pos_of_ne_zero h
    have hlt := (zeta_lt_iff ha1 hd m1 (show i - 1 < MachineM.Nd d by omega) hi).2 (by omega)
    refine lEc_of U (p := (d, i - 1, j)) ⟨hd, by simp only; omega, hj, m1, m2, rfl, ?_, ?_⟩
    · simp only [gsite]; omega
    · simp only [gsite]; rw [Nat.sub_add_cancel hpos]; omega

theorem lN_gsite :
    lNc U τ (gsite τ d m1 m2 i j) =
      if j + 1 < MachineM.Nd d then some ((vcolFormula U d i j).withX fun _ => false)
      else none := by
  have ha2 : FrameOffsets (a2 τ) := frameOffsets_phase _
  split_ifs with h
  · exact lNc_of U (p := (d, i, j)) ⟨hd, hi, h, m1, m2, rfl, le_rfl,
      (zeta_lt_iff ha2 hd m2 hj h).2 (by omega)⟩
  · refine lNc_none U ?_
    rintro ⟨⟨d', i', j'⟩, hs⟩
    have fj := zeta_free ha2 hd m2 hj
    obtain ⟨rfl, -, hj', e1, e2⟩ := VSeg_inv hd hi rfl ⟨fj.1.le, fj.2.1.le⟩ hs
    have : j < j' + 1 := (zeta_lt_iff ha2 hd m2 hj hj').1 e2
    omega

theorem lS_gsite :
    lNc U τ ((gsite τ d m1 m2 i j).1, (gsite τ d m1 m2 i j).2 - 1) =
      if j = 0 then none else some ((vcolFormula U d i (j - 1)).withX fun _ => false) := by
  have ha2 : FrameOffsets (a2 τ) := frameOffsets_phase _
  split_ifs with h
  · refine lNc_none U ?_
    rintro ⟨⟨d', i', j'⟩, hs⟩
    subst h
    simp only [gsite, zeta_zero ha2 hd m2] at hs
    have hlh := frameLo_lt_frameHi (a2 τ) d m2
    obtain ⟨rfl, -, hj', e1, -⟩ := VSeg_inv (m2 := m2) hd hi rfl
      ⟨by simp [rfree], by simp only [rfree]; omega⟩ hs
    have := (zeta_free (i := j') ha2 hd m2 (by omega)).1
    simp only [rfree] at e1; omega
  · have hpos : 0 < j := Nat.pos_of_ne_zero h
    have hlt := (zeta_lt_iff ha2 hd m2 (show j - 1 < MachineM.Nd d by omega) hj).2 (by omega)
    refine lNc_of U (p := (d, i, j - 1)) ⟨hd, hi, by simp only; omega, m1, m2, rfl, ?_, ?_⟩
    · simp only [gsite]; omega
    · simp only [gsite]; rw [Nat.sub_add_cancel hpos]; omega

theorem k_gsite :
    kF U τ (gsite τ d m1 m2 i j) =
      some ((cellFormula U d i j).withXY (fun _ => false) fun _ => false) :=
  kF_of U (p := (d, i, j)) ⟨hd, hi, hj, m1, m2, rfl⟩

end Positions2

theorem onColour_some {α : Type} {v : α} {P : α → Prop} (h : P v) : OnColour (some v) P :=
  fun c hc => by rw [Option.some.injEq] at hc; subst hc; exact h

theorem onColour_none {α : Type} {P : α → Prop} : OnColour (none : Option α) P :=
  fun c hc => by cases hc

theorem runAt_zero {U : Machine} {d j : ℕ} (hj : j < MachineM.Nd d) :
    runAt U d 0 j = initM U (decide (j = d + 2)) (decide (j = 0)) := by
  rw [runAt_eq hj]; rfl

theorem runAt_succ {U : Machine} {d i j : ℕ} (hj : j < MachineM.Nd d) :
    runAt U d (i + 1) j = fM U (if j = 0 then none else some (runAt U d i (j - 1))) (runAt U d i j)
      (if j + 1 < MachineM.Nd d then some (runAt U d i (j + 1)) else none) := by
  rw [runAt_eq hj, MachineM.runM, Function.iterate_succ_apply', ← MachineM.runM]
  simp only [MachineM.nextRow]
  congr 1
  · rcases j with _ | j
    · simp
    · simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.zero_lt_succ, ↓reduceDIte,
        Nat.add_sub_cancel]
      rw [runAt_eq (by omega)]
  · rw [runAt_eq hj]
  · by_cases h : j + 1 < MachineM.Nd d
    · rw [dif_pos h, if_pos h, runAt_eq h]
    · rw [dif_neg h, if_neg h]

/-! ### The rules (C0)–(C9) at the sites of a grid -/

section Rules

variable {U : Machine} {τ : ℕ → Bool × Bool} (hτ : Typical τ) (σ : Plane → Spin) {d : ℕ}
  (hd : 1 ≤ d) (m1 m2 : ℤ) {i j : ℕ} (hi : i < MachineM.Nd d) (hj : j < MachineM.Nd d)
include hτ hd hi hj

/-- At `ξ(i, j)` the record is `cellFormula` with `x = y = 0`, and (C0)–(C9) hold. -/
theorem cfg_rules :
    (cfg U τ σ (gsite τ d m1 m2 i j)).C0 ∧
    (cfg U τ σ (gsite τ d m1 m2 i j)).C1 ((cellFormula U d i j).withXY (fun _ => false) fun _ => false) ∧
    (cfg U τ σ (gsite τ d m1 m2 i j)).C2 ((cellFormula U d i j).withXY (fun _ => false) fun _ => false) ∧
    (cfg U τ σ (gsite τ d m1 m2 i j)).C3 ((cellFormula U d i j).withXY (fun _ => false) fun _ => false) ∧
    (cfg U τ σ (gsite τ d m1 m2 i j)).C4 ((cellFormula U d i j).withXY (fun _ => false) fun _ => false) ∧
    (cfg U τ σ (gsite τ d m1 m2 i j)).C5 ((cellFormula U d i j).withXY (fun _ => false) fun _ => false) ∧
    (cfg U τ σ (gsite τ d m1 m2 i j)).C6 ((cellFormula U d i j).withXY (fun _ => false) fun _ => false) ∧
    (cfg U τ σ (gsite τ d m1 m2 i j)).C7 ((cellFormula U d i j).withXY (fun _ => false) fun _ => false) ∧
    (cfg U τ σ (gsite τ d m1 m2 i j)).C8 ((cellFormula U d i j).withXY (fun _ => false) fun _ => false) ∧
    (cfg U τ σ (gsite τ d m1 m2 i j)).C9 ((cellFormula U d i j).withXY (fun _ => false) fun _ => false) := by
  obtain ⟨fW, fE, fS, fN⟩ := cfg_grids_c (U := U) hτ σ hd m1 m2 hi hj
  have hlW : (cfg U τ σ (gsite τ d m1 m2 i j)).lW =
      if i = 0 then none else some (hcolFormula U d (i - 1) j) := lW_gsite U hd m1 m2 hi hj
  have hlE : (cfg U τ σ (gsite τ d m1 m2 i j)).lE =
      if i + 1 < MachineM.Nd d then some (hcolFormula U d i j) else none := lE_gsite U hd m1 m2 hi hj
  have hlS : (cfg U τ σ (gsite τ d m1 m2 i j)).lS =
      if j = 0 then none else some ((vcolFormula U d i (j - 1)).withX fun _ => false) :=
    lS_gsite U hd m1 m2 hi hj
  have hlN : (cfg U τ σ (gsite τ d m1 m2 i j)).lN =
      if j + 1 < MachineM.Nd d then some ((vcolFormula U d i j).withX fun _ => false) else none :=
    lN_gsite U hd m1 m2 hi hj
  set s := cfg U τ σ (gsite τ d m1 m2 i j) with hs_def
  set k := (cellFormula U d i j).withXY (fun _ => false) fun _ => false with hk_def
  have hN := MachineM.two_le_Nd d
  -- the record's fields
  have kctIn : k.ctIn = if i = 0 then false else Nat.testBit (i - 1) j := rfl
  have kct : k.ct = Nat.testBit i j := rfl
  have kcy : k.cy = if i = 0 then false else carry (i - 1) 0 1 j := rfl
  have kay : k.ay = if i = MachineM.Nd d - 1 then carry (MachineM.Nd d - 1) 3 0 j else false := rfl
  have ksm : k.sm = if i = MachineM.Nd d - 1 then decide (j = d + 2) else false := rfl
  have khot : k.hot = decide (j = d + 2) := rfl
  have krdy : k.rdy = decide (MachineM.ready U d) := rfl
  have krc : k.rc = ⟨min j 80, by omega⟩ := rfl
  have ktS : k.tS = if j = 0 then none else some (runAt U d i (j - 1)) := rfl
  have ktN : k.tN = if j + 1 < MachineM.Nd d then some (runAt U d i (j + 1)) else none := rfl
  have ktC : k.tC = runAt U d i j := rfl
  refine ⟨?c0, ?c1, ?c2, ?c3, ?c4, ?c5, ?c6, ?c7, ?c8, ?c9⟩
  case c0 =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hlW, fW]; by_cases h : i = 0 <;> simp [h]
    · rw [hlE, fE]; by_cases h : i + 1 < MachineM.Nd d
      · simp [h]; omega
      · simp [h]; omega
    · rw [hlS, fS]; by_cases h : j = 0 <;> simp [h]
    · rw [hlN, fN]; by_cases h : j + 1 < MachineM.Nd d
      · simp [h]; omega
      · simp [h]; omega
  case c1 =>
    refine ⟨fun h => ?_, fun h => ?_, ?_, ?_⟩
    · rw [fW, decide_eq_true_iff] at h
      subst h
      exact ⟨rfl, by rw [kct, Nat.zero_testBit], rfl⟩
    · rw [fW, decide_eq_false_iff_not] at h
      refine ⟨?_, fun hs => ?_, fun hs => ?_, ?_⟩
      · rw [hlW, if_neg h]
        exact onColour_some (by rw [kctIn, if_neg h]; rfl)
      · rw [fS, decide_eq_true_iff] at hs
        subst hs
        rw [kcy, if_neg h, carry_zero]; rfl
      · rw [fS, decide_eq_false_iff_not] at hs
        rw [hlS, if_neg hs]
        refine onColour_some ?_
        show k.cy = ((if i = 0 then false else Nat.testBit (i - 1) (j - 1)) &&
          (if i = 0 then false else carry (i - 1) 0 1 (j - 1)))
        rw [kcy, if_neg h, if_neg h, if_neg h]
        obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        rw [carry_succ _ _ _ _ (by norm_num), Nat.zero_testBit, Nat.add_sub_cancel]
        simp [SiteVal.maj]
      · rw [kct, kctIn, kcy, if_neg h, if_neg h]
        have := testBit_add (i - 1) 0 1 j (by norm_num)
        rw [show i - 1 + 0 + 1 = i by omega, Nat.zero_testBit, Bool.xor_false] at this
        exact this
    · rw [hlE]; split_ifs
      · exact onColour_some rfl
      · exact onColour_none
    · rw [hlN]; split_ifs
      · exact onColour_some rfl
      · exact onColour_none
  case c2 =>
    refine ⟨fun h => ?_, fun h => ?_, ?_⟩
    · rw [fS, decide_eq_true_iff] at h; subst h; rw [krc]; rfl
    · rw [fS, decide_eq_false_iff_not] at h
      rw [hlS, if_neg h]
      refine onColour_some ?_
      show (min j 80) = min (min (j - 1) 80 + 1) 80
      omega
    · rw [hlN]; split_ifs
      · exact onColour_some rfl
      · exact onColour_none
  case c3 =>
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [fE, decide_eq_false_iff_not] at h
      refine ⟨by rw [kay, if_neg h], by rw [ksm, if_neg h], ?_⟩
      rw [hlN]; split_ifs
      · exact onColour_some (by show (if i = MachineM.Nd d - 1 then _ else false) = false; rw [if_neg h])
      · exact onColour_none
    · rw [fE, decide_eq_true_iff] at h
      subst h
      refine ⟨fun hs => ?_, fun hs => ?_, ?_, ?_⟩
      · rw [fS, decide_eq_true_iff] at hs; subst hs
        rw [kay, if_pos rfl, carry_zero]; rfl
      · rw [fS, decide_eq_false_iff_not] at hs
        rw [hlS, if_neg hs]
        refine onColour_some ?_
        show k.ay = (if MachineM.Nd d - 1 = MachineM.Nd d - 1 then SiteVal.maj
          (Nat.testBit (MachineM.Nd d - 1) (j - 1)) (decide (min (j - 1) 80 ≤ 1))
          (if MachineM.Nd d - 1 = MachineM.Nd d - 1 then carry (MachineM.Nd d - 1) 3 0 (j - 1)
            else false) else false)
        rw [kay, if_pos rfl, if_pos rfl, if_pos rfl]
        obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        rw [carry_succ _ _ _ _ (by norm_num), testBit_three, Nat.add_sub_cancel]
        rw [show decide (min j' 80 ≤ 1) = decide (j' ≤ 1) from decide_eq_decide.2 (by omega)]
      · rw [ksm, kct, kay, krc, if_pos rfl, if_pos rfl]
        show decide (j = d + 2) = xor (xor _ (decide (min j 80 ≤ 1))) _
        have e : decide (min j 80 ≤ 1) = Nat.testBit 3 j := by
          rw [testBit_three]; exact decide_eq_decide.2 (by omega)
        rw [e, ← testBit_add _ _ _ _ (by norm_num)]
        have h2 : MachineM.Nd d - 1 + 3 + 0 = 2 ^ (d + 2) := by
          unfold MachineM.Nd at *; omega
        rw [h2, Nat.testBit_two_pow]
        exact decide_eq_decide.2 eq_comm
      · rw [hlN]; split_ifs
        · exact onColour_some (by
            show (if MachineM.Nd d - 1 = MachineM.Nd d - 1 then _ else false) = _
            rw [if_pos rfl]; rfl)
        · exact onColour_none
  case c4 =>
    refine ⟨fun h => ?_, fun h => ?_, ?_⟩
    · rw [fE, decide_eq_true_iff] at h
      rw [khot, ksm, if_pos h]
    · rw [fE, decide_eq_false_iff_not] at h
      rw [hlE, if_pos (by omega)]
      exact onColour_some rfl
    · rw [hlW]; split_ifs
      · exact onColour_none
      · exact onColour_some rfl
  case c5 =>
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, ?_⟩
    · rw [fS, decide_eq_true_iff] at h; rw [ktS, if_pos h]
    · rw [fS, decide_eq_false_iff_not] at h
      rw [hlS, if_neg h]
      refine onColour_some ⟨by rw [ktS, if_neg h]; rfl, ?_⟩
      show k.tC = runAt U d i (j - 1 + 1)
      rw [ktC, Nat.sub_add_cancel (Nat.pos_of_ne_zero h)]
    · rw [fN, decide_eq_true_iff] at h; rw [ktN, if_neg (by omega)]
    · rw [fN, decide_eq_false_iff_not] at h
      rw [hlN, if_pos (by omega)]
      exact onColour_some ⟨rfl, by rw [ktN, if_pos (by omega)]; rfl⟩
    · rw [fW, decide_eq_true_iff] at h; subst h
      rw [ktC, runAt_zero hj, khot, fS]
    · rw [fW, decide_eq_false_iff_not] at h
      rw [hlW, if_neg h]
      refine onColour_some ?_
      show k.tC = fM U (if j = 0 then none else some (runAt U d (i - 1) (j - 1)))
        (runAt U d (i - 1) j)
        (if j + 1 < MachineM.Nd d then some (runAt U d (i - 1) (j + 1)) else none)
      obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      rw [ktC, runAt_succ hj, Nat.add_sub_cancel]
    · rw [hlE]; split_ifs
      · exact onColour_some rfl
      · exact onColour_none
  case c6 =>
    refine ⟨fun h => ⟨fun hs => ?_, fun hs => ?_, ?_⟩, fun h => ⟨?_, ?_⟩, ?_⟩
    · rw [fE, decide_eq_true_iff] at h
      rw [fS, decide_eq_true_iff] at hs
      subst h hs
      rw [krdy, ktC, runAt_eq hj]; rfl
    · rw [fE, decide_eq_true_iff] at h
      rw [fS, decide_eq_false_iff_not] at hs
      rw [hlS, if_neg hs]
      exact onColour_some (by show _ = (if i = MachineM.Nd d - 1 then _ else false); rw [if_pos h]; rfl)
    · rw [fE, decide_eq_true_iff] at h
      rw [hlN]; split_ifs
      · exact onColour_some (by show (if i = MachineM.Nd d - 1 then _ else false) = _; rw [if_pos h]; rfl)
      · exact onColour_none
    · rw [fE, decide_eq_false_iff_not] at h
      rw [hlE, if_pos (by omega)]
      exact onColour_some rfl
    · rw [fE, decide_eq_false_iff_not] at h
      rw [hlN]; split_ifs
      · exact onColour_some (by show (if i = MachineM.Nd d - 1 then _ else false) = _; rw [if_neg h])
      · exact onColour_none
    · rw [hlW]; split_ifs
      · exact onColour_none
      · exact onColour_some rfl
  case c7 =>
    refine ⟨fun h => ?_, fun h => ?_, ?_⟩
    · rw [fE, decide_eq_true_iff] at h
      subst h
      exact ⟨rfl, rfl⟩
    · rw [fE, decide_eq_false_iff_not] at h
      rw [hlE, if_pos (by omega)]
      exact onColour_some ⟨rfl, rfl⟩
    · rw [hlW]; split_ifs
      · exact onColour_none
      · exact onColour_some ⟨rfl, rfl⟩
  case c8 =>
    intro ι
    refine ⟨fun _ => ⟨rfl, ?_⟩, fun _ _ => rfl, fun _ => ?_, fun _ => ?_⟩
    · rw [hlN]; split_ifs
      · exact onColour_some rfl
      · exact onColour_none
    · rw [hlS]; split_ifs
      · exact onColour_none
      · exact onColour_some rfl
    · rw [hlN]; split_ifs
      · exact onColour_some rfl
      · exact onColour_none
  case c9 =>
    exact ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩

end Rules

/-! ## Roots along a marked line -/

theorem rfree_eq_add (a : ℕ → ℤ) (d : ℕ) (m : ℤ) :
    rfree a d m = rfree a d 0 + m * 4 ^ (d + 1) := by
  simp only [rfree, frameLo, pow_succ]; ring

theorem rootBelow_self {a : ℕ → ℤ} {d : ℕ} {m : ℤ} : rootBelow a d (rfree a d m) = rfree a d m := by
  unfold rootBelow
  congr 1
  rw [rfree_eq_add a d m, add_sub_cancel_left, Int.mul_ediv_cancel _ (by positivity)]

theorem rootBelow_pred {a : ℕ → ℤ} {d : ℕ} {z : ℤ} (h : ∀ m, z ≠ rfree a d m) :
    rootBelow a d z = rootBelow a d (z - 1) := by
  unfold rootBelow
  congr 1
  have hP0 : (0 : ℤ) < 4 ^ (d + 1) := by positivity
  have h1 := Int.emod_add_mul_ediv (z - 1 - rfree a d 0) (4 ^ (d + 1))
  have h2 := Int.emod_nonneg (z - 1 - rfree a d 0) hP0.ne'
  have h3 := Int.emod_lt_of_pos (z - 1 - rfree a d 0) hP0
  generalize (z - 1 - rfree a d 0) % 4 ^ (d + 1) = r at h1 h2 h3
  generalize (z - 1 - rfree a d 0) / 4 ^ (d + 1) = q at h1 ⊢
  have hr : r + 1 < 4 ^ (d + 1) := by
    by_contra hc
    have hrP : r + 1 = 4 ^ (d + 1) := by omega
    exact h (q + 1) (by rw [rfree_eq_add]; linear_combination -h1 + hrP)
  rw [show z - rfree a d 0 = (r + 1) + 4 ^ (d + 1) * q by linear_combination -h1,
    Int.add_mul_ediv_left _ _ hP0.ne', Int.ediv_eq_zero_of_lt (by omega) hr, zero_add]

/-- A configuration whose site values are allowed and whose neighbouring colours match is legal. -/
theorem legal_of {U : Machine} {ω : Config (SiteVal U)} (ha : ∀ ξ, (ω ξ).Allowed)
    (hH : ∀ ξ, (ω ξ).cE = (ω (ξ + e1)).cW) (hV : ∀ ξ, (ω ξ).cN = (ω (ξ + e2)).cS) :
    IsLegal (Phi U) ω := by
  intro A
  by_cases h0 : ∃ ξ, A = {ξ}
  · obtain ⟨ξ, rfl⟩ := h0
    rw [Phi_singleton]; unfold siteEnergy; rw [if_pos (ha ξ)]; simp
  by_cases h1 : ∃ ξ, A = {ξ, ξ + e1}
  · obtain ⟨ξ, rfl⟩ := h1
    rw [Phi_pairH]; unfold edgeEnergyH; rw [if_pos (hH ξ)]; simp
  by_cases h2 : ∃ ξ, A = {ξ, ξ + e2}
  · obtain ⟨ξ, rfl⟩ := h2
    rw [Phi_pairV]; unfold edgeEnergyV; rw [if_pos (hV ξ)]; simp
  rw [Phi_other h0 h1 h2]; simp

theorem evTag_none_iff {S : Type} (W : ℤ → Option S) (L R : S) (act : ℤ → Prop) (z : ℤ) :
    evTag W L R act z = none ↔ wtag W L z ≠ (L, R) := by
  unfold evTag; split_ifs with h <;> simp [h]

/-! ## The rules at every site, and legality -/

section Legal

variable {U : Machine} {τ : ℕ → Bool × Bool} (hτ : Typical τ) (σ : Plane → Spin)
include hτ

omit hτ in
theorem rowDepth_eq {y : ℤ} {d : ℕ} {m : ℤ} (hd : 1 ≤ d) (hy : y = rfree (a2 τ) d m) :
    rowDepth τ y = d := by
  classical
  have hex : ∃ d, ∃ m, 1 ≤ d ∧ y = rfree (a2 τ) d m := ⟨d, m, hd, hy⟩
  rw [rowDepth, dif_pos hex]
  obtain ⟨m', -, hm'⟩ := Nat.find_spec hex
  exact rfree_depth_unique (frameOffsets_phase _) (hm'.symm.trans hy)

omit hτ in
theorem colDepth_eq {x : ℤ} {d : ℕ} {m : ℤ} (hd : 1 ≤ d) (hx : x = rfree (a1 τ) d m) :
    colDepth τ x = d := by
  classical
  have hex : ∃ d, ∃ m, 1 ≤ d ∧ x = rfree (a1 τ) d m := ⟨d, m, hd, hx⟩
  rw [colDepth, dif_pos hex]
  obtain ⟨m', -, hm'⟩ := Nat.find_spec hex
  exact rfree_depth_unique (frameOffsets_phase _) (hm'.symm.trans hx)

/-- `bg:grids`(d) for the construction: the roots are the roots of the grids. -/
theorem cfg_isRoot (ξ : Plane) :
    (cfg U τ σ ξ).IsRoot ↔ ∃ d m1 m2, 1 ≤ d ∧ ξ = root τ d m1 m2 := by
  have ha1 : FrameOffsets (a1 τ) := frameOffsets_phase _
  have ha2 : FrameOffsets (a2 τ) := frameOffsets_phase _
  obtain ⟨x, y⟩ := ξ
  constructor
  · rintro ⟨hact, hW, hS⟩
    obtain ⟨d, m1, m2, hd, h1, h2⟩ := (cfg_active hτ σ _).1 hact
    obtain ⟨f1, -, f3, -⟩ := cfg_flags (U := U) hτ σ hd h1 h2
    rw [hW, eq_comm, decide_eq_true_iff] at f1
    rw [hS, eq_comm, decide_eq_true_iff] at f3
    exact ⟨d, m1, m2, hd, Prod.ext f1 f3⟩
  · rintro ⟨d, m1, m2, hd, he⟩
    simp only [root, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    have h1 := isFree_rfree ha1 hd m1
    have h2 := isFree_rfree ha2 hd m2
    obtain ⟨f1, -, f3, -⟩ := cfg_flags (U := U) hτ σ hd h1 h2
    exact ⟨(cfg_active hτ σ _).2 ⟨d, m1, m2, hd, h1, h2⟩, by rw [f1]; simp, by rw [f3]; simp⟩

theorem cfg_O1 (ξ : Plane) : (cfg U τ σ ξ).O1 := by
  obtain ⟨z, y⟩ := ξ
  have l := (rowLine hτ y).toLine
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have := (rowLine hτ y).toLine.copy (z - 1) (by rw [sub_add_cancel]; exact h)
    rw [sub_add_cancel] at this
    exact this.symm
  · exact ⟨(rowLine hτ y).toLine.right (z - 1) .L (by rw [sub_add_cancel]; exact h),
      (rowLine hτ y).toLine.left z .L h⟩
  · exact ⟨(rowLine hτ y).toLine.right (z - 1) .R (by rw [sub_add_cancel]; exact h),
      (rowLine hτ y).toLine.left z .R h⟩

theorem cfg_O2 (ξ : Plane) : (cfg U τ σ ξ).O2 := by
  obtain ⟨x, z⟩ := ξ
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have := (colLine hτ x).toLine.copy (z - 1) (by rw [sub_add_cancel]; exact h)
    rw [sub_add_cancel] at this
    exact this.symm
  · exact ⟨(colLine hτ x).toLine.right (z - 1) .B (by rw [sub_add_cancel]; exact h),
      (colLine hτ x).toLine.left z .B h⟩
  · exact ⟨(colLine hτ x).toLine.right (z - 1) .T (by rw [sub_add_cancel]; exact h),
      (colLine hτ x).toLine.left z .T h⟩

omit hτ in
theorem cfg_E1 (ξ : Plane) : (cfg U τ σ ξ).E1 :=
  ⟨evTag_none_iff _ _ _ _ _, evTag_none_iff _ _ _ _ _, evTag_none_iff _ _ _ _ _,
    evTag_none_iff _ _ _ _ _⟩

theorem cfg_E2 (ξ : Plane) : (cfg U τ σ ξ).E2 := by
  obtain ⟨z, y⟩ := ξ
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · obtain ⟨⟨hW, ho⟩, hnV⟩ := h
    have hna : ¬ actF τ (z, y) := fun ha => hnV ((cfg_active hτ σ _).2 ha).2
    exact (rowEv hτ y).ev_copy z hW ho hna
  · have ha := (cfg_active hτ σ _).1 h
    exact ⟨(rowEv hτ y).ev_actL z ha, (rowEv hτ y).ev_actR z ha⟩
  · exact (rowEv hτ y).ev_wallL z h.1 h.2
  · exact (rowEv hτ y).ev_wallR z h.1 h.2

theorem cfg_E3 (ξ : Plane) : (cfg U τ σ ξ).E3 := by
  obtain ⟨x, z⟩ := ξ
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · obtain ⟨⟨hW, ho⟩, hnH⟩ := h
    have hna : ¬ actF τ (x, z) := fun ha => hnH ((cfg_active hτ σ _).2 ha).1
    exact (colEv hτ x).ev_copy z hW ho hna
  · have ha := (cfg_active hτ σ _).1 h
    exact ⟨(colEv hτ x).ev_actL z ha, (colEv hτ x).ev_actR z ha⟩
  · exact (colEv hτ x).ev_wallL z h.1 h.2
  · exact (colEv hτ x).ev_wallR z h.1 h.2

theorem hseg_carrier {p : ℕ × ℕ × ℕ} {z y : ℤ} (h : HSeg τ p (z, y)) :
    (cfg U τ σ (z, y)).IsHCarrier ∧ (cfg U τ σ (z + 1, y)).IsHCarrier := by
  have ha1 : FrameOffsets (a1 τ) := frameOffsets_phase _
  have ha2 : FrameOffsets (a2 τ) := frameOffsets_phase _
  obtain ⟨d, i, j⟩ := p
  obtain ⟨hd, hi, hj, m1, m2, ey, ex1, ex2⟩ := h
  simp only at hd hi hj ey ex1 ex2
  have fy := zeta_free ha2 hd m2 hj
  rw [← ey] at fy
  have e2 : own (a2 τ) hτ.inFrame_row y = d := own_eq_of_isFree hd fy
  have fi := zeta_free ha1 hd m1 (show i < MachineM.Nd d by omega)
  have fi1 := zeta_free ha1 hd m1 hi
  refine ⟨(cfg_hcarrier hτ σ (z, y)).2 ⟨m1, ?_, ?_⟩, (cfg_hcarrier hτ σ (z + 1, y)).2 ⟨m1, ?_, ?_⟩⟩ <;>
    dsimp only <;> rw [e2]
  · have := fi.1; omega
  · have := fi1.2.1; omega
  · have := fi.1; omega
  · have := fi1.2.1; omega

theorem vseg_carrier {p : ℕ × ℕ × ℕ} {x z : ℤ} (h : VSeg τ p (x, z)) :
    (cfg U τ σ (x, z)).IsVCarrier ∧ (cfg U τ σ (x, z + 1)).IsVCarrier := by
  have ha1 : FrameOffsets (a1 τ) := frameOffsets_phase _
  have ha2 : FrameOffsets (a2 τ) := frameOffsets_phase _
  obtain ⟨d, i, j⟩ := p
  obtain ⟨hd, hi, hj, m1, m2, ex, ey1, ey2⟩ := h
  simp only at hd hi hj ex ey1 ey2
  have fx := zeta_free ha1 hd m1 hi
  rw [← ex] at fx
  have e1 : own (a1 τ) hτ.inFrame_col x = d := own_eq_of_isFree hd fx
  have fj := zeta_free ha2 hd m2 (show j < MachineM.Nd d by omega)
  have fj1 := zeta_free ha2 hd m2 hj
  refine ⟨(cfg_vcarrier hτ σ (x, z)).2 ⟨m2, ?_, ?_⟩, (cfg_vcarrier hτ σ (x, z + 1)).2 ⟨m2, ?_, ?_⟩⟩ <;>
    dsimp only <;> rw [e1]
  · have := fj.1; omega
  · have := fj1.2.1; omega
  · have := fj.1; omega
  · have := fj1.2.1; omega

theorem cfg_K1 (ξ : Plane) : (cfg U τ σ ξ).K1 := by
  have ha1 : FrameOffsets (a1 τ) := frameOffsets_phase _
  have ha2 : FrameOffsets (a2 τ) := frameOffsets_phase _
  obtain ⟨z, y⟩ := ξ
  refine ⟨fun h => ⟨?_, ?_⟩, fun h => ?_⟩
  · refine lEc_none U ?_
    rintro ⟨p, hs⟩
    have := (hseg_carrier (U := U) hτ σ hs).2
    rw [sub_add_cancel] at this
    exact h this
  · exact lEc_none U fun ⟨p, hs⟩ => h (hseg_carrier (U := U) hτ σ hs).1
  · obtain ⟨-, hnV⟩ := h
    have hna : ¬ actF τ (z, y) := fun ha => hnV ((cfg_active hτ σ _).2 ha).2
    show lEc U τ (z - 1, y) = lEc U τ (z, y)
    by_cases h1 : ∃ p, HSeg τ p (z - 1, y)
    · obtain ⟨⟨d, i, j⟩, hs⟩ := h1
      rw [lEc_of U hs]
      obtain ⟨hd, hi, hj, m1, m2, ey, ex1, ex2⟩ := hs
      simp only at hd hi hj ey ex1 ex2
      by_cases hz : z < zeta (a1 τ) d m1 (i + 1)
      · rw [lEc_of U (p := (d, i, j)) ⟨hd, hi, hj, m1, m2, ey, by dsimp only; omega, hz⟩]
      · exfalso
        have hz' : z = zeta (a1 τ) d m1 (i + 1) := by omega
        exact hna ⟨d, m1, m2, hd, by rw [hz']; exact zeta_free ha1 hd m1 hi,
          by dsimp only; rw [ey]; exact zeta_free ha2 hd m2 hj⟩
    · rw [lEc_none U h1]
      symm
      refine lEc_none U ?_
      rintro ⟨⟨d, i, j⟩, hs⟩
      obtain ⟨hd, hi, hj, m1, m2, ey, ex1, ex2⟩ := hs
      simp only at hd hi hj ey ex1 ex2
      by_cases hz : zeta (a1 τ) d m1 i < z
      · exact h1 ⟨(d, i, j), hd, hi, hj, m1, m2, ey, by dsimp only; omega, by dsimp only; omega⟩
      · have hz' : z = zeta (a1 τ) d m1 i := by omega
        exact hna ⟨d, m1, m2, hd, by rw [hz']; exact zeta_free ha1 hd m1 (by omega),
          by dsimp only; rw [ey]; exact zeta_free ha2 hd m2 hj⟩

theorem cfg_K2 (ξ : Plane) : (cfg U τ σ ξ).K2 := by
  have ha1 : FrameOffsets (a1 τ) := frameOffsets_phase _
  have ha2 : FrameOffsets (a2 τ) := frameOffsets_phase _
  obtain ⟨x, z⟩ := ξ
  refine ⟨fun h => ⟨?_, ?_⟩, fun h => ?_⟩
  · refine lNc_none U ?_
    rintro ⟨p, hs⟩
    have := (vseg_carrier (U := U) hτ σ hs).2
    rw [sub_add_cancel] at this
    exact h this
  · exact lNc_none U fun ⟨p, hs⟩ => h (vseg_carrier (U := U) hτ σ hs).1
  · obtain ⟨-, hnH⟩ := h
    have hna : ¬ actF τ (x, z) := fun ha => hnH ((cfg_active hτ σ _).2 ha).1
    show lNc U τ (x, z - 1) = lNc U τ (x, z)
    by_cases h1 : ∃ p, VSeg τ p (x, z - 1)
    · obtain ⟨⟨d, i, j⟩, hs⟩ := h1
      rw [lNc_of U hs]
      obtain ⟨hd, hi, hj, m1, m2, ex, ey1, ey2⟩ := hs
      simp only at hd hi hj ex ey1 ey2
      by_cases hz : z < zeta (a2 τ) d m2 (j + 1)
      · rw [lNc_of U (p := (d, i, j)) ⟨hd, hi, hj, m1, m2, ex, by dsimp only; omega, hz⟩]
      · exfalso
        have hz' : z = zeta (a2 τ) d m2 (j + 1) := by omega
        exact hna ⟨d, m1, m2, hd, by dsimp only; rw [ex]; exact zeta_free ha1 hd m1 hi,
          by rw [hz']; exact zeta_free ha2 hd m2 hj⟩
    · rw [lNc_none U h1]
      symm
      refine lNc_none U ?_
      rintro ⟨⟨d, i, j⟩, hs⟩
      obtain ⟨hd, hi, hj, m1, m2, ex, ey1, ey2⟩ := hs
      simp only at hd hi hj ex ey1 ey2
      by_cases hz : zeta (a2 τ) d m2 j < z
      · exact h1 ⟨(d, i, j), hd, hi, hj, m1, m2, ex, by dsimp only; omega, by dsimp only; omega⟩
      · have hz' : z = zeta (a2 τ) d m2 j := by omega
        exact hna ⟨d, m1, m2, hd, by dsimp only; rw [ex]; exact zeta_free ha1 hd m1 hi,
          by rw [hz']; exact zeta_free ha2 hd m2 (by omega)⟩

theorem cfg_K3 (ξ : Plane) : (cfg U τ σ ξ).K3 := by
  have ha1 : FrameOffsets (a1 τ) := frameOffsets_phase _
  have ha2 : FrameOffsets (a2 τ) := frameOffsets_phase _
  refine ⟨fun h => ?_, fun h => ?_⟩
  · refine kF_none U ?_
    rintro ⟨⟨d, i, j⟩, hd, hi, hj, m1, m2, rfl⟩
    exact h ((cfg_active hτ σ _).2 ⟨d, m1, m2, hd, zeta_free ha1 hd m1 hi, zeta_free ha2 hd m2 hj⟩)
  · obtain ⟨d, m1, m2, hd, h1, h2⟩ := (cfg_active hτ σ _).1 h
    obtain ⟨i, j, hi, hj, rfl⟩ := (mem_grid_iff hd).1 ⟨h1, h2⟩
    exact ⟨_, k_gsite U hd m1 m2 hi hj, cfg_rules hτ σ hd m1 m2 hi hj⟩

theorem cfg_Q1 (ξ : Plane) : (cfg U τ σ ξ).Q1 := by
  have ha1 : FrameOffsets (a1 τ) := frameOffsets_phase _
  have ha2 : FrameOffsets (a2 τ) := frameOffsets_phase _
  intro h
  obtain ⟨d, m1, m2, hd, h1, h2⟩ := (cfg_active hτ σ _).1 h
  obtain ⟨i, j, hi, hj, rfl⟩ := (mem_grid_iff hd).1 ⟨h1, h2⟩
  obtain ⟨fW, -, fS, -⟩ := cfg_grids_c (U := U) hτ σ hd m1 m2 hi hj
  rw [fW, fS]
  constructor
  · show rowMc τ (gsite τ d m1 m2 i j) = _
    unfold rowMc
    refine decide_eq_decide.2 ⟨?_, ?_⟩
    · rintro ⟨d', m, hd', hy⟩
      have f := zeta_free ha2 hd m2 hj
      have f' := isFree_rfree ha2 hd' m
      simp only [gsite] at hy
      rw [← hy] at f'
      obtain ⟨rfl, rfl⟩ := free_unique hd hd' f f'
      rw [← zeta_zero ha2 hd m2] at hy
      exact (zeta_inj ha2 hd m2 hj (by have := MachineM.two_le_Nd d; omega)).1 hy
    · rintro rfl
      exact ⟨d, m2, hd, by simp only [gsite]; exact zeta_zero ha2 hd m2⟩
  · show colMc τ (gsite τ d m1 m2 i j) = _
    unfold colMc
    refine decide_eq_decide.2 ⟨?_, ?_⟩
    · rintro ⟨d', m, hd', hx⟩
      have f := zeta_free ha1 hd m1 hi
      have f' := isFree_rfree ha1 hd' m
      simp only [gsite] at hx
      rw [← hx] at f'
      obtain ⟨rfl, rfl⟩ := free_unique hd hd' f f'
      rw [← zeta_zero ha1 hd m1] at hx
      exact (zeta_inj ha1 hd m1 hi (by have := MachineM.two_le_Nd d; omega)).1 hx
    · rintro rfl
      exact ⟨d, m1, hd, by simp only [gsite]; exact zeta_zero ha1 hd m1⟩

theorem cfg_Q2 (ξ : Plane) : (cfg U τ σ ξ).Q2 := by
  have ha1 : FrameOffsets (a1 τ) := frameOffsets_phase _
  have ha2 : FrameOffsets (a2 τ) := frameOffsets_phase _
  obtain ⟨x, y⟩ := ξ
  refine ⟨fun h => ?_, fun h => ?_⟩
  · show rowMc τ (x, y) = false
    unfold rowMc
    rw [decide_eq_false_iff_not]
    rintro ⟨d, m, hd, hy⟩
    obtain ⟨s, hs⟩ := Option.ne_none_iff_exists'.1 h
    have hf := isFree_rfree ha2 hd m
    dsimp only at hy
    rw [← hy] at hf
    rcases Setting.BT_two s with rfl | rfl
    · obtain ⟨e, he, hend, -⟩ := (colW_B hτ x y).1 hs
      exact free_not_endpoint ha2 he hf (Or.inl hend)
    · obtain ⟨e, he, hend, -⟩ := (colW_T hτ x y).1 hs
      exact free_not_endpoint ha2 he hf (Or.inr hend)
  · show colMc τ (x, y) = false
    unfold colMc
    rw [decide_eq_false_iff_not]
    rintro ⟨d, m, hd, hx⟩
    obtain ⟨s, hs⟩ := Option.ne_none_iff_exists'.1 h
    have hf := isFree_rfree ha1 hd m
    dsimp only at hx
    rw [← hx] at hf
    rcases Setting.LR_two s with rfl | rfl
    · obtain ⟨e, he, hend, -⟩ := (rowW_L hτ x y).1 hs
      exact free_not_endpoint ha1 he hf (Or.inl hend)
    · obtain ⟨e, he, hend, -⟩ := (rowW_R hτ x y).1 hs
      exact free_not_endpoint ha1 he hf (Or.inr hend)

theorem cfg_P1 (ξ : Plane) : (cfg U τ σ ξ).P1 := by
  have ha1 : FrameOffsets (a1 τ) := frameOffsets_phase _
  obtain ⟨z, y⟩ := ξ
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h' : rowMc τ (z - 1, y) = false := h
    exact ⟨by show wEc τ σ (z - 1, y) = none; rw [wEc, if_neg (by rw [h']; simp)],
      by show wEc τ σ (z, y) = none; rw [wEc, if_neg (by rw [show rowMc τ (z, y) = false from h]; simp)]⟩
  · have h' : rowMc τ (z - 1, y) = true := h
    have hm : ∃ d m, 1 ≤ d ∧ y = rfree (a2 τ) d m := by
      classical
      have := h; unfold SiteVal.rowM cfg rowMc at this; exact of_decide_eq_true this
    obtain ⟨d, m2, hd, hy⟩ := hm
    have hdep := rowDepth_eq hd hy
    refine ⟨by show wEc τ σ (z - 1, y) ≠ none; rw [wEc, if_pos h']; simp,
      by show wEc τ σ (z, y) ≠ none; rw [wEc, if_pos (show rowMc τ (z, y) = true from h)]; simp,
      fun hr => ?_, fun hr => ?_⟩
    · obtain ⟨d', m1, m2', hd', he⟩ := (cfg_isRoot hτ σ _).1 hr
      simp only [root, Prod.mk.injEq] at he
      obtain ⟨hz, hy'⟩ := he
      have e' : d' = d := by
        have := rfree_depth_unique (frameOffsets_phase _) (hy'.symm.trans hy); exact this
      subst e'
      show wEc τ σ (z, y) = some (σ (z, y))
      rw [wEc, if_pos (show rowMc τ (z, y) = true from h), hdep]
      simp only
      rw [hz, rootBelow_self]
    · show wEc τ σ (z, y) = wEc τ σ (z - 1, y)
      rw [wEc, wEc, if_pos (show rowMc τ (z, y) = true from h), if_pos h']
      simp only
      rw [hdep]
      have hnr : ∀ m, z ≠ rfree (a1 τ) d m := by
        intro m hzm
        exact hr ((cfg_isRoot hτ σ _).2 ⟨d, m, m2, hd, by simp [root, hzm, hy]⟩)
      rw [rootBelow_pred hnr]

theorem cfg_P2 (ξ : Plane) : (cfg U τ σ ξ).P2 := by
  have ha2 : FrameOffsets (a2 τ) := frameOffsets_phase _
  obtain ⟨x, z⟩ := ξ
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h' : colMc τ (x, z - 1) = false := h
    exact ⟨by show wNc τ σ (x, z - 1) = none; rw [wNc, if_neg (by rw [h']; simp)],
      by show wNc τ σ (x, z) = none; rw [wNc, if_neg (by rw [show colMc τ (x, z) = false from h]; simp)]⟩
  · have h' : colMc τ (x, z - 1) = true := h
    have hm : ∃ d m, 1 ≤ d ∧ x = rfree (a1 τ) d m := by
      classical
      have := h; unfold SiteVal.colM cfg colMc at this; exact of_decide_eq_true this
    obtain ⟨d, m1, hd, hx⟩ := hm
    have hdep := colDepth_eq hd hx
    refine ⟨by show wNc τ σ (x, z - 1) ≠ none; rw [wNc, if_pos h']; simp,
      by show wNc τ σ (x, z) ≠ none; rw [wNc, if_pos (show colMc τ (x, z) = true from h)]; simp,
      fun hr => ?_, fun hr => ?_⟩
    · obtain ⟨d', m1', m2, hd', he⟩ := (cfg_isRoot hτ σ _).1 hr
      simp only [root, Prod.mk.injEq] at he
      obtain ⟨hx', hz⟩ := he
      have e' : d' = d := by
        have := rfree_depth_unique (frameOffsets_phase _) (hx'.symm.trans hx); exact this
      subst e'
      show wNc τ σ (x, z) = some (σ (x, z))
      rw [wNc, if_pos (show colMc τ (x, z) = true from h), hdep]
      simp only
      rw [hz, rootBelow_self]
    · show wNc τ σ (x, z) = wNc τ σ (x, z - 1)
      rw [wNc, wNc, if_pos (show colMc τ (x, z) = true from h), if_pos h']
      simp only
      rw [hdep]
      have hnr : ∀ m, z ≠ rfree (a2 τ) d m := by
        intro m hzm
        exact hr ((cfg_isRoot hτ σ _).2 ⟨d, m1, m, hd, by simp [root, hzm, hx]⟩)
      rw [rootBelow_pred hnr]

omit hτ in
theorem cfg_P3 (ξ : Plane) : (cfg U τ σ ξ).P3 := by
  intro _ k hk _
  obtain ⟨hx, -⟩ := kF_xy U hk
  rw [hx]
  exact ⟨fun h => absurd h.2 (by simp), fun h => absurd h.2 (by simp)⟩

theorem cfg_allowed (ξ : Plane) : (cfg U τ σ ξ).Allowed :=
  ⟨cfg_O1 hτ σ ξ, cfg_O2 hτ σ ξ, cfg_E1 σ ξ, cfg_E2 hτ σ ξ, cfg_E3 hτ σ ξ, cfg_K1 hτ σ ξ,
    cfg_K2 hτ σ ξ, cfg_K3 hτ σ ξ, cfg_Q1 hτ σ ξ, cfg_Q2 hτ σ ξ, cfg_P1 hτ σ ξ, cfg_P2 hτ σ ξ,
    cfg_P3 σ ξ⟩

theorem cfg_matchH (ξ : Plane) : (cfg U τ σ ξ).cE = (cfg U τ σ (ξ + e1)).cW := by
  obtain ⟨z, y⟩ := ξ
  rw [add_e1]
  have hq : (qtilingOf τ (z, y)).colE = (qtilingOf τ (z + 1, y)).colW := by
    have := (qphase_cfg hτ).1.1 (z, y) trivial trivial
    simp only [Prod.mk_add_mk, add_zero] at this
    exact this
  show ((qtilingOf τ (z, y)).colE, oEc τ (z, y), eEc τ (z, y), lEc U τ (z, y), rowMc τ (z, y),
      wEc τ σ (z, y)) = ((qtilingOf τ (z + 1, y)).colW, oEc τ (z + 1 - 1, y), eEc τ (z + 1 - 1, y),
      lEc U τ (z + 1 - 1, y), rowMc τ (z + 1, y), wEc τ σ (z + 1 - 1, y))
  rw [add_sub_cancel_right, hq]
  rfl

theorem cfg_matchV (ξ : Plane) : (cfg U τ σ ξ).cN = (cfg U τ σ (ξ + e2)).cS := by
  obtain ⟨x, z⟩ := ξ
  rw [add_e2]
  have hq : (qtilingOf τ (x, z)).colN = (qtilingOf τ (x, z + 1)).colS := by
    have := (qphase_cfg hτ).1.2 (x, z) trivial trivial
    simp only [Prod.mk_add_mk, add_zero] at this
    exact this
  show ((qtilingOf τ (x, z)).colN, oNc τ (x, z), eNc τ (x, z), lNc U τ (x, z), colMc τ (x, z),
      wNc τ σ (x, z)) = ((qtilingOf τ (x, z + 1)).colS, oNc τ (x, z + 1 - 1), eNc τ (x, z + 1 - 1),
      lNc U τ (x, z + 1 - 1), colMc τ (x, z + 1), wNc τ σ (x, z + 1 - 1))
  rw [add_sub_cancel_right, hq]
  rfl

/-- **`prop:background`(b)**: for typical `τ` the configuration `cfg U τ σ` (spins `σ`, wire
values from the spins at the roots, switches and free bits `0`) is legal. -/
theorem cfg_legal : IsLegal (Phi U) (cfg U τ σ) :=
  legal_of (cfg_allowed hτ σ) (cfg_matchH hτ σ) (cfg_matchV hτ σ)

/-- The construction satisfies the standing assumption of Section 5. -/
theorem cfg_setting : Setting (cfg U τ σ) τ := ⟨cfg_legal hτ σ, (qphase_cfg hτ).2, hτ⟩

end Legal

end UPD.BG

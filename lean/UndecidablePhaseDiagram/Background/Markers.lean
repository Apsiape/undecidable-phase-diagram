/-
# Section 5.3: markers and roots (`bg:markers`)

New in this project.

* Matching makes `𝔯` constant along rows and `𝔠` constant along columns (`rowM_const`,
  `colM_const`).
* **`bg:markers`**: (a) `markers_a_row` (`𝔯(ξ) = 1` iff `ξ₂ = r^{(2)}_d(m)` for some `d ≥ 1`,
  `m`), `markers_a_col`; the depth is unique by `scf:frames`(d) (`rfree_depth_unique`);
  (b) `markers_b_row`, `markers_b_col` (the roots on a root row of depth `d` are the
  `𝐫_d(m₁, m₂)`, `m₁ ∈ ℤ`), `rfree_succ` (consecutive ones are `4^{d+1}` apart);
  (c) `markers_c_row` (a root row of depth `d` has light vertical walls at the endpoints of the
  column frames of depth `d` and no light horizontal wall), `markers_c_col`.
-/
import UndecidablePhaseDiagram.Background.Grids

set_option autoImplicit false

namespace UPD.BG

open UPD.Scaffold

variable {U : Machine}

/-- **`bg:markers`(b)**: consecutive least free coordinates are `4^{d+1}` apart. -/
theorem rfree_succ (a : ℕ → ℤ) (d : ℕ) (m : ℤ) : rfree a d (m + 1) - rfree a d m = 4 ^ (d + 1) := by
  simp only [rfree, frameLo, pow_succ]; ring

theorem rfree_inj {a : ℕ → ℤ} {d : ℕ} {m m' : ℤ} (h : rfree a d m = rfree a d m') : m = m' := by
  have hp : (0 : ℤ) < 4 ^ d := by positivity
  simp only [rfree, frameLo] at h
  have : (m - m') * (4 * 4 ^ d) = 0 := by linarith
  rcases mul_eq_zero.1 this with h | h
  · linarith
  · linarith

/-- A free coordinate of depth `d` is an endpoint of no frame of a depth `e ≥ 1` with
`InFrame a d z` excluded below: it is in no frame of depth `< d`, it is interior to its frame of
depth `d`, and endpoints of deeper frames avoid the frames of depth `d`. -/
theorem free_not_endpoint {a : ℕ → ℤ} (ha : FrameOffsets a) {d e : ℕ} (he : 1 ≤ e) {m : ℤ}
    {y : ℤ} (hy : IsFree a d m y) (hend : IsLeftEnd a e y ∨ IsRightEnd a e y) : False := by
  have hlh := frameLo_lt_frameHi a
  rcases lt_trichotomy e d with hlt | rfl | hlt
  · rcases hend with ⟨m', rfl⟩ | ⟨m', rfl⟩
    · exact hy.2.2 e he hlt ⟨m', le_rfl, (hlh e m').le⟩
    · exact hy.2.2 e he hlt ⟨m', (hlh e m').le, le_rfl⟩
  · rcases hend with ⟨m', hm'⟩ | ⟨m', hm'⟩
    · have := frame_window_unique (a := a) (d := e) ⟨hy.1.le, hy.2.1.le⟩
        ⟨hm'.ge, by rw [hm']; exact (hlh e m').le⟩
      subst this; exact absurd hm' (ne_of_gt hy.1)
    · have := frame_window_unique (a := a) (d := e) ⟨hy.1.le, hy.2.1.le⟩
        ⟨by rw [hm']; exact (hlh e m').le, hm'.le⟩
      subst this; exact absurd hm' (ne_of_lt hy.2.1)
  · rcases hend with ⟨m', rfl⟩ | ⟨m', rfl⟩
    · exact (endpoint_not_inFrame ha hlt m').1 ⟨m, hy.1.le, hy.2.1.le⟩
    · exact (endpoint_not_inFrame ha hlt m').2 ⟨m, hy.1.le, hy.2.1.le⟩

namespace Setting

variable {ω : Config (SiteVal U)} {τ : ℕ → Bool × Bool} (hs : Setting ω τ)
include hs

theorem rowM_add (z y : ℤ) (k : ℕ) : (ω (z + k, y)).rowM = (ω (z, y)).rowM := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← ih, show z + ((k + 1 : ℕ) : ℤ) = (z + k) + 1 by push_cast; ring, ← hs.rowM_eq]

/-- Matching makes `𝔯` constant along rows. -/
theorem rowM_const (z z' y : ℤ) : (ω (z, y)).rowM = (ω (z', y)).rowM := by
  rcases le_total z z' with h | h
  · have := hs.rowM_add z y (z' - z).toNat
    rw [show z + ((z' - z).toNat : ℤ) = z' by omega] at this; exact this.symm
  · have := hs.rowM_add z' y (z - z').toNat
    rw [show z' + ((z - z').toNat : ℤ) = z by omega] at this; exact this

theorem colM_add (x z : ℤ) (k : ℕ) : (ω (x, z + k)).colM = (ω (x, z)).colM := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← ih, show z + ((k + 1 : ℕ) : ℤ) = (z + k) + 1 by push_cast; ring, ← hs.colM_eq]

/-- Matching makes `𝔠` constant along columns. -/
theorem colM_const (x z z' : ℤ) : (ω (x, z)).colM = (ω (x, z')).colM := by
  rcases le_total z z' with h | h
  · have := hs.colM_add x z (z' - z).toNat
    rw [show z + ((z' - z).toNat : ℤ) = z' by omega] at this; exact this.symm
  · have := hs.colM_add x z' (z - z').toNat
    rw [show z' + ((z - z').toNat : ℤ) = z by omega] at this; exact this

/-- **`bg:markers`(a)** (rows): `𝔯(ξ) = 1` iff `ξ₂ = r^{(2)}_d(m)` for some `d ≥ 1` and `m ∈ ℤ`. -/
theorem markers_a_row (ξ : Plane) :
    (ω ξ).rowM = true ↔ ∃ d m, 1 ≤ d ∧ ξ.2 = rfree (a2 τ) d m := by
  have ha1 : FrameOffsets (a1 τ) := frameOffsets_phase _
  have ha2 : FrameOffsets (a2 τ) := frameOffsets_phase _
  obtain ⟨x, y⟩ := ξ
  simp only
  set d := hs.own2 y with hd_def
  have hd : 1 ≤ d := (own_spec (a2 τ) hs.typical.inFrame_row y).1
  obtain ⟨m', hm1, hm2⟩ : InFrame (a2 τ) d y := (own_spec (a2 τ) hs.typical.inFrame_row y).2
  have hlh := frameLo_lt_frameHi (a1 τ) d 0
  by_cases hend : y = frameLo (a2 τ) d m' ∨ y = frameHi (a2 τ) d m'
  · -- an endpoint row: a light horizontal wall seeds `𝔯 = 0`
    have hz : InFrame (a1 τ) d (frameLo (a1 τ) d 0) := ⟨0, le_rfl, hlh.le⟩
    have hHW : (ω (frameLo (a1 τ) d 0, y)).q.HW ≠ none := by
      rcases hend with h | h
      · rw [(hs.HW_B _ _).2 ⟨d, hd, ⟨m', h⟩, hz⟩]; simp
      · rw [(hs.HW_T _ _).2 ⟨d, hd, ⟨m', h⟩, hz⟩]; simp
    have h0 := (hs.Q2 (frameLo (a1 τ) d 0, y)).1 hHW
    rw [hs.rowM_const x (frameLo (a1 τ) d 0) y, h0]
    simp only [Bool.false_eq_true, false_iff, not_exists, not_and]
    intro e m he hy
    have hfree := isFree_rfree ha2 he m
    rw [← hy] at hfree
    refine free_not_endpoint ha2 hd hfree ?_
    rcases hend with h | h
    · exact Or.inl ⟨m', h⟩
    · exact Or.inr ⟨m', h⟩
  · -- a free row of depth `d`: `𝔯 = f_S` at its active sites
    push Not at hend
    have hy : IsFree (a2 τ) d m' y :=
      isFree_own (a := a2 τ) (h := hs.typical.inFrame_row) (lt_of_le_of_ne hm1 (Ne.symm hend.1))
        (lt_of_le_of_ne hm2 hend.2)
    have hx := isFree_rfree ha1 hd 0
    have hact := hs.active_of_free (ξ := (rfree (a1 τ) d 0, y)) hd hx hy
    obtain ⟨-, -, hS, -⟩ := hs.flags (ξ := (rfree (a1 τ) d 0, y)) hd hx hy
    rw [hs.rowM_const x (rfree (a1 τ) d 0) y, ((hs.Q1 _) hact).1, hS]
    simp only [decide_eq_true_iff]
    constructor
    · intro h; exact ⟨d, m', hd, h⟩
    · rintro ⟨e, m, he, hym⟩
      have hfree := isFree_rfree ha2 he m
      rw [← hym] at hfree
      have hed : e = d := (own_eq_of_isFree he hfree).symm.trans rfl
      subst hed
      have := frame_window_unique (a := a2 τ) ⟨hfree.1.le, hfree.2.1.le⟩ ⟨hy.1.le, hy.2.1.le⟩
      subst this
      exact hym

/-- **`bg:markers`(a)** (columns): `𝔠(ξ) = 1` iff `ξ₁ = r^{(1)}_d(m)` for some `d ≥ 1` and
`m ∈ ℤ`. -/
theorem markers_a_col (ξ : Plane) :
    (ω ξ).colM = true ↔ ∃ d m, 1 ≤ d ∧ ξ.1 = rfree (a1 τ) d m := by
  have ha1 : FrameOffsets (a1 τ) := frameOffsets_phase _
  have ha2 : FrameOffsets (a2 τ) := frameOffsets_phase _
  obtain ⟨x, y⟩ := ξ
  simp only
  set d := hs.own1 x with hd_def
  have hd : 1 ≤ d := (own_spec (a1 τ) hs.typical.inFrame_col x).1
  obtain ⟨m', hm1, hm2⟩ : InFrame (a1 τ) d x := (own_spec (a1 τ) hs.typical.inFrame_col x).2
  have hlh := frameLo_lt_frameHi (a2 τ) d 0
  by_cases hend : x = frameLo (a1 τ) d m' ∨ x = frameHi (a1 τ) d m'
  · have hz : InFrame (a2 τ) d (frameLo (a2 τ) d 0) := ⟨0, le_rfl, hlh.le⟩
    have hVW : (ω (x, frameLo (a2 τ) d 0)).q.VW ≠ none := by
      rcases hend with h | h
      · rw [(hs.VW_L _ _).2 ⟨d, hd, ⟨m', h⟩, hz⟩]; simp
      · rw [(hs.VW_R _ _).2 ⟨d, hd, ⟨m', h⟩, hz⟩]; simp
    have h0 := (hs.Q2 (x, frameLo (a2 τ) d 0)).2 hVW
    rw [hs.colM_const x y (frameLo (a2 τ) d 0), h0]
    simp only [Bool.false_eq_true, false_iff, not_exists, not_and]
    intro e m he hx
    have hfree := isFree_rfree ha1 he m
    rw [← hx] at hfree
    refine free_not_endpoint ha1 hd hfree ?_
    rcases hend with h | h
    · exact Or.inl ⟨m', h⟩
    · exact Or.inr ⟨m', h⟩
  · push Not at hend
    have hx : IsFree (a1 τ) d m' x :=
      isFree_own (a := a1 τ) (h := hs.typical.inFrame_col) (lt_of_le_of_ne hm1 (Ne.symm hend.1))
        (lt_of_le_of_ne hm2 hend.2)
    have hy := isFree_rfree ha2 hd 0
    have hact := hs.active_of_free (ξ := (x, rfree (a2 τ) d 0)) hd hx hy
    obtain ⟨hW, -, -, -⟩ := hs.flags (ξ := (x, rfree (a2 τ) d 0)) hd hx hy
    rw [hs.colM_const x y (rfree (a2 τ) d 0), ((hs.Q1 _) hact).2, hW]
    simp only [decide_eq_true_iff]
    constructor
    · intro h; exact ⟨d, m', hd, h⟩
    · rintro ⟨e, m, he, hxm⟩
      have hfree := isFree_rfree ha1 he m
      rw [← hxm] at hfree
      have hed : e = d := (own_eq_of_isFree he hfree).symm.trans rfl
      subst hed
      have := frame_window_unique (a := a1 τ) ⟨hfree.1.le, hfree.2.1.le⟩ ⟨hx.1.le, hx.2.1.le⟩
      subst this
      exact hxm

/-- **`bg:markers`(b)** (rows): the roots on the root row `r^{(2)}_d(m₂)` of depth `d` are the
sites `𝐫_d(m₁, m₂)`, `m₁ ∈ ℤ` (consecutive ones `4^{d+1}` apart, `rfree_succ`). -/
theorem markers_b_row {d : ℕ} (hd : 1 ≤ d) (m2 : ℤ) {ξ : Plane}
    (hξ : ξ.2 = rfree (a2 τ) d m2) : (ω ξ).IsRoot ↔ ∃ m1, ξ = root τ d m1 m2 := by
  rw [hs.isRoot_iff]
  constructor
  · rintro ⟨e, m1, m2', he, rfl⟩
    simp only [root] at hξ
    have hed := rfree_depth_unique (frameOffsets_phase _) hξ
    subst hed
    exact ⟨m1, by rw [rfree_inj hξ]⟩
  · rintro ⟨m1, rfl⟩; exact ⟨d, m1, m2, hd, rfl⟩

/-- **`bg:markers`(b)** (columns). -/
theorem markers_b_col {d : ℕ} (hd : 1 ≤ d) (m1 : ℤ) {ξ : Plane}
    (hξ : ξ.1 = rfree (a1 τ) d m1) : (ω ξ).IsRoot ↔ ∃ m2, ξ = root τ d m1 m2 := by
  rw [hs.isRoot_iff]
  constructor
  · rintro ⟨e, m1', m2, he, rfl⟩
    simp only [root] at hξ
    have hed := rfree_depth_unique (frameOffsets_phase _) hξ
    subst hed
    exact ⟨m2, by rw [rfree_inj hξ]⟩
  · rintro ⟨m2, rfl⟩; exact ⟨d, m1, m2, hd, rfl⟩

/-- **`bg:markers`(c)** (rows): a root row of depth `d` contains light vertical walls, at the
endpoints of the column frames of depth `d`, and no light horizontal wall. -/
theorem markers_c_row {d : ℕ} (hd : 1 ≤ d) (m2 : ℤ) :
    (∀ m, (ω (frameLo (a1 τ) d m, rfree (a2 τ) d m2)).q.VW = some .L ∧
      (ω (frameHi (a1 τ) d m, rfree (a2 τ) d m2)).q.VW = some .R) ∧
    ∀ z, (ω (z, rfree (a2 τ) d m2)).q.HW = none := by
  have ha2 : FrameOffsets (a2 τ) := frameOffsets_phase _
  have hy := isFree_rfree ha2 hd m2
  have iy : InFrame (a2 τ) d (rfree (a2 τ) d m2) := ⟨m2, hy.1.le, hy.2.1.le⟩
  refine ⟨fun m => ⟨(hs.VW_L _ _).2 ⟨d, hd, ⟨m, rfl⟩, iy⟩, (hs.VW_R _ _).2 ⟨d, hd, ⟨m, rfl⟩, iy⟩⟩,
    fun z => ?_⟩
  rcases h : (ω (z, rfree (a2 τ) d m2)).q.HW with _ | s
  · rfl
  · exfalso
    rcases BT_two s with rfl | rfl
    · obtain ⟨e, he, hend, -⟩ := (hs.HW_B _ _).1 h
      exact free_not_endpoint ha2 he hy (Or.inl hend)
    · obtain ⟨e, he, hend, -⟩ := (hs.HW_T _ _).1 h
      exact free_not_endpoint ha2 he hy (Or.inr hend)

/-- **`bg:markers`(c)** (columns): a root column of depth `d` contains light horizontal walls, at
the endpoints of the row frames of depth `d`, and no light vertical wall. -/
theorem markers_c_col {d : ℕ} (hd : 1 ≤ d) (m1 : ℤ) :
    (∀ m, (ω (rfree (a1 τ) d m1, frameLo (a2 τ) d m)).q.HW = some .B ∧
      (ω (rfree (a1 τ) d m1, frameHi (a2 τ) d m)).q.HW = some .T) ∧
    ∀ z, (ω (rfree (a1 τ) d m1, z)).q.VW = none := by
  have ha1 : FrameOffsets (a1 τ) := frameOffsets_phase _
  have hx := isFree_rfree ha1 hd m1
  have ix : InFrame (a1 τ) d (rfree (a1 τ) d m1) := ⟨m1, hx.1.le, hx.2.1.le⟩
  refine ⟨fun m => ⟨(hs.HW_B _ _).2 ⟨d, hd, ⟨m, rfl⟩, ix⟩, (hs.HW_T _ _).2 ⟨d, hd, ⟨m, rfl⟩, ix⟩⟩,
    fun z => ?_⟩
  rcases h : (ω (rfree (a1 τ) d m1, z)).q.VW with _ | s
  · rfl
  · exfalso
    rcases LR_two s with rfl | rfl
    · obtain ⟨e, he, hend, -⟩ := (hs.VW_L _ _).1 h
      exact free_not_endpoint ha1 he hx (Or.inl hend)
    · obtain ⟨e, he, hend, -⟩ := (hs.VW_R _ _).1 h
      exact free_not_endpoint ha1 he hx (Or.inr hend)

end Setting

end UPD.BG

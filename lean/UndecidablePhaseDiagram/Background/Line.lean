/-
# Section 5.1: corridors and carriers along one line (`prop:routing`, abstractly)

New in this project. The beginning of Section 5 ("Fix a row `y`. Let `D(y)` be the set of depths
`d` such that `y` lies in a row frame of depth `d` … We call these sites the walls of the row …
The frames of depth `own₂(y)` occur periodically in both directions, so the walls of the row are
unbounded on both sides") and the proofs of `prop:routing`(a), (b), read along one line. A row
and a column are the same once the frames along the line (offsets `a`) and across it (offsets `b`,
the line at the cross coordinate `y`) are named; `Background/Routing.lean` instantiates this file
twice (rows: `VW`, `o^E`; columns: `HW`, `o^N`).

* `Line`: walls `W` (`W z = L` iff `z` is a left endpoint of a frame of a depth `e` with `y` in a
  cross frame of depth `e`, likewise `R`, by `scf:walls`), tags `o z` on the edge `(z, z + 1)`
  that are copied across non-walls (O1 and matching) and name the side of a wall next to them.
* `d0 = own(y)`; `wall_lo`, `wall_hi`: the endpoints of the frames of depth `d0` are walls;
  `interior_none`: a frame of depth `d0` has no wall in its interior; `exists_wall_lt`,
  `exists_wall_gt`: walls are unbounded on both sides; `exists_nearest`.
* **`routing`** (`prop:routing`(a)): the tag of an edge is the pair of the sides of the nearest
  walls.
* **`carrier_iff`** (`prop:routing`(b)): off the walls, `o(z - 1) = (L, R)` iff `z` lies in the
  interior of a frame of depth `d0` (the paper's `app:laminar` argument, done directly with
  `scf:frames`(a), (b)).
* `EvLine`: event tags (E1), (E2) along the line; `first_wall`, `second_wall`: in a frame of depth
  `d0` whose first and last interior sites are active, the first entry of the event tag of an edge
  is `wall` only on the first edge, and the second entry only on the last edge (the proof of
  `bg:grids`(c)).
* `chain`: values copied across a run of sites (logical colours along channels, `bg:grid`).
-/
import UndecidablePhaseDiagram.Scaffold.Typical

set_option autoImplicit false

namespace UPD.BG

open UPD.Scaffold

/-! ## Copying along a run of sites -/

/-- Values `f z` on the edge `(z, z + 1)` read from the west (`f`) and from the east (`g`) of the
sites: matching `f z = g (z + 1)`, and the sites strictly between `p` and `q` copy (`g x = f x`).
Then `f p = g q`. -/
theorem chain {α : Type} {f g : ℤ → α} (hm : ∀ z, f z = g (z + 1)) {p q : ℤ} (hpq : p < q)
    (hc : ∀ x, p < x → x < q → g x = f x) : f p = g q := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, q = p + 1 + k := ⟨(q - p - 1).toNat, by omega⟩
  subst hk
  induction k with
  | zero => simpa using hm p
  | succ k ih =>
    rw [ih (by omega) (fun x h1 h2 => hc x h1 (by push_cast; omega)),
      hc _ (by omega) (by push_cast; omega), hm]
    congr 1; push_cast; ring

/-- `chain`, read from the other end. -/
theorem chain' {α : Type} {f g : ℤ → α} (hm : ∀ z, f z = g (z + 1)) {p q : ℤ} (hpq : p < q)
    (hc : ∀ x, p < x → x < q → g x = f x) : g q = f p := (chain hm hpq hc).symm

/-! ## Lines -/

/-- A line (a row or a column) of a legal configuration with typical quarter phase: frames along
the line have offsets `a`, frames across it have offsets `b` (every integer lies in a cross frame,
the remark after `scf:def-typical`), and the line sits at the cross coordinate `y`. `W z` is the
wall at the site `z` of the line (`scf:walls`), `o z` the orientation tag of the edge `(z, z + 1)`.
`S` is `{L, R}` (rows) or `{B, T}` (columns). -/
structure Line (S : Type) where
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
  /-- the wall at a site of the line (`VW` or `HW`) -/
  W : ℤ → Option S
  wallL : ∀ z, W z = some L ↔ ∃ e, 1 ≤ e ∧ IsLeftEnd a e z ∧ InFrame b e y
  wallR : ∀ z, W z = some R ↔ ∃ e, 1 ≤ e ∧ IsRightEnd a e z ∧ InFrame b e y
  /-- the orientation tag of the edge `(z, z + 1)` -/
  o : ℤ → S × S
  /-- (O1) at a non-wall and matching: the tag is copied -/
  copy : ∀ z, W (z + 1) = none → o (z + 1) = o z
  /-- (O1) at a wall: the first entry of the tag east of it is its side -/
  left : ∀ z s, W z = some s → (o z).1 = s
  /-- (O1) at a wall and matching: the second entry of the tag west of it is its side -/
  right : ∀ z s, W (z + 1) = some s → (o z).2 = s

namespace Line

variable {S : Type} (l : Line S)

/-- `own(y)`: the least depth of a cross frame containing the line. -/
noncomputable def d0 : ℕ := own l.b l.hb l.y

theorem one_le_d0 : 1 ≤ l.d0 := (own_spec l.b l.hb l.y).1

theorem inFrame_d0 : InFrame l.b l.d0 l.y := (own_spec l.b l.hb l.y).2

theorem d0_le {e : ℕ} (he : 1 ≤ e) (h : InFrame l.b e l.y) : l.d0 ≤ e := own_le l.b l.hb he h

theorem wall_iff (z : ℤ) : l.W z ≠ none ↔
    ∃ e, 1 ≤ e ∧ (IsLeftEnd l.a e z ∨ IsRightEnd l.a e z) ∧ InFrame l.b e l.y := by
  constructor
  · intro h
    obtain ⟨s, hs⟩ := Option.ne_none_iff_exists'.1 h
    rcases l.two s with rfl | rfl
    · obtain ⟨e, he, h1, h2⟩ := (l.wallL z).1 hs
      exact ⟨e, he, Or.inl h1, h2⟩
    · obtain ⟨e, he, h1, h2⟩ := (l.wallR z).1 hs
      exact ⟨e, he, Or.inr h1, h2⟩
  · rintro ⟨e, he, h1 | h1, h2⟩
    · rw [(l.wallL z).2 ⟨e, he, h1, h2⟩]; simp
    · rw [(l.wallR z).2 ⟨e, he, h1, h2⟩]; simp

/-- The endpoints of the frames of depth `own(y)` are walls of the line. -/
theorem wall_lo (m : ℤ) : l.W (frameLo l.a l.d0 m) = some l.L :=
  (l.wallL _).2 ⟨l.d0, l.one_le_d0, ⟨m, rfl⟩, l.inFrame_d0⟩

theorem wall_hi (m : ℤ) : l.W (frameHi l.a l.d0 m) = some l.R :=
  (l.wallR _).2 ⟨l.d0, l.one_le_d0, ⟨m, rfl⟩, l.inFrame_d0⟩

/-- A frame of depth `own(y)` contains no wall in its interior (its endpoints are consecutive
walls). -/
theorem interior_none {m z : ℤ} (h1 : frameLo l.a l.d0 m < z) (h2 : z < frameHi l.a l.d0 m) :
    l.W z = none := by
  by_contra hne
  obtain ⟨e, he, hend, hy⟩ := (l.wall_iff z).1 hne
  have hle := l.d0_le he hy
  have hz : InFrame l.a l.d0 z := ⟨m, h1.le, h2.le⟩
  rcases Nat.lt_or_ge l.d0 e with hlt | hge
  · rcases hend with ⟨m', rfl⟩ | ⟨m', rfl⟩
    · exact (endpoint_not_inFrame l.ha hlt m').1 hz
    · exact (endpoint_not_inFrame l.ha hlt m').2 hz
  · have he' : e = l.d0 := le_antisymm hge hle
    rw [he'] at hend
    have hlh := frameLo_lt_frameHi l.a l.d0
    rcases hend with ⟨m', rfl⟩ | ⟨m', rfl⟩
    · have := frame_window_unique (a := l.a) ⟨h1.le, h2.le⟩ ⟨le_rfl, (hlh m').le⟩
      subst this; omega
    · have := frame_window_unique (a := l.a) ⟨h1.le, h2.le⟩ ⟨(hlh m').le, le_rfl⟩
      subst this; omega

theorem frameLo_lt (a : ℕ → ℤ) (d : ℕ) (z : ℤ) : ∃ m, frameLo a d m < z := by
  have hp : (1 : ℤ) ≤ 4 ^ d := one_le_pow₀ (by norm_num)
  refine ⟨-(|z| + |a d|) - 1, ?_⟩
  simp only [frameLo]
  have h1 := neg_abs_le z
  have h2 := le_abs_self (a d)
  have h4 := abs_nonneg z
  have h5 := abs_nonneg (a d)
  have h3 : (4 * (-(|z| + |a d|) - 1) + 1) * 4 ^ d ≤ 4 * (-(|z| + |a d|) - 1) + 1 := by
    have : 4 * (-(|z| + |a d|) - 1) + 1 ≤ 0 := by
      have := abs_nonneg z; have := abs_nonneg (a d); linarith
    nlinarith
  linarith

theorem lt_frameHi (a : ℕ → ℤ) (d : ℕ) (z : ℤ) : ∃ m, z < frameHi a d m := by
  have hp : (1 : ℤ) ≤ 4 ^ d := one_le_pow₀ (by norm_num)
  refine ⟨|z| + |a d|, ?_⟩
  simp only [frameHi]
  have h1 := le_abs_self z
  have h2 := neg_abs_le (a d)
  have h4 := abs_nonneg z
  have h5 := abs_nonneg (a d)
  have h3 : 4 * (|z| + |a d|) + 3 ≤ (4 * (|z| + |a d|) + 3) * 4 ^ d := by
    have : 0 ≤ 4 * (|z| + |a d|) + 3 := by
      have := abs_nonneg z; have := abs_nonneg (a d); linarith
    nlinarith
  linarith

/-- The walls of the line are unbounded below. -/
theorem exists_wall_lt (z : ℤ) : ∃ w, w < z ∧ l.W w ≠ none := by
  obtain ⟨m, hm⟩ := frameLo_lt l.a l.d0 z
  exact ⟨_, hm, by rw [l.wall_lo m]; simp⟩

/-- The walls of the line are unbounded above. -/
theorem exists_wall_gt (z : ℤ) : ∃ w, z < w ∧ l.W w ≠ none := by
  obtain ⟨m, hm⟩ := lt_frameHi l.a l.d0 z
  exact ⟨_, hm, by rw [l.wall_hi m]; simp⟩

/-- The nearest walls on both sides of a non-wall. -/
theorem exists_nearest {z : ℤ} (hz : l.W z = none) : ∃ wl wr : ℤ, ∃ sl sr : S,
    wl < z ∧ z < wr ∧ l.W wl = some sl ∧ l.W wr = some sr ∧
      ∀ x, wl < x → x < wr → l.W x = none := by
  obtain ⟨wl, ⟨hl1, hl2⟩, hlmax⟩ := Int.exists_greatest_of_bdd (P := fun x => x < z ∧ l.W x ≠ none)
    ⟨z, fun x hx => hx.1.le⟩ (l.exists_wall_lt z)
  obtain ⟨wr, ⟨hr1, hr2⟩, hrmin⟩ := Int.exists_least_of_bdd (P := fun x => z < x ∧ l.W x ≠ none)
    ⟨z, fun x hx => hx.1.le⟩ (l.exists_wall_gt z)
  obtain ⟨sl, hsl⟩ := Option.ne_none_iff_exists'.1 hl2
  obtain ⟨sr, hsr⟩ := Option.ne_none_iff_exists'.1 hr2
  refine ⟨wl, wr, sl, sr, hl1, hr1, hsl, hsr, fun x h1 h2 => ?_⟩
  by_contra hx
  rcases lt_trichotomy x z with hxz | rfl | hxz
  · have := hlmax x ⟨hxz, hx⟩; omega
  · exact hx hz
  · have := hrmin x ⟨hxz, hx⟩; omega

/-- The tag is constant between walls. -/
theorem o_const (z : ℤ) (k : ℕ) (h : ∀ i : ℕ, 1 ≤ i → i ≤ k → l.W (z + i) = none) :
    l.o (z + k) = l.o z := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 : l.W (z + k + 1) = none := by
      have := h (k + 1) (by omega) le_rfl; push_cast at this; rwa [← add_assoc] at this
    push_cast
    rw [← add_assoc, l.copy _ h1, ih (fun i h1 h2 => h i h1 (by omega))]

/-- **`prop:routing`(a)**, along one line: if `wl ≤ z` is the largest wall at or before `z` and
`wr ≥ z + 1` the smallest wall at or after `z + 1`, the tag of the edge `(z, z + 1)` is the pair
of their sides. -/
theorem routing {z wl wr : ℤ} {sl sr : S} (hl : wl ≤ z) (hwl : l.W wl = some sl)
    (hl' : ∀ x, wl < x → x ≤ z → l.W x = none) (hr : z < wr) (hwr : l.W wr = some sr)
    (hr' : ∀ x, z < x → x < wr → l.W x = none) : l.o z = (sl, sr) := by
  have e1 : l.o z = l.o wl := by
    have := l.o_const wl (z - wl).toNat (fun i h1 h2 => hl' _ (by omega) (by omega))
    rwa [show wl + ((z - wl).toNat : ℤ) = z by omega] at this
  have e2 : l.o (wr - 1) = l.o z := by
    have := l.o_const z (wr - 1 - z).toNat (fun i h1 h2 => hr' _ (by omega) (by omega))
    rwa [show z + ((wr - 1 - z).toNat : ℤ) = wr - 1 by omega] at this
  have h1 : (l.o z).1 = sl := by rw [e1]; exact l.left wl sl hwl
  have h2 : (l.o z).2 = sr := by
    rw [← e2]; exact l.right (wr - 1) sr (by rwa [sub_add_cancel])
  exact Prod.ext h1 h2

/-- **`prop:routing`(b)**, along one line: off the walls, the tag `(L, R)` west of `z` marks
exactly the interiors of the frames of depth `own(y)`. -/
theorem carrier_iff {z : ℤ} (hz : l.W z = none) :
    l.o (z - 1) = (l.L, l.R) ↔ ∃ m, frameLo l.a l.d0 m < z ∧ z < frameHi l.a l.d0 m := by
  constructor
  · intro ho
    obtain ⟨wl, wr, sl, sr, hl, hr, hwl, hwr, hbetween⟩ := l.exists_nearest hz
    have hrt := l.routing (z := z - 1) (by omega) hwl
      (fun x h1 h2 => hbetween x h1 (by omega)) (by omega) hwr
      (fun x h1 h2 => hbetween x (by omega) h2)
    rw [ho, Prod.mk.injEq] at hrt
    obtain ⟨rfl, rfl⟩ := hrt
    obtain ⟨e, he, ⟨m, hm⟩, hey⟩ := (l.wallL wl).1 hwl
    obtain ⟨e', he', ⟨m', hm'⟩, hey'⟩ := (l.wallR wr).1 hwr
    -- the other endpoints of the two frames are walls outside `(wl, wr)`
    have hlh := frameLo_lt_frameHi l.a
    have hA : wr ≤ frameHi l.a e m := by
      by_contra hc
      have := hbetween (frameHi l.a e m) (by rw [hm]; exact hlh e m) (by omega)
      rw [(l.wallR _).2 ⟨e, he, ⟨m, rfl⟩, hey⟩] at this
      exact Option.some_ne_none _ this
    have hB : frameLo l.a e' m' ≤ wl := by
      by_contra hc
      have := hbetween (frameLo l.a e' m') (by omega) (by rw [hm']; exact hlh e' m')
      rw [(l.wallL _).2 ⟨e', he', ⟨m', rfl⟩, hey'⟩] at this
      exact Option.some_ne_none _ this
    -- the two frames are the same
    have hee : e = e' := by
      rcases lt_trichotomy e e' with hlt | heq | hlt
      · rcases frames_nested l.ha hlt m' m with (h | h) | h <;> omega
      · exact heq
      · rcases frames_nested l.ha hlt m m' with (h | h) | h <;> omega
    subst hee
    have hmm : m = m' := frame_window_unique (a := l.a) (z := wl) ⟨by omega, by omega⟩
      ⟨hB, by omega⟩
    subst hmm
    -- and its depth is `own(y)`
    have hde : e = l.d0 := by
      rcases Nat.lt_or_ge l.d0 e with hlt | hge
      · exfalso
        obtain ⟨m'', h1, h2⟩ := frames_contain l.a hlt m
        have hne : frameLo l.a e m ≠ frameLo l.a l.d0 m'' := by
          intro h
          exact (endpoint_not_inFrame l.ha hlt m).1 ⟨m'', by rw [h], by rw [h]; exact (hlh _ _).le⟩
        have := hbetween (frameLo l.a l.d0 m'') (by omega) (by have := hlh l.d0 m''; omega)
        rw [l.wall_lo] at this
        exact Option.some_ne_none _ this
      · exact le_antisymm hge (l.d0_le he hey)
    subst hde
    exact ⟨m, by omega, by omega⟩
  · rintro ⟨m, h1, h2⟩
    exact l.routing (z := z - 1) (wl := frameLo l.a l.d0 m) (wr := frameHi l.a l.d0 m)
      (by omega) (l.wall_lo m) (fun x hx1 hx2 => l.interior_none hx1 (by omega)) (by omega)
      (l.wall_hi m) (fun x hx1 hx2 => l.interior_none (by omega) hx2)

/-- The tags inside a frame of depth `own(y)` are `(L, R)` (including its first and last edge). -/
theorem o_frame {m z : ℤ} (h1 : frameLo l.a l.d0 m ≤ z) (h2 : z < frameHi l.a l.d0 m) :
    l.o z = (l.L, l.R) :=
  l.routing (wl := frameLo l.a l.d0 m) (wr := frameHi l.a l.d0 m) h1 (l.wall_lo m)
    (fun x hx1 hx2 => l.interior_none hx1 (by omega)) h2 (l.wall_hi m)
    (fun x hx1 hx2 => l.interior_none (by omega) hx2)

end Line

/-! ## Event tags along a line -/

/-- Event tags along a line (E1), (E2): `eR z` and `eL z` are the event tags on the edges after and
before the site `z` (`e^E`, `e^W` on rows; `e^N`, `e^S` on columns), `act z` says the site is
active. -/
structure EvLine (S : Type) extends Line S where
  /-- the event tag of the site `z` on its edge `(z, z + 1)` -/
  eR : ℤ → Option (Ev × Ev)
  /-- the event tag of the site `z` on its edge `(z - 1, z)` -/
  eL : ℤ → Option (Ev × Ev)
  /-- the site `z` is active -/
  act : ℤ → Prop
  /-- matching -/
  ev_match : ∀ z, eR z = eL (z + 1)
  /-- (E2) at a horizontal (vertical) site -/
  ev_copy : ∀ z, W z = none → o (z - 1) = (L, R) → ¬ act z → eL z = eR z
  /-- (E2) at an active site, first half -/
  ev_actL : ∀ z, act z → Ev.SecondIs (eL z) .cell
  /-- (E2) at an active site, second half -/
  ev_actR : ∀ z, act z → Ev.FirstIs (eR z) .cell
  /-- (E2) at a left (bottom) side -/
  ev_wallL : ∀ z, W z = some L → o z = (L, R) → Ev.FirstIs (eR z) .wall
  /-- (E2) at a right (top) side -/
  ev_wallR : ∀ z, W z = some R → o (z - 1) = (L, R) → Ev.SecondIs (eL z) .wall

namespace EvLine

variable {S : Type} (l : EvLine S)

theorem not_firstIs {e : Option (Ev × Ev)} (h : Ev.FirstIs e .cell) : ¬ Ev.FirstIs e .wall := by
  rintro ⟨b, rfl⟩; obtain ⟨b', h'⟩ := h; simp at h'

theorem not_secondIs {e : Option (Ev × Ev)} (h : Ev.SecondIs e .cell) :
    ¬ Ev.SecondIs e .wall := by
  rintro ⟨b, rfl⟩; obtain ⟨b', h'⟩ := h; simp at h'

/-- The proof of `bg:grids`(c), west to east: in a frame `[w, w']` of depth `own(y)` whose first
interior site is active, the first entry of the event tag on the edge `(x, x + 1)` is `wall` for
`x = w` and not for `w < x < w'`. -/
theorem first_wall {m : ℤ} (hact : l.act (frameLo l.a l.d0 m + 1)) :
    Ev.FirstIs (l.eR (frameLo l.a l.d0 m)) .wall ∧
      ∀ x, frameLo l.a l.d0 m < x → x < frameHi l.a l.d0 m → ¬ Ev.FirstIs (l.eR x) .wall := by
  set w := frameLo l.a l.d0 m
  set w' := frameHi l.a l.d0 m
  have hlh : w < w' := frameLo_lt_frameHi l.a l.d0 m
  refine ⟨l.ev_wallL w (l.wall_lo m) (l.o_frame le_rfl hlh), ?_⟩
  intro x hx1 hx2
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, x = w + 1 + k := ⟨(x - w - 1).toNat, by omega⟩
  induction k with
  | zero => simpa using not_firstIs (l.ev_actR _ hact)
  | succ k ih =>
    have hx : w + 1 + ((k + 1 : ℕ) : ℤ) = (w + 1 + k) + 1 := by push_cast; ring
    rw [hx]
    by_cases ha : l.act (w + 1 + k + 1)
    · exact not_firstIs (l.ev_actR _ ha)
    · have hW := l.interior_none (m := m) (z := w + 1 + k + 1) (by omega) (by rw [← hx]; exact hx2)
      have ho := l.o_frame (m := m) (z := w + 1 + k + 1 - 1) (by omega) (by omega)
      rw [← l.ev_copy _ hW ho ha, ← l.ev_match]
      exact ih (by omega) (by omega)

/-- The proof of `bg:grids`(c), east to west: in a frame `[w, w']` of depth `own(y)` whose last
interior site is active, the second entry of the event tag on the edge `(x - 1, x)` is `wall` for
`x = w'` and not for `w < x < w'`. -/
theorem second_wall {m : ℤ} (hact : l.act (frameHi l.a l.d0 m - 1)) :
    Ev.SecondIs (l.eL (frameHi l.a l.d0 m)) .wall ∧
      ∀ x, frameLo l.a l.d0 m < x → x < frameHi l.a l.d0 m → ¬ Ev.SecondIs (l.eL x) .wall := by
  set w := frameLo l.a l.d0 m
  set w' := frameHi l.a l.d0 m
  have hlh : w < w' := frameLo_lt_frameHi l.a l.d0 m
  refine ⟨l.ev_wallR w' (l.wall_hi m) (l.o_frame (m := m) (z := w' - 1) (by omega) (by omega)), ?_⟩
  intro x hx1 hx2
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, x = w' - 1 - k := ⟨(w' - 1 - x).toNat, by omega⟩
  induction k with
  | zero => simpa using not_secondIs (l.ev_actL _ hact)
  | succ k ih =>
    by_cases ha : l.act (w' - 1 - ((k + 1 : ℕ) : ℤ))
    · exact not_secondIs (l.ev_actL _ ha)
    · have hW := l.interior_none (m := m) (z := w' - 1 - ((k + 1 : ℕ) : ℤ)) hx1 (by omega)
      have ho := l.o_frame (m := m) (z := w' - 1 - ((k + 1 : ℕ) : ℤ) - 1) (by omega) (by omega)
      rw [l.ev_copy _ hW ho ha, l.ev_match]
      have hx : w' - 1 - ((k + 1 : ℕ) : ℤ) + 1 = w' - 1 - k := by push_cast; ring
      rw [hx]
      exact ih (by omega) (by omega)

end EvLine

end UPD.BG

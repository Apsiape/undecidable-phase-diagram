/-
# Section 5.4: the background is forced (`prop:background`(a), uniqueness, and (d))

New in this project. "We show that the rules force every background field of `ω`, compute the
result, …" Two legal configurations whose quarters have the same typical phase `τ` have the same
background (`background_unique`); with `prop:quarter-ti`(b) this is `prop:background`(d)
(`background_rigid`).

* Along a line: the tag `(L, R)` occurs exactly inside the frames of depth `own(y)`
  (`Line.lr_frame`, `Line.frame_of_LR`); in such a frame the event tags are determined by the
  active sites (`EvLine.ev_det`: the first entry is `cell` iff there is an active site between the
  left wall and the edge, the second iff there is one between the edge and the right wall);
  `corridor`: values copied across a corridor from a wall.
* `cellFormula U d i j`: the background components of `𝔨(i, j)` as functions of `d`
  (`cell_formula`, from `bg:grid` and (C1)–(C7)); `hcolFormula`, `vcolFormula`: the logical
  colours at the sites of a grid (`lE_grid`, `lN_grid`). This is the sentence of `bg:grid` "the
  background components of the cell records of `G`, and of the logical colours at the sites of
  `G` and of its channels, are determined by `d`".
* **`background_unique`**, **`background_rigid`**.
-/
import UndecidablePhaseDiagram.Background.Split
import UndecidablePhaseDiagram.Background.Markers

set_option autoImplicit false

namespace UPD.BG

open UPD.Scaffold

/-! ## Corridors -/

/-- Two configurations copying values across a corridor from the same value at a wall agree on
the corridor: `f z` is the value on the edge `(z, z + 1)` read from the west of `z + 1`, `g z` the
one read from `z`; at each site of the corridor either both copy (`g x = f x`) or the values are
known to agree. -/
theorem corridor {α : Type} {f g f' g' : ℤ → α} (hm : ∀ z, f z = g (z + 1))
    (hm' : ∀ z, f' z = g' (z + 1)) {w w' : ℤ} (h0 : f w = f' w)
    (hstep : ∀ x, w < x → x < w' → (g x = f x ∧ g' x = f' x) ∨ f x = f' x) :
    ∀ x, w ≤ x → x < w' → f x = f' x := by
  intro x hx1 hx2
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, x = w + k := ⟨(x - w).toNat, by omega⟩
  induction k with
  | zero => simpa using h0
  | succ k ih =>
    have e : w + ((k + 1 : ℕ) : ℤ) = (w + k) + 1 := by push_cast; ring
    rcases hstep (w + ((k + 1 : ℕ) : ℤ)) (by omega) hx2 with ⟨h1, h2⟩ | h
    · rw [← h1, ← h2, e, ← hm, ← hm']
      exact ih (by omega) (by omega)
    · exact h

namespace Line

variable {S : Type} (l : Line S)

/-- Consecutive walls `L` and `R` are the endpoints of a frame of depth `own(y)` (the core of
`carrier_iff`). -/
theorem lr_frame {wl wr : ℤ} (hlr : wl < wr) (hwl : l.W wl = some l.L) (hwr : l.W wr = some l.R)
    (hbetween : ∀ x, wl < x → x < wr → l.W x = none) :
    ∃ m, wl = frameLo l.a l.d0 m ∧ wr = frameHi l.a l.d0 m := by
  obtain ⟨e, he, ⟨m, hm⟩, hey⟩ := (l.wallL wl).1 hwl
  obtain ⟨e', he', ⟨m', hm'⟩, hey'⟩ := (l.wallR wr).1 hwr
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
  have hee : e = e' := by
    rcases lt_trichotomy e e' with hlt | heq | hlt
    · rcases frames_nested l.ha hlt m' m with (h | h) | h <;> omega
    · exact heq
    · rcases frames_nested l.ha hlt m m' with (h | h) | h <;> omega
  subst hee
  have hmm : m = m' := frame_window_unique (a := l.a) (z := wl) ⟨by omega, by omega⟩
    ⟨hB, by omega⟩
  subst hmm
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
  exact ⟨m, hm, hm'⟩

/-- The tag `(L, R)` occurs only on the edges of the frames of depth `own(y)`. -/
theorem frame_of_LR {z : ℤ} (ho : l.o z = (l.L, l.R)) :
    ∃ m, frameLo l.a l.d0 m ≤ z ∧ z < frameHi l.a l.d0 m := by
  obtain ⟨wl, ⟨hl1, hl2⟩, hlmax⟩ := Int.exists_greatest_of_bdd
    (P := fun x => x ≤ z ∧ l.W x ≠ none) ⟨z, fun x hx => hx.1⟩
    (by obtain ⟨w, hw, hw'⟩ := l.exists_wall_lt (z + 1); exact ⟨w, by omega, hw'⟩)
  obtain ⟨wr, ⟨hr1, hr2⟩, hrmin⟩ := Int.exists_least_of_bdd
    (P := fun x => z + 1 ≤ x ∧ l.W x ≠ none) ⟨z + 1, fun x hx => hx.1⟩
    (by obtain ⟨w, hw, hw'⟩ := l.exists_wall_gt z; exact ⟨w, by omega, hw'⟩)
  obtain ⟨sl, hsl⟩ := Option.ne_none_iff_exists'.1 hl2
  obtain ⟨sr, hsr⟩ := Option.ne_none_iff_exists'.1 hr2
  have hbetween : ∀ x, wl < x → x < wr → l.W x = none := by
    intro x h1 h2
    by_contra hx
    rcases le_or_gt x z with hxz | hxz
    · have := hlmax x ⟨hxz, hx⟩; omega
    · have := hrmin x ⟨by omega, hx⟩; omega
  have hrt := l.routing (z := z) hl1 hsl (fun x h1 h2 => hbetween x h1 (by omega)) (by omega) hsr
    (fun x h1 h2 => hbetween x (by omega) h2)
  rw [ho, Prod.mk.injEq] at hrt
  obtain ⟨rfl, rfl⟩ := hrt
  obtain ⟨m, rfl, rfl⟩ := l.lr_frame (by omega) hsl hsr hbetween
  exact ⟨m, hl1, by omega⟩

end Line

namespace EvLine

variable {S : Type} (l : EvLine S)

open Classical in
/-- The proof of `prop:background`(a), event tags: in a frame `[w, w']` of depth `own(y)` the event
tag on the edge `(x, x + 1)`, `w ≤ x < w'`, is `(e₋, e₊)` with `e₋ = cell` iff there is an active
site in `(w, x]` and `e₊ = cell` iff there is one in `[x + 1, w')`. -/
theorem ev_det (hE1 : ∀ x, l.o x = (l.L, l.R) → l.eR x ≠ none) {m : ℤ} :
    ∀ x, frameLo l.a l.d0 m ≤ x → x < frameHi l.a l.d0 m →
      l.eR x = some ((if ∃ z, frameLo l.a l.d0 m < z ∧ z ≤ x ∧ l.act z then .cell else .wall),
        (if ∃ z, x < z ∧ z < frameHi l.a l.d0 m ∧ l.act z then .cell else .wall)) := by
  set w := frameLo l.a l.d0 m
  set w' := frameHi l.a l.d0 m
  have hlh : w < w' := frameLo_lt_frameHi l.a l.d0 m
  have hpair : ∀ x, w ≤ x → x < w' → ∃ a b, l.eR x = some (a, b) := by
    intro x h1 h2
    obtain ⟨⟨a, b⟩, h⟩ := Option.ne_none_iff_exists'.1 (hE1 x (l.o_frame h1 h2))
    exact ⟨a, b, h⟩
  -- the copying rule inside the frame
  have hcopy : ∀ x, w < x → x < w' → ¬ l.act x → l.eR x = l.eR (x - 1) := by
    intro x h1 h2 hna
    have hW := l.interior_none (m := m) h1 h2
    have ho := l.o_frame (m := m) (z := x - 1) (by omega) (by omega)
    rw [← l.ev_copy x hW ho hna, ← sub_add_cancel x 1, ← l.ev_match]; simp
  -- first entries, from the west
  have hfirst : ∀ x, w ≤ x → x < w' → ∀ a b, l.eR x = some (a, b) →
      a = if ∃ z, w < z ∧ z ≤ x ∧ l.act z then .cell else .wall := by
    intro x hx1 hx2
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, x = w + k := ⟨(x - w).toNat, by omega⟩
    induction k with
    | zero =>
      intro a b h
      obtain ⟨b', hb'⟩ := l.ev_wallL w (l.wall_lo m) (l.o_frame le_rfl hlh)
      simp only [Nat.cast_zero, add_zero] at h ⊢
      rw [h] at hb'
      simp only [Option.some.injEq, Prod.mk.injEq] at hb'
      rw [hb'.1, if_neg]; rintro ⟨z, h1, h2, -⟩; omega
    | succ k ih =>
      intro a b h
      have e : w + ((k + 1 : ℕ) : ℤ) = (w + k) + 1 := by push_cast; ring
      by_cases ha : l.act (w + ((k + 1 : ℕ) : ℤ))
      · obtain ⟨b', hb'⟩ := l.ev_actR _ ha
        rw [h] at hb'
        simp only [Option.some.injEq, Prod.mk.injEq] at hb'
        rw [hb'.1, if_pos ⟨_, by omega, le_rfl, ha⟩]
      · rw [hcopy _ (by omega) hx2 ha, e, add_sub_cancel_right] at h
        rw [ih (by omega) (by omega) a b h]
        congr 1
        apply propext
        constructor
        · rintro ⟨z, h1, h2, h3⟩; exact ⟨z, h1, by omega, h3⟩
        · rintro ⟨z, h1, h2, h3⟩
          refine ⟨z, h1, ?_, h3⟩
          by_contra hz
          exact ha (by rw [show w + ((k + 1 : ℕ) : ℤ) = z by omega]; exact h3)
  -- second entries, from the east
  have hsecond : ∀ x, w ≤ x → x < w' → ∀ a b, l.eR x = some (a, b) →
      b = if ∃ z, x < z ∧ z < w' ∧ l.act z then .cell else .wall := by
    intro x hx1 hx2
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, x = w' - 1 - k := ⟨(w' - 1 - x).toNat, by omega⟩
    induction k with
    | zero =>
      intro a b h
      obtain ⟨a', ha'⟩ := l.ev_wallR w' (l.wall_hi m) (l.o_frame (m := m) (z := w' - 1)
        (by omega) (by omega))
      rw [show w' = w' - 1 + 1 by ring, ← l.ev_match] at ha'
      simp only [Nat.cast_zero, sub_zero] at h ⊢
      rw [h] at ha'
      simp only [Option.some.injEq, Prod.mk.injEq] at ha'
      rw [ha'.2, if_neg]; rintro ⟨z, h1, h2, -⟩; omega
    | succ k ih =>
      intro a b h
      set x := w' - 1 - ((k + 1 : ℕ) : ℤ)
      have e : x + 1 = w' - 1 - k := by simp only [x]; push_cast; ring
      have hk : w ≤ w' - 1 - (k : ℤ) := by omega
      obtain ⟨a', b', h'⟩ := hpair (w' - 1 - k) hk (by omega)
      have hb := ih hk (by omega) a' b' h'
      by_cases ha : l.act (x + 1)
      · obtain ⟨a'', ha''⟩ := l.ev_actL _ ha
        rw [← l.ev_match, h] at ha''
        simp only [Option.some.injEq, Prod.mk.injEq] at ha''
        rw [ha''.2, if_pos ⟨x + 1, by omega, by omega, ha⟩]
      · have hc := hcopy (x + 1) (by omega) (by omega) ha
        rw [add_sub_cancel_right, e, h'] at hc
        rw [h] at hc
        simp only [Option.some.injEq, Prod.mk.injEq] at hc
        rw [← hc.2, hb]
        congr 1
        apply propext
        rw [← e]
        constructor
        · rintro ⟨z, h1, h2, h3⟩; exact ⟨z, by omega, h2, h3⟩
        · rintro ⟨z, h1, h2, h3⟩
          refine ⟨z, ?_, h2, h3⟩
          by_contra hz
          exact ha (by rw [show x + 1 = z by omega]; exact h3)
  intro x hx1 hx2
  obtain ⟨a, b, h⟩ := hpair x hx1 hx2
  rw [h, hfirst x hx1 hx2 a b h, hsecond x hx1 hx2 a b h]

end EvLine

/-! ## The cell records and colours of a grid, explicitly -/

variable {U : Machine}

/-- `c_i(j)` for `j < N_d` (and `init(0, 0)` otherwise). -/
def runAt (U : Machine) (d i j : ℕ) : CellM U :=
  if h : j < MachineM.Nd d then MachineM.runM U d i ⟨j, h⟩ else initM U false false

theorem runAt_eq {d i j : ℕ} (h : j < MachineM.Nd d) :
    runAt U d i j = MachineM.runM U d i ⟨j, h⟩ := by
  rw [runAt, dif_pos h]

/-- **`bg:grid`**: the background components of `𝔨(i, j)`, as functions of `d` (`cell_formula`). -/
def cellFormula (U : Machine) (d i j : ℕ) : CellRecB U where
  ctIn := if i = 0 then false else Nat.testBit (i - 1) j
  ct := Nat.testBit i j
  cy := if i = 0 then false else carry (i - 1) 0 1 j
  ay := if i = MachineM.Nd d - 1 then carry (MachineM.Nd d - 1) 3 0 j else false
  sm := if i = MachineM.Nd d - 1 then decide (j = d + 2) else false
  hot := decide (j = d + 2)
  rdy := decide (MachineM.ready U d)
  gm := decide (MachineM.ready U d) && maskMinus U (runAt U d (MachineM.Nd d - 1) j)
  gp := decide (MachineM.ready U d) && maskPlus U (runAt U d (MachineM.Nd d - 1) j)
  rc := ⟨min j 80, by omega⟩
  tS := if j = 0 then none else some (runAt U d i (j - 1))
  tN := if j + 1 < MachineM.Nd d then some (runAt U d i (j + 1)) else none
  tC := runAt U d i j

/-- The east colour at `ξ(i, j)`, `i < N - 1`, as a function of `d`. -/
def hcolFormula (U : Machine) (d i j : ℕ) : HCol U :=
  ⟨(cellFormula U d i j).ct,
    fM U (cellFormula U d i j).tS (cellFormula U d i j).tC (cellFormula U d i j).tN,
    (cellFormula U d i j).hot, (cellFormula U d i j).rdy, (cellFormula U d i j).gm,
    (cellFormula U d i j).gp⟩

/-- The background of the north colour at `ξ(i, j)`, `j < N - 1`, as a function of `d`. -/
def vcolFormula (U : Machine) (d i j : ℕ) : VColB U :=
  ⟨(cellFormula U d i j).ctIn && (cellFormula U d i j).cy,
    (if i = MachineM.Nd d - 1 then SiteVal.maj (cellFormula U d i j).ct
      (decide ((cellFormula U d i j).rc.val ≤ 1)) (cellFormula U d i j).ay else false),
    (cellFormula U d i j).rc,
    (if i = MachineM.Nd d - 1 then (cellFormula U d i j).rdy else false),
    ((cellFormula U d i j).tC, runAt U d i (j + 1))⟩

namespace Setting

variable {ω : Config (SiteVal U)} {τ : ℕ → Bool × Bool} (hs : Setting ω τ)
variable {d : ℕ} (hd : 1 ≤ d) (m1 m2 : ℤ)
include hs hd

theorem grid_ctIn {i j : ℕ} (hi : i < MachineM.Nd d) (hj : j < MachineM.Nd d) :
    (cellAt ω τ d m1 m2 i j).ctIn = if i = 0 then false else Nat.testBit (i - 1) j := by
  rcases i with _ | i
  · obtain ⟨-, -, c1, -⟩ := hs.rules hd m1 m2 hi hj
    obtain ⟨fW, -, -, -⟩ := hs.grids_c hd m1 m2 hi hj
    simp [(c1.1 (by rw [fW]; rfl)).1]
  · obtain ⟨l, hl1, hl2⟩ := hs.chanH_some hd m1 m2 hi hj
    obtain ⟨-, -, c1, -⟩ := hs.rules hd m1 m2 hi hj
    obtain ⟨-, -, c1', -⟩ := hs.rules hd m1 m2 (show i < MachineM.Nd d by omega) hj
    obtain ⟨fW, -, -, -⟩ := hs.grids_c hd m1 m2 hi hj
    rw [(c1.2.1 (by rw [fW]; simp)).1 l hl2, c1'.2.2.1 l hl1,
      (hs.grid_a hd m1 m2 (by omega) hj).1]
    simp

/-- **`bg:grid`**, the sentence before (a): the background components of `𝔨(i, j)` are determined
by `d`. -/
theorem cell_formula {i j : ℕ} (hi : i < MachineM.Nd d) (hj : j < MachineM.Nd d) :
    (cellAt ω τ d m1 m2 i j).bg = cellFormula U d i j := by
  obtain ⟨-, -, -, -, c3, -⟩ := hs.rules hd m1 m2 hi hj
  obtain ⟨-, fE, -, -⟩ := hs.grids_c hd m1 m2 hi hj
  have hay : (cellAt ω τ d m1 m2 i j).ay =
      if i = MachineM.Nd d - 1 then carry (MachineM.Nd d - 1) 3 0 j else false := by
    split_ifs with h
    · subst h; exact hs.grid_ay hd m1 m2 hj
    · exact (c3.1 (by rw [fE]; simp [h])).1
  have hsm : (cellAt ω τ d m1 m2 i j).sm =
      if i = MachineM.Nd d - 1 then decide (j = d + 2) else false := by
    split_ifs with h
    · subst h; exact hs.grid_sm hd m1 m2 hj
    · exact (c3.1 (by rw [fE]; simp [h])).2.1
  have hgd := hs.grid_d hd m1 m2 hi hj
  have htS : (cellAt ω τ d m1 m2 i j).tS = if j = 0 then none else some (runAt U d i (j - 1)) := by
    rcases j with _ | j
    · simp [(hs.grid_tS_zero hd m1 m2 hi).1]
    · rw [(hs.grid_tS hd m1 m2 hi hj).1, hs.grid_c hd m1 m2 hi (by omega), runAt_eq (by omega)]
      simp
  have htN : (cellAt ω τ d m1 m2 i j).tN =
      if j + 1 < MachineM.Nd d then some (runAt U d i (j + 1)) else none := by
    split_ifs with h
    · rw [(hs.grid_tS hd m1 m2 hi h).2, hs.grid_c hd m1 m2 hi h, runAt_eq h]
    · have e : j = MachineM.Nd d - 1 := by omega
      subst e; exact (hs.grid_tS_zero hd m1 m2 hi).2
  simp only [CellRec.bg, cellFormula, CellRecB.mk.injEq]
  refine ⟨hs.grid_ctIn hd m1 m2 hi hj, (hs.grid_a hd m1 m2 hi hj).1, hs.grid_cy hd m1 m2 hi hj,
    hay, hsm, hs.grid_b hd m1 m2 hi hj, hgd.1, ?_, ?_, Fin.ext (hs.grid_a hd m1 m2 hi hj).2,
    htS, htN, ?_⟩
  · rw [hgd.2.1, runAt_eq hj]
  · rw [hgd.2.2, runAt_eq hj]
  · rw [hs.grid_c hd m1 m2 hi hj, runAt_eq hj]

/-- The east colour at `ξ(i, j)` is determined by `d` (`∘` in the last column). -/
theorem lE_grid {i j : ℕ} (hi : i < MachineM.Nd d) (hj : j < MachineM.Nd d) :
    (ω (gsite τ d m1 m2 i j)).lE =
      if i + 1 < MachineM.Nd d then some (hcolFormula U d i j) else none := by
  have hcf := hs.cell_formula hd m1 m2 hi hj
  obtain ⟨-, c0, c1, -, -, c4, c5, c6, c7, -⟩ := hs.rules hd m1 m2 hi hj
  obtain ⟨-, fE, -, -⟩ := hs.grids_c hd m1 m2 hi hj
  split_ifs with h
  · obtain ⟨l, hl1, -⟩ := hs.chanH_some hd m1 m2 h hj
    have hfE : (ω (gsite τ d m1 m2 i j)).fE = false := by rw [fE]; simp; omega
    have e1 := c1.2.2.1 l hl1
    have e2 := c5.2.2.2.2.2.2 l hl1
    have e3 := c4.2.1 hfE l hl1
    have e4 := (c6.2.1 hfE).1 l hl1
    have e5 := c7.2.1 hfE l hl1
    rw [hl1]
    simp only [hcolFormula, ← hcf]
    obtain ⟨ct, tb, hot, rdy, gm, gp⟩ := l
    simp only at e1 e2 e3 e4 e5
    simp only [CellRec.bg, Option.some.injEq, HCol.mk.injEq]
    exact ⟨e1, e2, e3.symm, e4.symm, e5.1.symm, e5.2.symm⟩
  · exact c0.2.1.2 (by rw [fE]; simp; omega)

/-- The background of the north colour at `ξ(i, j)` is determined by `d` (`∘` in the last row). -/
theorem lN_grid {i j : ℕ} (hi : i < MachineM.Nd d) (hj : j < MachineM.Nd d) :
    (ω (gsite τ d m1 m2 i j)).lN.map VCol.bg =
      if j + 1 < MachineM.Nd d then some (vcolFormula U d i j) else none := by
  have hcf := hs.cell_formula hd m1 m2 hi hj
  obtain ⟨-, c0, c1, c2, c3, -, c5, c6, -⟩ := hs.rules hd m1 m2 hi hj
  obtain ⟨-, fE, -, fN⟩ := hs.grids_c hd m1 m2 hi hj
  split_ifs with h
  · obtain ⟨l, hl1, -⟩ := hs.chanV_some hd m1 m2 hi h
    have hfN : (ω (gsite τ d m1 m2 i j)).fN = false := by rw [fN]; simp; omega
    have e1 := c1.2.2.2 l hl1
    have e2 := c2.2.2 l hl1
    obtain ⟨e3, e4⟩ := c5.2.2.2.1 hfN l hl1
    have htN : (cellAt ω τ d m1 m2 i j).tN = some (runAt U d i (j + 1)) := by
      have := congrArg CellRecB.tN hcf
      simp only [CellRec.bg, cellFormula, if_pos h] at this
      exact this
    rw [htN, Option.some.injEq] at e4
    have eay : l.ay = if i = MachineM.Nd d - 1 then SiteVal.maj (cellAt ω τ d m1 m2 i j).ct
        (decide ((cellAt ω τ d m1 m2 i j).rc.val ≤ 1)) (cellAt ω τ d m1 m2 i j).ay else false := by
      split_ifs with hi1
      · exact (c3.2 (by rw [fE, hi1]; simp)).2.2.2 l hl1
      · exact (c3.1 (by rw [fE]; simp [hi1])).2.2 l hl1
    have erdy : l.rdy = if i = MachineM.Nd d - 1 then (cellAt ω τ d m1 m2 i j).rdy else false := by
      split_ifs with hi1
      · exact (c6.1 (by rw [fE, hi1]; simp)).2.2 l hl1
      · exact (c6.2.1 (by rw [fE]; simp [hi1])).2 l hl1
    rw [hl1, Option.map_some]
    simp only [vcolFormula, ← hcf]
    obtain ⟨cy, ay, rc, rdy, ⟨tb1, tb2⟩, x⟩ := l
    simp only at e1 e2 e3 e4 eay erdy
    simp only [VCol.bg, CellRec.bg, Option.some.injEq, VColB.mk.injEq, Prod.mk.injEq]
    exact ⟨e1, eay, e2, erdy, e3, e4.symm⟩
  · rw [c0.2.2.2.2 (by rw [fN]; simp; omega)]; rfl

end Setting

/-! ## Uniqueness of the background -/

namespace Setting

section One

variable {ω : Config (SiteVal U)} {τ : ℕ → Bool × Bool} (hs : Setting ω τ)
include hs

/-- An active site is a site `ξ(i, j)` of a grid (`prop:routing`(c), `bg:def-grid`). -/
theorem active_grid {ξ : Plane} (h : (ω ξ).IsActive) : ∃ d m1 m2 i j, 1 ≤ d ∧
    i < MachineM.Nd d ∧ j < MachineM.Nd d ∧ ξ = gsite τ d m1 m2 i j := by
  obtain ⟨d, m1, m2, hd, h1, h2⟩ := (hs.routing_c ξ).1 h
  obtain ⟨i, j, hi, hj, e⟩ := (mem_grid_iff hd).1 ⟨h1, h2⟩
  exact ⟨d, m1, m2, i, j, hd, hi, hj, e⟩

/-- At an active site the cell record is `cellFormula`. -/
theorem k_grid {d : ℕ} (hd : 1 ≤ d) (m1 m2 : ℤ) {i j : ℕ} (hi : i < MachineM.Nd d)
    (hj : j < MachineM.Nd d) :
    (ω (gsite τ d m1 m2 i j)).k.map CellRec.bg = some (cellFormula U d i j) := by
  rw [(hs.rules hd m1 m2 hi hj).1, Option.map_some, hs.cell_formula hd m1 m2 hi hj]

end One

variable {ω ω' : Config (SiteVal U)} {τ : ℕ → Bool × Bool} (hs : Setting ω τ)
  (hs' : Setting ω' τ)
include hs hs'

/-- The quarters are the unique tiling `Y_τ` (`prop:quarter-ti`(a)). -/
theorem q_same (ξ : Plane) : (ω ξ).q = (ω' ξ).q := by
  obtain ⟨f, hf, hY, -⟩ := hs.phase
  obtain ⟨f', hf', hY', -⟩ := hs'.phase
  have e := (quarter_ti_a hs.typical.1).unique
    ⟨by rw [hY]; exact isQTiling_qshift hf _, hs.phase⟩
    ⟨by rw [hY']; exact isQTiling_qshift hf' _, hs'.phase⟩
  exact congrFun e ξ

theorem VW_same (ξ : Plane) : (ω ξ).q.VW = (ω' ξ).q.VW := by rw [hs.q_same hs' ξ]

theorem HW_same (ξ : Plane) : (ω ξ).q.HW = (ω' ξ).q.HW := by rw [hs.q_same hs' ξ]

theorem oE_same (ξ : Plane) : (ω ξ).oE = (ω' ξ).oE := by
  obtain ⟨wl, wr, sl, sr, h1, h2, h3, h4, h5, h6⟩ := hs.exists_walls_h ξ
  have hv : ∀ x, (ω' (x, ξ.2)).q.VW = (ω (x, ξ.2)).q.VW := fun x => (hs.VW_same hs' _).symm
  rw [(hs.routing_a h1 h2 h3 h4 h5 h6).1, (hs'.routing_a h1 (by rw [hv]; exact h2)
    (fun x a b => by rw [hv]; exact h3 x a b) h4 (by rw [hv]; exact h5)
    (fun x a b => by rw [hv]; exact h6 x a b)).1]

theorem oN_same (ξ : Plane) : (ω ξ).oN = (ω' ξ).oN := by
  obtain ⟨wl, wr, sl, sr, h1, h2, h3, h4, h5, h6⟩ := hs.exists_walls_v ξ
  have hv : ∀ x, (ω' (ξ.1, x)).q.HW = (ω (ξ.1, x)).q.HW := fun x => (hs.HW_same hs' _).symm
  rw [(hs.routing_a_v h1 h2 h3 h4 h5 h6).1, (hs'.routing_a_v h1 (by rw [hv]; exact h2)
    (fun x a b => by rw [hv]; exact h3 x a b) h4 (by rw [hv]; exact h5)
    (fun x a b => by rw [hv]; exact h6 x a b)).1]

theorem oW_same (ξ : Plane) : (ω ξ).oW = (ω' ξ).oW := by
  obtain ⟨z, y⟩ := ξ
  rw [hs.oW_eq, hs'.oW_eq, hs.oE_same hs']

theorem oS_same (ξ : Plane) : (ω ξ).oS = (ω' ξ).oS := by
  obtain ⟨x, z⟩ := ξ
  rw [hs.oS_eq, hs'.oS_eq, hs.oN_same hs']

theorem hcarrier_iff (ξ : Plane) : (ω ξ).IsHCarrier ↔ (ω' ξ).IsHCarrier := by
  rw [hs.routing_b_h, hs'.routing_b_h]

theorem vcarrier_iff (ξ : Plane) : (ω ξ).IsVCarrier ↔ (ω' ξ).IsVCarrier := by
  rw [hs.routing_b_v, hs'.routing_b_v]

theorem active_iff (ξ : Plane) : (ω ξ).IsActive ↔ (ω' ξ).IsActive := by
  rw [hs.routing_c, hs'.routing_c]

theorem eE_same (ξ : Plane) : (ω ξ).eE = (ω' ξ).eE := by
  obtain ⟨z, y⟩ := ξ
  by_cases hLR : (ω (z, y)).oE = (.L, .R)
  · have hLR' : (ω' (z, y)).oE = (.L, .R) := by rw [← hs.oE_same hs']; exact hLR
    set l := hs.hevline y
    set l' := hs'.hevline y
    obtain ⟨m, h1, h2⟩ := l.toLine.frame_of_LR hLR
    have hE1 : ∀ x, l.o x = (l.L, l.R) → l.eR x ≠ none := fun x hx hn =>
      ((hs.E1 (x, y)).2.1.1 hn) hx
    have hE1' : ∀ x, l'.o x = (l'.L, l'.R) → l'.eR x ≠ none := fun x hx hn =>
      ((hs'.E1 (x, y)).2.1.1 hn) hx
    have d1 := l.ev_det hE1 (m := m) z h1 h2
    have d2 := l'.ev_det hE1' (m := m) z h1 h2
    have hfun : l.act = l'.act := funext fun x => propext (hs.active_iff hs' (x, y))
    rw [hfun] at d1
    exact d1.trans d2.symm
  · have hLR' : ¬ (ω' (z, y)).oE = (.L, .R) := by rw [← hs.oE_same hs']; exact hLR
    rw [(hs.E1 (z, y)).2.1.2 hLR, (hs'.E1 (z, y)).2.1.2 hLR']

theorem eN_same (ξ : Plane) : (ω ξ).eN = (ω' ξ).eN := by
  obtain ⟨x, z⟩ := ξ
  by_cases hBT : (ω (x, z)).oN = (.B, .T)
  · set l := hs.vevline x
    set l' := hs'.vevline x
    obtain ⟨m, h1, h2⟩ := l.toLine.frame_of_LR hBT
    have hE1 : ∀ y, l.o y = (l.L, l.R) → l.eR y ≠ none := fun y hy hn =>
      ((hs.E1 (x, y)).2.2.2.1 hn) hy
    have hE1' : ∀ y, l'.o y = (l'.L, l'.R) → l'.eR y ≠ none := fun y hy hn =>
      ((hs'.E1 (x, y)).2.2.2.1 hn) hy
    have d1 := l.ev_det hE1 (m := m) z h1 h2
    have d2 := l'.ev_det hE1' (m := m) z h1 h2
    have hfun : l.act = l'.act := funext fun y => propext (hs.active_iff hs' (x, y))
    rw [hfun] at d1
    exact d1.trans d2.symm
  · have hBT' : ¬ (ω' (x, z)).oN = (.B, .T) := by rw [← hs.oN_same hs']; exact hBT
    rw [(hs.E1 (x, z)).2.2.2.2 hBT, (hs'.E1 (x, z)).2.2.2.2 hBT']

theorem eW_same (ξ : Plane) : (ω ξ).eW = (ω' ξ).eW := by
  obtain ⟨z, y⟩ := ξ
  have a := hs.eE_eq (z - 1) y
  have b := hs'.eE_eq (z - 1) y
  rw [sub_add_cancel] at a b
  rw [← a, ← b, hs.eE_same hs']

theorem eS_same (ξ : Plane) : (ω ξ).eS = (ω' ξ).eS := by
  obtain ⟨x, z⟩ := ξ
  have a := hs.eN_eq x (z - 1)
  have b := hs'.eN_eq x (z - 1)
  rw [sub_add_cancel] at a b
  rw [← a, ← b, hs.eN_same hs']

theorem lE_same (ξ : Plane) : (ω ξ).lE = (ω' ξ).lE := by
  obtain ⟨z, y⟩ := ξ
  by_cases hH : (ω (z, y)).IsHCarrier
  · obtain ⟨m, h1, h2⟩ := (hs.routing_b_h (z, y)).1 hH
    have hwall : ∀ {ω₀ : Config (SiteVal U)} (h₀ : Setting ω₀ τ),
        (ω₀ (frameLo (a1 τ) (hs.own2 y) m, y)).lE = none := by
      intro ω₀ h₀
      have hW : (ω₀ (frameLo (a1 τ) (hs.own2 y) m, y)).q.VW = some .L := (h₀.hline y).wall_lo m
      exact ((h₀.K1 _).1 fun hc => by rw [hc.1] at hW; simp at hW).2
    refine corridor (f := fun x => (ω (x, y)).lE) (g := fun x => (ω (x, y)).lW)
      (f' := fun x => (ω' (x, y)).lE) (g' := fun x => (ω' (x, y)).lW)
      (fun x => hs.lE_eq x y) (fun x => hs'.lE_eq x y)
      (by simp only; rw [hwall hs, hwall hs']) (fun x hx1 hx2 => ?_) z h1.le h2
    have hHx : (ω (x, y)).IsHCarrier := (hs.routing_b_h (x, y)).2 ⟨m, hx1, hx2⟩
    by_cases ha : (ω (x, y)).IsActive
    · right
      obtain ⟨d, m1, m2, i, j, hd, hi, hj, e⟩ := hs.active_grid ha
      rw [e, hs.lE_grid hd m1 m2 hi hj, hs'.lE_grid hd m1 m2 hi hj]
    · left
      have ha' : ¬ (ω' (x, y)).IsActive := by rwa [← hs.active_iff hs']
      have hHx' : (ω' (x, y)).IsHCarrier := (hs.hcarrier_iff hs' _).1 hHx
      exact ⟨(hs.K1 _).2 ⟨hHx, fun hV => ha ⟨hHx, hV⟩⟩, (hs'.K1 _).2 ⟨hHx', fun hV => ha' ⟨hHx', hV⟩⟩⟩
  · have hH' : ¬ (ω' (z, y)).IsHCarrier := by rwa [← hs.hcarrier_iff hs']
    rw [((hs.K1 _).1 hH).2, ((hs'.K1 _).1 hH').2]

theorem lW_same (ξ : Plane) : (ω ξ).lW = (ω' ξ).lW := by
  obtain ⟨z, y⟩ := ξ
  have a := hs.lE_eq (z - 1) y
  have b := hs'.lE_eq (z - 1) y
  rw [sub_add_cancel] at a b
  rw [← a, ← b, hs.lE_same hs']

theorem lN_same (ξ : Plane) : (ω ξ).lN.map VCol.bg = (ω' ξ).lN.map VCol.bg := by
  obtain ⟨x, z⟩ := ξ
  by_cases hV : (ω (x, z)).IsVCarrier
  · obtain ⟨m, h1, h2⟩ := (hs.routing_b_v (x, z)).1 hV
    have hwall : ∀ {ω₀ : Config (SiteVal U)} (h₀ : Setting ω₀ τ),
        (ω₀ (x, frameLo (a2 τ) (hs.own1 x) m)).lN = none := by
      intro ω₀ h₀
      have hW : (ω₀ (x, frameLo (a2 τ) (hs.own1 x) m)).q.HW = some .B := (h₀.vline x).wall_lo m
      exact ((h₀.K2 _).1 fun hc => by rw [hc.1] at hW; simp at hW).2
    refine corridor (f := fun y => (ω (x, y)).lN.map VCol.bg)
      (g := fun y => (ω (x, y)).lS.map VCol.bg)
      (f' := fun y => (ω' (x, y)).lN.map VCol.bg) (g' := fun y => (ω' (x, y)).lS.map VCol.bg)
      (fun y => by rw [hs.lN_eq x y]) (fun y => by rw [hs'.lN_eq x y])
      (by simp only; rw [hwall hs, hwall hs']) (fun y hy1 hy2 => ?_) z h1.le h2
    have hVy : (ω (x, y)).IsVCarrier := (hs.routing_b_v (x, y)).2 ⟨m, hy1, hy2⟩
    by_cases ha : (ω (x, y)).IsActive
    · right
      obtain ⟨d, m1, m2, i, j, hd, hi, hj, e⟩ := hs.active_grid ha
      rw [e, hs.lN_grid hd m1 m2 hi hj, hs'.lN_grid hd m1 m2 hi hj]
    · left
      have ha' : ¬ (ω' (x, y)).IsActive := by rwa [← hs.active_iff hs']
      have hVy' : (ω' (x, y)).IsVCarrier := (hs.vcarrier_iff hs' _).1 hVy
      rw [(hs.K2 _).2 ⟨hVy, fun hH => ha ⟨hH, hVy⟩⟩, (hs'.K2 _).2 ⟨hVy', fun hH => ha' ⟨hH, hVy'⟩⟩]
      exact ⟨rfl, rfl⟩
  · have hV' : ¬ (ω' (x, z)).IsVCarrier := by rwa [← hs.vcarrier_iff hs']
    rw [((hs.K2 _).1 hV).2, ((hs'.K2 _).1 hV').2]

theorem lS_same (ξ : Plane) : (ω ξ).lS.map VCol.bg = (ω' ξ).lS.map VCol.bg := by
  obtain ⟨x, z⟩ := ξ
  have a := hs.lN_eq x (z - 1)
  have b := hs'.lN_eq x (z - 1)
  rw [sub_add_cancel] at a b
  rw [← a, ← b, hs.lN_same hs']

theorem k_same (ξ : Plane) : (ω ξ).k.map CellRec.bg = (ω' ξ).k.map CellRec.bg := by
  by_cases ha : (ω ξ).IsActive
  · obtain ⟨d, m1, m2, i, j, hd, hi, hj, rfl⟩ := hs.active_grid ha
    rw [hs.k_grid hd m1 m2 hi hj, hs'.k_grid hd m1 m2 hi hj]
  · have ha' : ¬ (ω' ξ).IsActive := by rwa [← hs.active_iff hs']
    rw [(hs.K3 ξ).1 ha, (hs'.K3 ξ).1 ha']

theorem rowM_same (ξ : Plane) : (ω ξ).rowM = (ω' ξ).rowM :=
  Bool.eq_iff_iff.2 ((hs.markers_a_row ξ).trans (hs'.markers_a_row ξ).symm)

theorem colM_same (ξ : Plane) : (ω ξ).colM = (ω' ξ).colM :=
  Bool.eq_iff_iff.2 ((hs.markers_a_col ξ).trans (hs'.markers_a_col ξ).symm)

/-- **`prop:background`(a)**, uniqueness: two legal configurations whose quarters have the same
typical phase `τ` have the same background. -/
theorem background_unique : bgOf ω = bgOf ω' := by
  funext ξ
  simp only [bgOf, bgPart, BgVal.mk.injEq]
  exact ⟨hs.q_same hs' ξ, hs.oW_same hs' ξ, hs.oE_same hs' ξ, hs.oS_same hs' ξ,
    hs.oN_same hs' ξ, hs.eW_same hs' ξ, hs.eE_same hs' ξ, hs.eS_same hs' ξ, hs.eN_same hs' ξ,
    hs.lW_same hs' ξ, hs.lE_same hs' ξ, hs.lS_same hs' ξ, hs.lN_same hs' ξ, hs.k_same hs' ξ,
    hs.rowM_same hs' ξ, hs.colM_same hs' ξ⟩

end Setting

/-- The quarters of a legal configuration form a tiling of `𝔸^q` (matching of the quarter
colours). -/
theorem isQTiling_of_legal {ω : Config (SiteVal U)} (h : IsLegal (Phi U) ω) :
    IsQTiling (fun ξ => (ω ξ).q) :=
  ⟨fun u _ _ => by
      show (ω u).q.colE = (ω (u + (1, 0))).q.colW
      exact congrArg (fun c => c.1) (matchH_of_legal h u),
    fun u _ _ => by
      show (ω u).q.colN = (ω (u + (0, 1))).q.colS
      exact congrArg (fun c => c.1) (matchV_of_legal h u)⟩

/-- **`prop:background`(d)**: if `ω ∈ X_Φ` has typical quarter phase and `ω' ∈ X_Φ` agrees with
`ω` outside a finite set, then `ω'` has the same background as `ω`. -/
theorem background_rigid {ω : Config (SiteVal U)} {τ : ℕ → Bool × Bool} (hs : Setting ω τ)
    {ω' : Config (SiteVal U)} (h' : IsLegal (Phi U) ω') (D : Finset Plane)
    (hD : ∀ ξ, ξ ∉ D → ω' ξ = ω ξ) : bgOf ω' = bgOf ω := by
  have hq := quarter_rigid (isQTiling_of_legal h') hs.phase hs.typical.1 D
    (fun ξ hξ => by simp only [hD ξ hξ])
  have hs' : Setting ω' τ := ⟨h', by rw [hq]; exact hs.phase, hs.typical⟩
  exact hs'.background_unique hs

end UPD.BG

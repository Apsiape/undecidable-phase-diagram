/-
# Section 5.1: grids (`bg:def-grid`, `bg:grids`)

New in this project.

* The free coordinates `𝓕_d(m)` as a finite set (`freeSet`, `card_freeSet`: `N_d` elements by
  `scf:frames`(c)) and their increasing enumeration `ζ_0 < … < ζ_{N-1}` (`zeta`; `zeta_zero`:
  `ζ_0 = r_d(m)`, `zeta_last`: `ζ_{N-1}` is the right endpoint minus one).
* **`bg:def-grid`**: the grid `G_d(m₁, m₂)` (`grid`, the product of the free sets), its sites
  `ξ(i, j) = (ζ^{(1)}_i, ζ^{(2)}_j)` (`gsite`) and its root `𝐫_d(m₁, m₂) = ξ(0, 0)` (`root`);
  the label `n(d) = 1 + v₂(d)` is `MachineM.label` (`Background/Label.lean`).
* **`bg:grids`**: (a) `grids_a_h`, `grids_a_v`; (b) `grids_b`; (c) `flags` (position-free form:
  `f_W = [ξ₁ = r^{(1)}_d(m₁)]`, …) and `grids_c` (at logical positions); (d) `grids_d_exists`,
  `grid_unique`, `isRoot_iff`.
-/
import UndecidablePhaseDiagram.Background.Routing
import UndecidablePhaseDiagram.Background.Run

set_option autoImplicit false

namespace UPD.BG

open UPD.Scaffold

/-! ## Free coordinates as a finite set, and their enumeration -/

open Classical in
/-- `𝓕_d(m)`, the free coordinates of `I_d(m)`, as a finite set. -/
noncomputable def freeSet (a : ℕ → ℤ) (d : ℕ) (m : ℤ) : Finset ℤ :=
  (Finset.Ioo (frameLo a d m) (frameHi a d m)).filter (IsFree a d m)

theorem mem_freeSet {a : ℕ → ℤ} {d : ℕ} {m z : ℤ} : z ∈ freeSet a d m ↔ IsFree a d m z := by
  classical
  simp only [freeSet, Finset.mem_filter, Finset.mem_Ioo]
  exact ⟨fun h => h.2, fun h => ⟨⟨h.1, h.2.1⟩, h⟩⟩

/-- `scf:frames`(c): `|𝓕_d(m)| = N_d`. -/
theorem card_freeSet {a : ℕ → ℤ} (ha : FrameOffsets a) {d : ℕ} (hd : 1 ≤ d) (m : ℤ) :
    (freeSet a d m).card = MachineM.Nd d := by
  have h := card_free ha hd m
  have e : {z | IsFree a d m z} = ↑(freeSet a d m) := by
    ext z; simp [mem_freeSet]
  rw [e, Set.ncard_coe_finset] at h
  exact h

/-- `bg:def-grid`: the `i`-th free coordinate `ζ_i` of `I_d(m)` in increasing order (`0` for
`i ≥ N_d`). -/
noncomputable def zeta (a : ℕ → ℤ) (d : ℕ) (m : ℤ) (i : ℕ) : ℤ :=
  if h : i < (freeSet a d m).card then (freeSet a d m).orderEmbOfFin rfl ⟨i, h⟩ else 0

section Zeta

variable {a : ℕ → ℤ} (ha : FrameOffsets a) {d : ℕ} (hd : 1 ≤ d) (m : ℤ)
include ha hd

theorem zeta_eq {i : ℕ} (hi : i < MachineM.Nd d) :
    zeta a d m i = (freeSet a d m).orderEmbOfFin rfl ⟨i, by rw [card_freeSet ha hd]; exact hi⟩ := by
  have hc : i < (freeSet a d m).card := by rw [card_freeSet ha hd]; exact hi
  rw [zeta, dif_pos hc]

theorem zeta_free {i : ℕ} (hi : i < MachineM.Nd d) : IsFree a d m (zeta a d m i) := by
  rw [zeta_eq ha hd m hi, ← mem_freeSet]; exact Finset.orderEmbOfFin_mem _ _ _

theorem zeta_lt_iff {i i' : ℕ} (hi : i < MachineM.Nd d) (hi' : i' < MachineM.Nd d) :
    zeta a d m i < zeta a d m i' ↔ i < i' := by
  rw [zeta_eq ha hd m hi, zeta_eq ha hd m hi', OrderEmbedding.lt_iff_lt, Fin.mk_lt_mk]

theorem zeta_inj {i i' : ℕ} (hi : i < MachineM.Nd d) (hi' : i' < MachineM.Nd d) :
    zeta a d m i = zeta a d m i' ↔ i = i' := by
  rw [zeta_eq ha hd m hi, zeta_eq ha hd m hi', EmbeddingLike.apply_eq_iff_eq, Fin.mk.injEq]

theorem exists_zeta {z : ℤ} (hz : IsFree a d m z) : ∃ i, i < MachineM.Nd d ∧ zeta a d m i = z := by
  have hz' : z ∈ (freeSet a d m : Set ℤ) := mem_freeSet.2 hz
  rw [← Finset.range_orderEmbOfFin (freeSet a d m) rfl] at hz'
  obtain ⟨⟨i, hi⟩, rfl⟩ := hz'
  have hi' : i < MachineM.Nd d := by rwa [card_freeSet ha hd] at hi
  exact ⟨i, hi', by rw [zeta_eq ha hd m hi']⟩

/-- `scf:frames`(c): `ζ_0 = r_d(m)`, the least free coordinate. -/
theorem zeta_zero : zeta a d m 0 = rfree a d m := by
  have h0 : 0 < MachineM.Nd d := by have := MachineM.two_le_Nd d; omega
  have hc0 : 0 < (freeSet a d m).card := by rw [card_freeSet ha hd]; exact h0
  rw [zeta, dif_pos hc0, Finset.orderEmbOfFin_zero rfl hc0]
  apply le_antisymm
  · exact Finset.min'_le _ _ (mem_freeSet.2 (isFree_rfree ha hd m))
  · refine Finset.le_min' _ _ _ (fun z hz => ?_)
    have := (mem_freeSet.1 hz).1
    simp only [rfree]; omega

/-- `scf:frames`(c): `ζ_{N-1}` is the right endpoint minus one, the largest free coordinate. -/
theorem zeta_last : zeta a d m (MachineM.Nd d - 1) = frameHi a d m - 1 := by
  have h0 : 0 < MachineM.Nd d := by have := MachineM.two_le_Nd d; omega
  have hc : (freeSet a d m).card = MachineM.Nd d := card_freeSet ha hd m
  have hc0 : 0 < (freeSet a d m).card := by rw [hc]; exact h0
  have hi : MachineM.Nd d - 1 < (freeSet a d m).card := by omega
  rw [zeta, dif_pos hi]
  have e : (⟨MachineM.Nd d - 1, hi⟩ : Fin (freeSet a d m).card) =
      ⟨(freeSet a d m).card - 1, by omega⟩ := Fin.ext (by simp [hc])
  rw [e, Finset.orderEmbOfFin_last rfl hc0]
  apply le_antisymm
  · refine Finset.max'_le _ _ _ (fun z hz => ?_)
    have := (mem_freeSet.1 hz).2.1
    omega
  · exact Finset.le_max' _ _ (mem_freeSet.2 (isFree_frameHi_sub_one ha hd m))

/-- No free coordinate lies strictly between two consecutive ones. -/
theorem not_free_between {i : ℕ} (hi : i + 1 < MachineM.Nd d) {z : ℤ} (h1 : zeta a d m i < z)
    (h2 : z < zeta a d m (i + 1)) : ¬ IsFree a d m z := by
  intro hz
  obtain ⟨k, hk, rfl⟩ := exists_zeta ha hd m hz
  rw [zeta_lt_iff ha hd m (by omega) hk] at h1
  rw [zeta_lt_iff ha hd m hk hi] at h2
  omega

omit ha hd in
/-- A point of the interior of `I_d(m)` that is not free lies in a frame of smaller depth. -/
theorem exists_smaller {z : ℤ} (h1 : frameLo a d m < z) (h2 : z < frameHi a d m)
    (hz : ¬ IsFree a d m z) : ∃ e, 1 ≤ e ∧ e < d ∧ InFrame a e z := by
  by_contra hc
  push Not at hc
  exact hz ⟨h1, h2, fun e he hed => hc e he hed⟩

end Zeta

/-! ## `bg:def-grid` -/

variable {U : Machine}

/-- **`bg:def-grid`**: the site `ξ(i, j) = (ζ^{(1)}_i, ζ^{(2)}_j)` of the grid `G_d(m₁, m₂)`,
at the logical position `(i, j)`. -/
noncomputable def gsite (τ : ℕ → Bool × Bool) (d : ℕ) (m1 m2 : ℤ) (i j : ℕ) : Plane :=
  (zeta (a1 τ) d m1 i, zeta (a2 τ) d m2 j)

/-- **`bg:def-grid`**: the grid `G_d(m₁, m₂)`, the set of its sites, which is
`𝓕^{(1)}_d(m₁) × 𝓕^{(2)}_d(m₂)` (`mem_grid_iff`). -/
def grid (τ : ℕ → Bool × Bool) (d : ℕ) (m1 m2 : ℤ) : Set Plane :=
  {ξ | IsFree (a1 τ) d m1 ξ.1 ∧ IsFree (a2 τ) d m2 ξ.2}

/-- **`bg:def-grid`**: the root `𝐫_d(m₁, m₂) = ξ(0, 0) = (r^{(1)}_d(m₁), r^{(2)}_d(m₂))`. -/
def root (τ : ℕ → Bool × Bool) (d : ℕ) (m1 m2 : ℤ) : Plane :=
  (rfree (a1 τ) d m1, rfree (a2 τ) d m2)

theorem mem_grid_iff {τ : ℕ → Bool × Bool} {d : ℕ} (hd : 1 ≤ d) {m1 m2 : ℤ} {ξ : Plane} :
    ξ ∈ grid τ d m1 m2 ↔ ∃ i j, i < MachineM.Nd d ∧ j < MachineM.Nd d ∧ ξ = gsite τ d m1 m2 i j := by
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨i, hi, e1⟩ := exists_zeta (frameOffsets_phase _) hd m1 h1
    obtain ⟨j, hj, e2⟩ := exists_zeta (frameOffsets_phase _) hd m2 h2
    exact ⟨i, j, hi, hj, by rw [gsite, e1, e2]⟩
  · rintro ⟨i, j, hi, hj, rfl⟩
    exact ⟨zeta_free (frameOffsets_phase _) hd m1 hi, zeta_free (frameOffsets_phase _) hd m2 hj⟩

theorem gsite_zero {τ : ℕ → Bool × Bool} {d : ℕ} (hd : 1 ≤ d) (m1 m2 : ℤ) :
    gsite τ d m1 m2 0 0 = root τ d m1 m2 := by
  simp only [gsite, root, zeta_zero (frameOffsets_phase _) hd]

/-! ## Event tags and boundary flags -/

namespace SiteValFlags

theorem fW_iff (s : SiteVal U) : s.fW = true ↔ Ev.FirstIs s.eW .wall := by
  unfold SiteVal.fW Ev.FirstIs
  rcases s.eW with _ | ⟨a, b⟩ <;> simp

theorem fE_iff (s : SiteVal U) : s.fE = true ↔ Ev.SecondIs s.eE .wall := by
  unfold SiteVal.fE Ev.SecondIs
  rcases s.eE with _ | ⟨a, b⟩ <;> simp

theorem fS_iff (s : SiteVal U) : s.fS = true ↔ Ev.FirstIs s.eS .wall := by
  unfold SiteVal.fS Ev.FirstIs
  rcases s.eS with _ | ⟨a, b⟩ <;> simp

theorem fN_iff (s : SiteVal U) : s.fN = true ↔ Ev.SecondIs s.eN .wall := by
  unfold SiteVal.fN Ev.SecondIs
  rcases s.eN with _ | ⟨a, b⟩ <;> simp

end SiteValFlags

open SiteValFlags

namespace Setting

variable {ω : Config (SiteVal U)} {τ : ℕ → Bool × Bool} (hs : Setting ω τ)
include hs

/-- The root of a grid is active (by `prop:routing`(c)). -/
theorem active_of_free {d : ℕ} (hd : 1 ≤ d) {m1 m2 : ℤ} {ξ : Plane}
    (h1 : IsFree (a1 τ) d m1 ξ.1) (h2 : IsFree (a2 τ) d m2 ξ.2) : (ω ξ).IsActive :=
  (hs.routing_c ξ).2 ⟨d, m1, m2, hd, h1, h2⟩

/-- **`bg:grids`(a)** (rows): the sites strictly between `ξ(i, j)` and `ξ(i + 1, j)` are
horizontal. -/
theorem grids_a_h {d : ℕ} (hd : 1 ≤ d) (m1 m2 : ℤ) {i j : ℕ} (hi : i + 1 < MachineM.Nd d)
    (hj : j < MachineM.Nd d) {z : ℤ} (h1 : zeta (a1 τ) d m1 i < z)
    (h2 : z < zeta (a1 τ) d m1 (i + 1)) : (ω (z, zeta (a2 τ) d m2 j)).IsHorizontal := by
  have ha1 : FrameOffsets (a1 τ) := frameOffsets_phase _
  have ha2 : FrameOffsets (a2 τ) := frameOffsets_phase _
  set y := zeta (a2 τ) d m2 j
  have hy : IsFree (a2 τ) d m2 y := zeta_free ha2 hd m2 hj
  have hown : hs.own2 y = d := own_eq_of_isFree hd hy
  have hzi := zeta_free ha1 hd m1 (show i < MachineM.Nd d by omega)
  have hzi' := zeta_free ha1 hd m1 hi
  have hlo : frameLo (a1 τ) d m1 < z := by have := hzi.1; omega
  have hhi : z < frameHi (a1 τ) d m1 := by have := hzi'.2.1; omega
  refine ⟨(hs.routing_b_h (z, y)).2 ⟨m1, by rw [hown]; exact hlo, by rw [hown]; exact hhi⟩, ?_⟩
  intro hV
  obtain ⟨e, he, hed, hin⟩ := exists_smaller m1 hlo hhi (not_free_between ha1 hd m1 hi h1 h2)
  have hle : hs.own1 z ≤ e := own_le _ _ he hin
  obtain ⟨m, hm1, hm2⟩ := (hs.routing_b_v (z, y)).1 hV
  exact hy.2.2 (hs.own1 z) (own_spec (a1 τ) hs.typical.inFrame_col z).1 (by omega)
    ⟨m, hm1.le, hm2.le⟩

/-- **`bg:grids`(a)** (columns): the sites strictly between `ξ(i, j)` and `ξ(i, j + 1)` are
vertical. -/
theorem grids_a_v {d : ℕ} (hd : 1 ≤ d) (m1 m2 : ℤ) {i j : ℕ} (hi : i < MachineM.Nd d)
    (hj : j + 1 < MachineM.Nd d) {z : ℤ} (h1 : zeta (a2 τ) d m2 j < z)
    (h2 : z < zeta (a2 τ) d m2 (j + 1)) : (ω (zeta (a1 τ) d m1 i, z)).IsVertical := by
  have ha1 : FrameOffsets (a1 τ) := frameOffsets_phase _
  have ha2 : FrameOffsets (a2 τ) := frameOffsets_phase _
  set x := zeta (a1 τ) d m1 i
  have hx : IsFree (a1 τ) d m1 x := zeta_free ha1 hd m1 hi
  have hown : hs.own1 x = d := own_eq_of_isFree hd hx
  have hzj := zeta_free ha2 hd m2 (show j < MachineM.Nd d by omega)
  have hzj' := zeta_free ha2 hd m2 hj
  have hlo : frameLo (a2 τ) d m2 < z := by have := hzj.1; omega
  have hhi : z < frameHi (a2 τ) d m2 := by have := hzj'.2.1; omega
  refine ⟨(hs.routing_b_v (x, z)).2 ⟨m2, by rw [hown]; exact hlo, by rw [hown]; exact hhi⟩, ?_⟩
  intro hH
  obtain ⟨e, he, hed, hin⟩ := exists_smaller m2 hlo hhi (not_free_between ha2 hd m2 hj h1 h2)
  have hle : hs.own2 z ≤ e := own_le _ _ he hin
  obtain ⟨m, hm1, hm2⟩ := (hs.routing_b_h (x, z)).1 hH
  exact hx.2.2 (hs.own2 z) (own_spec (a2 τ) hs.typical.inFrame_row z).1 (by omega)
    ⟨m, hm1.le, hm2.le⟩

/-- **`bg:grids`(b)**: `ξ(0, j) - e₁` and `ξ(N-1, j) + e₁` lie on light vertical walls, as a left
and a right side; `ξ(i, 0) - e₂` and `ξ(i, N-1) + e₂` lie on light horizontal walls, as a bottom
and a top side. -/
theorem grids_b {d : ℕ} (hd : 1 ≤ d) (m1 m2 : ℤ) {i j : ℕ} (hi : i < MachineM.Nd d)
    (hj : j < MachineM.Nd d) :
    (ω (zeta (a1 τ) d m1 0 - 1, zeta (a2 τ) d m2 j)).q.VW = some .L ∧
    (ω (zeta (a1 τ) d m1 (MachineM.Nd d - 1) + 1, zeta (a2 τ) d m2 j)).q.VW = some .R ∧
    (ω (zeta (a1 τ) d m1 i, zeta (a2 τ) d m2 0 - 1)).q.HW = some .B ∧
    (ω (zeta (a1 τ) d m1 i, zeta (a2 τ) d m2 (MachineM.Nd d - 1) + 1)).q.HW = some .T := by
  have ha1 : FrameOffsets (a1 τ) := frameOffsets_phase _
  have ha2 : FrameOffsets (a2 τ) := frameOffsets_phase _
  have hy := zeta_free ha2 hd m2 hj
  have hx := zeta_free ha1 hd m1 hi
  have iy : InFrame (a2 τ) d (zeta (a2 τ) d m2 j) := ⟨m2, hy.1.le, hy.2.1.le⟩
  have ix : InFrame (a1 τ) d (zeta (a1 τ) d m1 i) := ⟨m1, hx.1.le, hx.2.1.le⟩
  rw [zeta_zero ha1 hd, zeta_last ha1 hd, zeta_zero ha2 hd, zeta_last ha2 hd]
  refine ⟨(hs.VW_L _ _).2 ⟨d, hd, ⟨m1, by simp [rfree]⟩, iy⟩,
    (hs.VW_R _ _).2 ⟨d, hd, ⟨m1, by ring⟩, iy⟩,
    (hs.HW_B _ _).2 ⟨d, hd, ⟨m2, by simp [rfree]⟩, ix⟩,
    (hs.HW_T _ _).2 ⟨d, hd, ⟨m2, by ring⟩, ix⟩⟩

/-- **`bg:grids`(c)**, position-free form: at a site of `G_d(m₁, m₂)`,
`f_W = [ξ₁ = r^{(1)}_d(m₁)]`, `f_E = [ξ₁ = ` right endpoint `- 1]`, `f_S = [ξ₂ = r^{(2)}_d(m₂)]`
and `f_N = [ξ₂ = ` right endpoint `- 1]`. -/
theorem flags {d : ℕ} (hd : 1 ≤ d) {m1 m2 : ℤ} {ξ : Plane} (h1 : IsFree (a1 τ) d m1 ξ.1)
    (h2 : IsFree (a2 τ) d m2 ξ.2) :
    (ω ξ).fW = decide (ξ.1 = rfree (a1 τ) d m1) ∧
    (ω ξ).fE = decide (ξ.1 = frameHi (a1 τ) d m1 - 1) ∧
    (ω ξ).fS = decide (ξ.2 = rfree (a2 τ) d m2) ∧
    (ω ξ).fN = decide (ξ.2 = frameHi (a2 τ) d m2 - 1) := by
  have ha1 : FrameOffsets (a1 τ) := frameOffsets_phase _
  have ha2 : FrameOffsets (a2 τ) := frameOffsets_phase _
  obtain ⟨x, y⟩ := ξ
  simp only at h1 h2 ⊢
  -- the row `y`
  have hd0h : (hs.hevline y).toLine.d0 = d := own_eq_of_isFree hd h2
  have hd0v : (hs.vevline x).toLine.d0 = d := own_eq_of_isFree hd h1
  have actH : ∀ z, IsFree (a1 τ) d m1 z → (hs.hevline y).act z := fun z hz =>
    hs.active_of_free (ξ := (z, y)) hd hz h2
  have actV : ∀ z, IsFree (a2 τ) d m2 z → (hs.vevline x).act z := fun z hz =>
    hs.active_of_free (ξ := (x, z)) hd h1 hz
  obtain ⟨fw1, fw2⟩ := (hs.hevline y).first_wall (m := m1)
    (by rw [hd0h]; exact actH _ (isFree_rfree ha1 hd m1))
  obtain ⟨fe1, fe2⟩ := (hs.hevline y).second_wall (m := m1)
    (by rw [hd0h]; exact actH _ (isFree_frameHi_sub_one ha1 hd m1))
  obtain ⟨fs1, fs2⟩ := (hs.vevline x).first_wall (m := m2)
    (by rw [hd0v]; exact actV _ (isFree_rfree ha2 hd m2))
  obtain ⟨fn1, fn2⟩ := (hs.vevline x).second_wall (m := m2)
    (by rw [hd0v]; exact actV _ (isFree_frameHi_sub_one ha2 hd m2))
  rw [hd0h] at fw1 fw2 fe1 fe2
  rw [hd0v] at fs1 fs2 fn1 fn2
  change Ev.FirstIs (ω (frameLo (a1 τ) d m1, y)).eE .wall at fw1
  change ∀ z, frameLo (a1 τ) d m1 < z → z < frameHi (a1 τ) d m1 →
    ¬ Ev.FirstIs (ω (z, y)).eE .wall at fw2
  change Ev.SecondIs (ω (frameHi (a1 τ) d m1, y)).eW .wall at fe1
  change ∀ z, frameLo (a1 τ) d m1 < z → z < frameHi (a1 τ) d m1 →
    ¬ Ev.SecondIs (ω (z, y)).eW .wall at fe2
  change Ev.FirstIs (ω (x, frameLo (a2 τ) d m2)).eN .wall at fs1
  change ∀ z, frameLo (a2 τ) d m2 < z → z < frameHi (a2 τ) d m2 →
    ¬ Ev.FirstIs (ω (x, z)).eN .wall at fs2
  change Ev.SecondIs (ω (x, frameHi (a2 τ) d m2)).eS .wall at fn1
  change ∀ z, frameLo (a2 τ) d m2 < z → z < frameHi (a2 τ) d m2 →
    ¬ Ev.SecondIs (ω (x, z)).eS .wall at fn2
  obtain ⟨hx1, hx2, -⟩ := h1
  obtain ⟨hy1, hy2, -⟩ := h2
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- `f_W`: the event tag west of `(x, y)` is the one east of `(x - 1, y)`
    have e : (ω (x, y)).eW = (ω (x - 1, y)).eE := by rw [hs.eE_eq, sub_add_cancel]
    rw [Bool.eq_iff_iff, fW_iff, e, decide_eq_true_iff]
    by_cases hx : x = rfree (a1 τ) d m1
    · rw [hx]; simp only [rfree, add_sub_cancel_right, iff_true]; exact fw1
    · simp only [hx, iff_false]
      exact fw2 _ (by simp only [rfree] at hx; omega) (by omega)
  · -- `f_E`: the event tag east of `(x, y)` is the one west of `(x + 1, y)`
    rw [Bool.eq_iff_iff, fE_iff, hs.eE_eq, decide_eq_true_iff]
    by_cases hx : x = frameHi (a1 τ) d m1 - 1
    · rw [hx, sub_add_cancel]; simp only [iff_true]; exact fe1
    · simp only [hx, iff_false]
      exact fe2 _ (by omega) (by omega)
  · have e : (ω (x, y)).eS = (ω (x, y - 1)).eN := by rw [hs.eN_eq, sub_add_cancel]
    rw [Bool.eq_iff_iff, fS_iff, e, decide_eq_true_iff]
    by_cases hy : y = rfree (a2 τ) d m2
    · rw [hy]; simp only [rfree, add_sub_cancel_right, iff_true]; exact fs1
    · simp only [hy, iff_false]
      exact fs2 _ (by simp only [rfree] at hy; omega) (by omega)
  · rw [Bool.eq_iff_iff, fN_iff, hs.eN_eq, decide_eq_true_iff]
    by_cases hy : y = frameHi (a2 τ) d m2 - 1
    · rw [hy, sub_add_cancel]; simp only [iff_true]; exact fn1
    · simp only [hy, iff_false]
      exact fn2 _ (by omega) (by omega)

/-- **`bg:grids`(c)**: the boundary flags at `ξ(i, j)` are `f_W = [i = 0]`, `f_E = [i = N-1]`,
`f_S = [j = 0]` and `f_N = [j = N-1]`. -/
theorem grids_c {d : ℕ} (hd : 1 ≤ d) (m1 m2 : ℤ) {i j : ℕ} (hi : i < MachineM.Nd d)
    (hj : j < MachineM.Nd d) :
    (ω (gsite τ d m1 m2 i j)).fW = decide (i = 0) ∧
    (ω (gsite τ d m1 m2 i j)).fE = decide (i = MachineM.Nd d - 1) ∧
    (ω (gsite τ d m1 m2 i j)).fS = decide (j = 0) ∧
    (ω (gsite τ d m1 m2 i j)).fN = decide (j = MachineM.Nd d - 1) := by
  have ha1 : FrameOffsets (a1 τ) := frameOffsets_phase _
  have ha2 : FrameOffsets (a2 τ) := frameOffsets_phase _
  have h0 : 0 < MachineM.Nd d := by have := MachineM.two_le_Nd d; omega
  obtain ⟨f1, f2, f3, f4⟩ := hs.flags hd (ξ := gsite τ d m1 m2 i j) (zeta_free ha1 hd m1 hi)
    (zeta_free ha2 hd m2 hj)
  simp only [gsite] at f1 f2 f3 f4 ⊢
  rw [f1, f2, f3, f4, ← zeta_zero ha1 hd m1, ← zeta_last ha1 hd m1, ← zeta_zero ha2 hd m2,
    ← zeta_last ha2 hd m2]
  exact ⟨decide_eq_decide.2 (zeta_inj ha1 hd m1 hi h0),
    decide_eq_decide.2 (zeta_inj ha1 hd m1 hi (by omega)),
    decide_eq_decide.2 (zeta_inj ha2 hd m2 hj h0),
    decide_eq_decide.2 (zeta_inj ha2 hd m2 hj (by omega))⟩

/-- **`bg:grids`(d)**, first claim (existence): every active site lies in a grid. -/
theorem grids_d_exists {ξ : Plane} (h : (ω ξ).IsActive) :
    ∃ d m1 m2, 1 ≤ d ∧ ξ ∈ grid τ d m1 m2 := by
  obtain ⟨d, m1, m2, hd, h1, h2⟩ := (hs.routing_c ξ).1 h
  exact ⟨d, m1, m2, hd, h1, h2⟩

omit hs in
/-- **`bg:grids`(d)**, first claim (uniqueness): the grids are pairwise disjoint (the sets
`𝓕^{(i)}_d(m)` are pairwise disjoint for different `(d, m)`, `scf:frames`(a)). -/
theorem grid_unique {d d' : ℕ} (hd : 1 ≤ d) (hd' : 1 ≤ d') {m1 m2 m1' m2' : ℤ} {ξ : Plane}
    (h : ξ ∈ grid τ d m1 m2) (h' : ξ ∈ grid τ d' m1' m2') : d = d' ∧ m1 = m1' ∧ m2 = m2' := by
  obtain ⟨h1, h2⟩ := h
  obtain ⟨h1', h2'⟩ := h'
  have e : d = d' := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact h1'.2.2 d hd hlt ⟨m1, h1.1.le, h1.2.1.le⟩
    · exact h1.2.2 d' hd' hlt ⟨m1', h1'.1.le, h1'.2.1.le⟩
  subst e
  exact ⟨rfl, frame_window_unique ⟨h1.1.le, h1.2.1.le⟩ ⟨h1'.1.le, h1'.2.1.le⟩,
    frame_window_unique ⟨h2.1.le, h2.2.1.le⟩ ⟨h2'.1.le, h2'.2.1.le⟩⟩

/-- **`bg:grids`(d)**, second claim: the roots of `ω` are exactly the roots of the grids. -/
theorem isRoot_iff (ξ : Plane) :
    (ω ξ).IsRoot ↔ ∃ d m1 m2, 1 ≤ d ∧ ξ = root τ d m1 m2 := by
  have ha1 : FrameOffsets (a1 τ) := frameOffsets_phase _
  have ha2 : FrameOffsets (a2 τ) := frameOffsets_phase _
  constructor
  · rintro ⟨hact, hW, hS⟩
    obtain ⟨d, m1, m2, hd, h1, h2⟩ := (hs.routing_c ξ).1 hact
    obtain ⟨f1, -, f3, -⟩ := hs.flags hd h1 h2
    rw [hW, eq_comm, decide_eq_true_iff] at f1
    rw [hS, eq_comm, decide_eq_true_iff] at f3
    exact ⟨d, m1, m2, hd, Prod.ext f1 f3⟩
  · rintro ⟨d, m1, m2, hd, rfl⟩
    have h1 := isFree_rfree ha1 hd m1
    have h2 := isFree_rfree ha2 hd m2
    obtain ⟨f1, -, f3, -⟩ := hs.flags (ξ := root τ d m1 m2) hd h1 h2
    exact ⟨hs.active_of_free hd h1 h2, by rw [f1]; simp [root], by rw [f3]; simp [root]⟩

/-- **`bg:grids`(d)**: an active site is a root exactly when its logical position is `(0, 0)`. -/
theorem isRoot_gsite_iff {d : ℕ} (hd : 1 ≤ d) (m1 m2 : ℤ) {i j : ℕ} (hi : i < MachineM.Nd d)
    (hj : j < MachineM.Nd d) : (ω (gsite τ d m1 m2 i j)).IsRoot ↔ i = 0 ∧ j = 0 := by
  obtain ⟨f1, -, f3, -⟩ := hs.grids_c hd m1 m2 hi hj
  have hact := hs.active_of_free (ξ := gsite τ d m1 m2 i j) hd
    (zeta_free (frameOffsets_phase _) hd m1 hi) (zeta_free (frameOffsets_phase _) hd m2 hj)
  simp only [SiteVal.IsRoot, hact, f1, f3, decide_eq_true_iff, true_and]

end Setting

end UPD.BG

/-
# Section 6: edges and their private coordinates

New in this project (session 10). The edges of Section 6 ("Edges and their private
coordinates") for the background `𝔟_τ`, and their private coordinates, as data for `pay:elim`
(`Gibbs/Elim.lean`, P-36: the fixed coordinates of `pay:factor`(a) are the private coordinates of
one "site edge" per site, whose tail and head are that site).

* `REdge = ℕ × ℤ × ℤ × Bool`: `(k, m₁, m₂, v)` is the horizontal (`v = false`) or vertical
  (`v = true`) edge of depth `d = k + 1` with head `𝐫_d(m₁, m₂)` and tail `𝐫_d(m₁ - 1, m₂)`
  (resp. `𝐫_d(m₁, m₂ - 1)`); `Ed = Plane ⊕ REdge` adds the site edges.
* `armPred r q`, `sensPred U τ r q`: the coordinate `q` lies in the arm (the wire values
  `w^E(z, v₂)`, `u₁ ≤ z < v₁`, and `w^W(z, v₂)`, `u₁ < z ≤ v₁`; vertically `w^N`, `w^S`) or, for a
  ready depth, in the sensor of `r` (the components `x_ι`, `y_ι` of the cell records at `ξ(0, j)`,
  `j < N`, and `x_ι` of `ℓ^S`, `ℓ^N` on the first column where these colours are present, for the
  two components `ι` of the edge: `ι ∈ {0, 1}` horizontal, `{2, 3}` vertical). **[flag 3]** the
  paper lists the `x` components of `ℓ^S`, `ℓ^N` "at the sites of the column of `v` from `ξ(0, 0)`
  to `ξ(0, N-1)`"; `ℓ^S` at `ξ(0, 0)` and `ℓ^N` at `ξ(0, N - 1)` are `∘` in `𝔟_τ` (`lS_gsite`,
  `lN_gsite`), so the sensor here has `ℓ^S_x` on `(ζ₀, ζ_{N-1}]` and `ℓ^N_x` on `[ζ₀, ζ_{N-1})`.
* `privPred_unique` (**`pay:factor`(a)**, disjointness): a coordinate lies in the private
  coordinates of at most one edge; no spin coordinate lies in any.
* `owner`: the edge of a non-spin coordinate (its real edge, or the site edge of its site);
  `Q e` the private coordinates of `e` (finite), `relabel : Coord ≃ Plane ⊕ Σ e, Q e`.
* `edgesAt`, `mem_edgesAt`.
-/
import UndecidablePhaseDiagram.Payload.Legal
import UndecidablePhaseDiagram.Payload.Graph
import UndecidablePhaseDiagram.Gibbs.Elim
import UndecidablePhaseDiagram.Payload.Sensor

set_option autoImplicit false

noncomputable section

namespace UPD.BG

open UPD.Scaffold

/-! ## Edges -/

/-- A real edge `(k, m₁, m₂, v)`: depth `k + 1`, head `𝐫_{k+1}(m₁, m₂)`, vertical iff `v`. -/
abbrev REdge := ℕ × ℤ × ℤ × Bool

/-- The edges: one site edge per site, and the real edges. -/
abbrev Ed := Plane ⊕ REdge

variable (τ : ℕ → Bool × Bool)

/-- The head `v = 𝐫_d(m₁, m₂)` of a real edge. -/
def rhead (r : REdge) : Plane := root τ (r.1 + 1) r.2.1 r.2.2.1

/-- The tail `u = 𝐫_d(m₁ - 1, m₂)` (horizontal) or `𝐫_d(m₁, m₂ - 1)` (vertical). -/
def rtail (r : REdge) : Plane :=
  if r.2.2.2 then root τ (r.1 + 1) r.2.1 (r.2.2.1 - 1) else root τ (r.1 + 1) (r.2.1 - 1) r.2.2.1

/-- The tail of an edge (a site edge has tail and head its site). -/
def etail : Ed → Plane
  | Sum.inl ξ => ξ
  | Sum.inr r => rtail τ r

/-- The head of an edge. -/
def ehead : Ed → Plane
  | Sum.inl ξ => ξ
  | Sum.inr r => rhead τ r

/-! ## Private coordinates -/

/-- The arm of a real edge. -/
def armPred (r : REdge) (q : Coord) : Prop :=
  if r.2.2.2 then
    q.1.1 = rfree (a1 τ) (r.1 + 1) r.2.1 ∧
      ((q.2 = .wN ∧ rfree (a2 τ) (r.1 + 1) (r.2.2.1 - 1) ≤ q.1.2 ∧
          q.1.2 < rfree (a2 τ) (r.1 + 1) r.2.2.1) ∨
        (q.2 = .wS ∧ rfree (a2 τ) (r.1 + 1) (r.2.2.1 - 1) < q.1.2 ∧
          q.1.2 ≤ rfree (a2 τ) (r.1 + 1) r.2.2.1))
  else
    q.1.2 = rfree (a2 τ) (r.1 + 1) r.2.2.1 ∧
      ((q.2 = .wE ∧ rfree (a1 τ) (r.1 + 1) (r.2.1 - 1) ≤ q.1.1 ∧
          q.1.1 < rfree (a1 τ) (r.1 + 1) r.2.1) ∨
        (q.2 = .wW ∧ rfree (a1 τ) (r.1 + 1) (r.2.1 - 1) < q.1.1 ∧
          q.1.1 ≤ rfree (a1 τ) (r.1 + 1) r.2.1))

/-- The two components `ι` of the switches of an edge: `{0, 1}` horizontal, `{2, 3}` vertical. -/
def InPair (v : Bool) (ι : Fin 4) : Prop := if v then 2 ≤ ι.val else ι.val < 2

instance (v : Bool) (ι : Fin 4) : Decidable (InPair v ι) := by
  unfold InPair; split <;> infer_instance

variable (U : Machine)

/-- The sensor of a real edge of ready depth. -/
def sensPred (r : REdge) (q : Coord) : Prop :=
  MachineM.ready U (r.1 + 1) ∧ ∃ ι : Fin 4, InPair r.2.2.2 ι ∧
    ((∃ j, j < MachineM.Nd (r.1 + 1) ∧ q.1 = gsite τ (r.1 + 1) r.2.1 r.2.2.1 0 j ∧
        (q.2 = .kx ι ∨ q.2 = .ky ι)) ∨
      (q.1.1 = rfree (a1 τ) (r.1 + 1) r.2.1 ∧ zeta (a2 τ) (r.1 + 1) r.2.2.1 0 < q.1.2 ∧
        q.1.2 ≤ zeta (a2 τ) (r.1 + 1) r.2.2.1 (MachineM.Nd (r.1 + 1) - 1) ∧ q.2 = .lSx ι) ∨
      (q.1.1 = rfree (a1 τ) (r.1 + 1) r.2.1 ∧ zeta (a2 τ) (r.1 + 1) r.2.2.1 0 ≤ q.1.2 ∧
        q.1.2 < zeta (a2 τ) (r.1 + 1) r.2.2.1 (MachineM.Nd (r.1 + 1) - 1) ∧ q.2 = .lNx ι))

/-- The private coordinates of a real edge: its arm and, for a ready depth, its sensor. -/
def privPred (r : REdge) (q : Coord) : Prop := armPred τ r q ∨ sensPred τ U r q

variable {τ U}

/-! ## Disjointness (`pay:factor`(a)) -/

/-- An integer lies in at most one interval `[r_d(m), r_d(m + 1))`. -/
theorem idx_unique {a : ℕ → ℤ} {d : ℕ} {m m' z : ℤ} (h0 : rfree a d m ≤ z)
    (h1 : z < rfree a d (m + 1)) (h0' : rfree a d m' ≤ z) (h1' : z < rfree a d (m' + 1)) :
    m = m' :=
  rfree_inj ((rootBelow_eq h0 h1).symm.trans (rootBelow_eq h0' h1'))

/-- An integer lies in at most one interval `[r_d(m - 1), r_d(m))`. -/
theorem idx_unique' {a : ℕ → ℤ} {d : ℕ} {m m' z : ℤ} (h0 : rfree a d (m - 1) ≤ z)
    (h1 : z < rfree a d m) (h0' : rfree a d (m' - 1) ≤ z) (h1' : z < rfree a d m') : m = m' := by
  have := idx_unique (m := m - 1) (m' := m' - 1) h0 (by rwa [sub_add_cancel])
    h0' (by rwa [sub_add_cancel])
  omega

/-- The sites of the first column of a grid lie in `[r_d(m₂), r_d(m₂ + 1))`. -/
theorem zeta_mem_window {d : ℕ} (hd : 1 ≤ d) (m2 : ℤ) {j : ℕ} (hj : j < MachineM.Nd d) :
    rfree (a2 τ) d m2 ≤ zeta (a2 τ) d m2 j ∧ zeta (a2 τ) d m2 j < rfree (a2 τ) d (m2 + 1) := by
  have ha2 : FrameOffsets (a2 τ) := frameOffsets_phase _
  have hf := zeta_free ha2 hd m2 hj
  have h0 := zeta_le_zeta ha2 hd m2 hj (Nat.zero_le j)
  rw [zeta_zero ha2 hd] at h0
  have e := rfree_succ_eq (a2 τ) d m2
  have hp : (0 : ℤ) < 4 ^ d := by positivity
  exact ⟨h0, by linarith [hf.2.1]⟩

theorem zeta_last_lt {d : ℕ} (hd : 1 ≤ d) (m2 : ℤ) :
    zeta (a2 τ) d m2 (MachineM.Nd d - 1) < rfree (a2 τ) d (m2 + 1) :=
  (zeta_mem_window hd m2 (by have := MachineM.two_le_Nd d; omega)).2

theorem zeta_first {d : ℕ} (hd : 1 ≤ d) (m2 : ℤ) : zeta (a2 τ) d m2 0 = rfree (a2 τ) d m2 :=
  zeta_zero (frameOffsets_phase _) hd m2

/-- The window of the sensor column: `[ζ₀, ζ_{N-1}] ⊆ [r_d(m₂), r_d(m₂ + 1))`. -/
theorem col_window {d : ℕ} (hd : 1 ≤ d) (m2 : ℤ) {z : ℤ} (h0 : zeta (a2 τ) d m2 0 ≤ z)
    (h1 : z ≤ zeta (a2 τ) d m2 (MachineM.Nd d - 1)) :
    rfree (a2 τ) d m2 ≤ z ∧ z < rfree (a2 τ) d (m2 + 1) := by
  rw [zeta_first hd] at h0
  exact ⟨h0, lt_of_le_of_lt h1 (zeta_last_lt hd m2)⟩

theorem gsite_inj {d d' : ℕ} {m1 m2 m1' m2' : ℤ} {j j' : ℕ} (hj : j < MachineM.Nd (d + 1))
    (hj' : j' < MachineM.Nd (d' + 1))
    (h : gsite τ (d + 1) m1 m2 0 j = gsite τ (d' + 1) m1' m2' 0 j') :
    d = d' ∧ m1 = m1' ∧ m2 = m2' := by
  have ha1 : FrameOffsets (a1 τ) := frameOffsets_phase _
  have h1 : zeta (a1 τ) (d + 1) m1 0 = zeta (a1 τ) (d' + 1) m1' 0 := congrArg Prod.fst h
  have h2 : zeta (a2 τ) (d + 1) m2 j = zeta (a2 τ) (d' + 1) m2' j' := congrArg Prod.snd h
  rw [zeta_zero ha1 (by omega), zeta_zero ha1 (by omega)] at h1
  have hdd : d = d' := by have := rfree_depth_unique ha1 h1; omega
  subst hdd
  have w := zeta_mem_window (τ := τ) (by omega) m2 hj
  have w' := zeta_mem_window (τ := τ) (by omega) m2' hj'
  rw [h2] at w
  exact ⟨rfl, rfree_inj h1, idx_unique w.1 w.2 w'.1 w'.2⟩

theorem inPair_unique {v v' : Bool} {ι : Fin 4} (h : InPair v ι) (h' : InPair v' ι) : v = v' := by
  unfold InPair at h h'
  cases v <;> cases v' <;> simp_all <;> omega

/-- **`pay:factor`(a)**, disjointness: the private coordinates of different edges are disjoint. -/
theorem privPred_unique {r r' : REdge} {q : Coord} (h : privPred τ U r q)
    (h' : privPred τ U r' q) : r = r' := by
  obtain ⟨k, m1, m2, v⟩ := r
  obtain ⟨k', m1', m2', v'⟩ := r'
  obtain ⟨⟨x, y⟩, f⟩ := q
  have ha1 : FrameOffsets (a1 τ) := frameOffsets_phase _
  have ha2 : FrameOffsets (a2 τ) := frameOffsets_phase _
  rcases h with ha | ⟨hr, ι, hι, hs⟩ <;> rcases h' with ha' | ⟨hr', ι', hι', hs'⟩
  · -- two arms
    unfold armPred at ha ha'
    cases v <;> cases v' <;> simp only [Bool.false_eq_true, ↓reduceIte] at ha ha'
    · obtain ⟨hy, hw⟩ := ha
      obtain ⟨hy', hw'⟩ := ha'
      have hkk : k = k' := by have := rfree_depth_unique ha2 (hy.symm.trans hy'); omega
      subst hkk
      have e2 := rfree_inj (hy.symm.trans hy')
      have e1 : m1 - 1 = m1' - 1 := by
        rcases hw with ⟨rfl, h0, h1⟩ | ⟨rfl, h0, h1⟩ <;>
          rcases hw' with ⟨hf, h0', h1'⟩ | ⟨hf, h0', h1'⟩ <;> simp at hf
        · have := idx_unique' h0 h1 h0' h1'; omega
        · have := idx_unique' (a := a1 τ) (d := k + 1) (m := m1) (m' := m1') (z := x - 1)
            (by omega) (by omega) (by omega) (by omega)
          omega
      exact Prod.ext rfl (Prod.ext (by simp only; omega) (Prod.ext e2 rfl))
    · rcases ha.2 with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> rcases ha'.2 with ⟨hf, -⟩ | ⟨hf, -⟩ <;> simp at hf
    · rcases ha.2 with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> rcases ha'.2 with ⟨hf, -⟩ | ⟨hf, -⟩ <;> simp at hf
    · obtain ⟨hx, hw⟩ := ha
      obtain ⟨hx', hw'⟩ := ha'
      have hkk : k = k' := by have := rfree_depth_unique ha1 (hx.symm.trans hx'); omega
      subst hkk
      have e1 := rfree_inj (hx.symm.trans hx')
      have e2 : m2 - 1 = m2' - 1 := by
        rcases hw with ⟨rfl, h0, h1⟩ | ⟨rfl, h0, h1⟩ <;>
          rcases hw' with ⟨hf, h0', h1'⟩ | ⟨hf, h0', h1'⟩ <;> simp at hf
        · have := idx_unique' h0 h1 h0' h1'; omega
        · have := idx_unique' (a := a2 τ) (d := k + 1) (m := m2) (m' := m2') (z := y - 1)
            (by omega) (by omega) (by omega) (by omega)
          omega
      exact Prod.ext rfl (Prod.ext e1 (Prod.ext (by simp only; omega) rfl))
  · -- an arm and a sensor: different fields
    exfalso
    unfold armPred at ha
    have hf : f = .wN ∨ f = .wS ∨ f = .wE ∨ f = .wW := by
      split_ifs at ha
      · rcases ha.2 with ⟨h, -⟩ | ⟨h, -⟩ <;> simp_all
      · rcases ha.2 with ⟨h, -⟩ | ⟨h, -⟩ <;> simp_all
    rcases hs' with ⟨j, -, -, h | h⟩ | ⟨-, -, -, h⟩ | ⟨-, -, -, h⟩ <;>
      rcases hf with rfl | rfl | rfl | rfl <;> simp at h
  · exfalso
    unfold armPred at ha'
    have hf : f = .wN ∨ f = .wS ∨ f = .wE ∨ f = .wW := by
      split_ifs at ha'
      · rcases ha'.2 with ⟨h, -⟩ | ⟨h, -⟩ <;> simp_all
      · rcases ha'.2 with ⟨h, -⟩ | ⟨h, -⟩ <;> simp_all
    rcases hs with ⟨j, -, -, h | h⟩ | ⟨-, -, -, h⟩ | ⟨-, -, -, h⟩ <;>
      rcases hf with rfl | rfl | rfl | rfl <;> simp at h
  · -- two sensors
    have hιι : ι = ι' := by
      rcases hs with ⟨j, -, -, h | h⟩ | ⟨-, -, -, h⟩ | ⟨-, -, -, h⟩ <;>
        rcases hs' with ⟨j', -, -, h' | h'⟩ | ⟨-, -, -, h'⟩ | ⟨-, -, -, h'⟩ <;>
        simp only at h h' <;> rw [h] at h' <;> simp at h' <;> exact h'
    subst hιι
    have hvv := inPair_unique hι hι'
    subst hvv
    simp only [Prod.mk.injEq, and_true]
    rcases hs with ⟨j, hj, hq, h⟩ | ⟨hx, h0, h1, h⟩ | ⟨hx, h0, h1, h⟩ <;>
      rcases hs' with ⟨j', hj', hq', h'⟩ | ⟨hx', h0', h1', h'⟩ | ⟨hx', h0', h1', h'⟩
    · exact gsite_inj hj hj' (hq.symm.trans hq')
    · exfalso; rcases h with h | h <;> rw [h] at h' <;> simp at h'
    · exfalso; rcases h with h | h <;> rw [h] at h' <;> simp at h'
    · exfalso; rcases h' with h' | h' <;> rw [h'] at h <;> simp at h
    · have hkk : k = k' := by have := rfree_depth_unique ha1 (hx.symm.trans hx'); omega
      subst hkk
      have w := col_window (τ := τ) (by omega) m2 h0.le h1
      have w' := col_window (τ := τ) (by omega) m2' h0'.le h1'
      exact ⟨rfl, rfree_inj (hx.symm.trans hx'), idx_unique w.1 w.2 w'.1 w'.2⟩
    · exfalso; rw [h] at h'; simp at h'
    · exfalso; rcases h' with h' | h' <;> rw [h'] at h <;> simp at h
    · exfalso; rw [h] at h'; simp at h'
    · have hkk : k = k' := by have := rfree_depth_unique ha1 (hx.symm.trans hx'); omega
      subst hkk
      have w := col_window (τ := τ) (by omega) m2 h0 h1.le
      have w' := col_window (τ := τ) (by omega) m2' h0' h1'.le
      exact ⟨rfl, rfree_inj (hx.symm.trans hx'), idx_unique w.1 w.2 w'.1 w'.2⟩

/-- No spin coordinate is private. -/
theorem not_privPred_spin {r : REdge} {ξ : Plane} : ¬ privPred τ U r (ξ, .spin) := by
  rintro (ha | ⟨-, ι, -, hs⟩)
  · unfold armPred at ha
    split_ifs at ha
    · rcases ha.2 with ⟨h, -⟩ | ⟨h, -⟩ <;> simp at h
    · rcases ha.2 with ⟨h, -⟩ | ⟨h, -⟩ <;> simp at h
  · rcases hs with ⟨j, -, -, h | h⟩ | ⟨-, -, -, h⟩ | ⟨-, -, -, h⟩ <;> simp at h

/-! ## The owner of a coordinate, the private coordinates, the relabelling -/

variable (τ U) in
open Classical in
/-- The edge of a coordinate: the real edge to whose private coordinates it belongs, if any (unique
by `privPred_unique`), and otherwise the site edge of its site. -/
def owner (q : Coord) : Ed := if h : ∃ r, privPred τ U r q then Sum.inr h.choose else Sum.inl q.1

theorem owner_of {r : REdge} {q : Coord} (h : privPred τ U r q) : owner τ U q = Sum.inr r := by
  have hex : ∃ r, privPred τ U r q := ⟨r, h⟩
  rw [owner, dif_pos hex, privPred_unique hex.choose_spec h]

theorem owner_of_not {q : Coord} (h : ¬ ∃ r, privPred τ U r q) : owner τ U q = Sum.inl q.1 := by
  rw [owner, dif_neg h]

theorem privPred_of_owner {r : REdge} {q : Coord} (h : owner τ U q = Sum.inr r) :
    privPred τ U r q := by
  by_cases hex : ∃ r, privPred τ U r q
  · rw [owner, dif_pos hex] at h
    rw [← Sum.inr.inj h]; exact hex.choose_spec
  · rw [owner, dif_neg hex] at h
    exact absurd h (by simp)

theorem of_owner_inl {ξ : Plane} {q : Coord} (h : owner τ U q = Sum.inl ξ) :
    q.1 = ξ ∧ ¬ ∃ r, privPred τ U r q := by
  by_cases hex : ∃ r, privPred τ U r q
  · rw [owner, dif_pos hex] at h
    exact absurd h (by simp)
  · rw [owner, dif_neg hex] at h
    exact ⟨Sum.inl.inj h, hex⟩

variable (τ U) in
/-- The private coordinates of an edge (`pay:factor`(a); the fixed coordinates of a site are the
private coordinates of its site edge). -/
abbrev Q (e : Ed) : Type := {q : Coord // q.2 ≠ .spin ∧ owner τ U q = e}

theorem rfree_pred_le (a : ℕ → ℤ) (d : ℕ) (m : ℤ) : rfree a d (m - 1) ≤ rfree a d m := by
  have := rfree_succ a d (m - 1)
  rw [sub_add_cancel] at this
  have hp : (0 : ℤ) < 4 ^ (d + 1) := by positivity
  linarith

/-- The private coordinates of a real edge are finitely many. -/
theorem privPred_finite (r : REdge) : {q : Coord | privPred τ U r q}.Finite := by
  obtain ⟨k, m1, m2, v⟩ := r
  have hsub : {q : Coord | privPred τ U (k, m1, m2, v) q} ⊆
      ((Set.Icc (rfree (a1 τ) (k + 1) (m1 - 1)) (rfree (a1 τ) (k + 1) m1) ×ˢ
          Set.Icc (rfree (a2 τ) (k + 1) (m2 - 1)) (rfree (a2 τ) (k + 1) m2)) ×ˢ Set.univ) ∪
        ((((Finset.range (MachineM.Nd (k + 1))).image (gsite τ (k + 1) m1 m2 0) : Set Plane)) ×ˢ
          Set.univ) ∪
        (({rfree (a1 τ) (k + 1) m1} ×ˢ Set.Icc (zeta (a2 τ) (k + 1) m2 0)
          (zeta (a2 τ) (k + 1) m2 (MachineM.Nd (k + 1) - 1))) ×ˢ Set.univ) := by
    rintro ⟨⟨x, y⟩, f⟩ (ha | ⟨-, ι, -, hs⟩)
    · have p1 := rfree_pred_le (a1 τ) (k + 1) m1
      have p2 := rfree_pred_le (a2 τ) (k + 1) m2
      left; left
      unfold armPred at ha
      simp only [Set.mem_prod, Set.mem_Icc, Set.mem_univ, and_true]
      cases v <;> simp only [Bool.false_eq_true, ↓reduceIte] at ha
      · obtain ⟨rfl, h⟩ := ha
        rcases h with ⟨-, h0, h1⟩ | ⟨-, h0, h1⟩ <;> exact ⟨⟨by omega, by omega⟩, p2, le_rfl⟩
      · obtain ⟨rfl, h⟩ := ha
        rcases h with ⟨-, h0, h1⟩ | ⟨-, h0, h1⟩ <;> exact ⟨⟨p1, le_rfl⟩, by omega, by omega⟩
    · rcases hs with ⟨j, hj, hq, -⟩ | ⟨hx, h0, h1, -⟩ | ⟨hx, h0, h1, -⟩
      · left; right
        simp only [Set.mem_prod, Finset.coe_image, Set.mem_image, Finset.mem_coe,
          Finset.mem_range, Set.mem_univ, and_true]
        exact ⟨j, hj, hq.symm⟩
      · right
        simp only [Set.mem_prod, Set.mem_singleton_iff, Set.mem_Icc, Set.mem_univ, and_true]
        exact ⟨hx, h0.le, h1⟩
      · right
        simp only [Set.mem_prod, Set.mem_singleton_iff, Set.mem_Icc, Set.mem_univ, and_true]
        exact ⟨hx, h0, h1.le⟩
  refine Set.Finite.subset (Set.Finite.union (Set.Finite.union ?_ ?_) ?_) hsub
  · exact ((Set.finite_Icc _ _).prod (Set.finite_Icc _ _)).prod Set.finite_univ
  · exact (Finset.finite_toSet _).prod Set.finite_univ
  · exact ((Set.finite_singleton _).prod (Set.finite_Icc _ _)).prod Set.finite_univ

instance (e : Ed) : Finite (Q τ U e) := by
  rcases e with ξ | r
  · refine Finite.of_injective (fun q : Q τ U (Sum.inl ξ) => q.1.2) ?_
    intro a b h
    apply Subtype.ext
    exact Prod.ext ((of_owner_inl a.2.2).1.trans (of_owner_inl b.2.2).1.symm) h
  · have := (privPred_finite (τ := τ) (U := U) r).to_subtype
    exact Finite.of_injective
      (fun q : Q τ U (Sum.inr r) =>
        (⟨q.1, privPred_of_owner q.2.2⟩ : {q : Coord | privPred τ U r q}))
      (fun a b h => Subtype.ext (by have := congrArg Subtype.val h; exact this))

noncomputable instance (e : Ed) : Fintype (Q τ U e) := Fintype.ofFinite _

/-- (An intermediate instance; instance search for `DecidableEq (Plane ⊕ Σ e, Q e)` otherwise
gives up.) -/
instance instDecEqSigmaQ : DecidableEq (Σ e : Ed, Q τ U e) := inferInstance

variable (τ U) in
/-- **The relabelling** `Coord ≃ Plane ⊕ Σ e, Q e`: spin coordinates to the vertices, every other
coordinate to its owner (`pay:factor`(a)). -/
def relabel : Coord ≃ Gibbs.ECoord Plane Ed (Q τ U) where
  toFun q := if h : q.2 = .spin then Sum.inl q.1 else Sum.inr ⟨owner τ U q, ⟨q, h, rfl⟩⟩
  invFun x := match x with
    | Sum.inl ξ => (ξ, .spin)
    | Sum.inr ⟨_, q⟩ => q.1
  left_inv q := by
    obtain ⟨ξ, f⟩ := q
    by_cases h : f = .spin
    · subst h; simp
    · simp [h]
  right_inv x := by
    rcases x with ξ | ⟨e, ⟨q, hq, ho⟩⟩
    · simp
    · subst ho
      simp [hq]

theorem relabel_spin (ξ : Plane) : relabel τ U (ξ, .spin) = Sum.inl ξ := by simp [relabel]

theorem relabel_of {q : Coord} (h : q.2 ≠ .spin) :
    relabel τ U q = Sum.inr ⟨owner τ U q, ⟨q, h, rfl⟩⟩ := by simp [relabel, h]

/-! ## The edges at a vertex -/

variable (τ) in
open Classical in
/-- The depth and index of a root (`none` at the other sites). -/
def rootIdx (v : Plane) : Option (ℕ × ℤ × ℤ) :=
  if h : ∃ p : ℕ × ℤ × ℤ, v = root τ (p.1 + 1) p.2.1 p.2.2 then some h.choose else none

variable (τ) in
/-- The edges with an end at `v`: its site edge, and if `v = 𝐫_d(m)` the two edges with head `v`
and the two with tail `v`. -/
def edgesAt (v : Plane) : Finset Ed :=
  match rootIdx τ v with
  | some p => {Sum.inl v, Sum.inr (p.1, p.2.1, p.2.2, false), Sum.inr (p.1, p.2.1, p.2.2, true),
      Sum.inr (p.1, p.2.1 + 1, p.2.2, false), Sum.inr (p.1, p.2.1, p.2.2 + 1, true)}
  | none => {Sum.inl v}

theorem rootIdx_root (k : ℕ) (m1 m2 : ℤ) :
    rootIdx τ (root τ (k + 1) m1 m2) = some (k, m1, m2) := by
  have hex : ∃ p : ℕ × ℤ × ℤ, root τ (k + 1) m1 m2 = root τ (p.1 + 1) p.2.1 p.2.2 :=
    ⟨(k, m1, m2), rfl⟩
  rw [rootIdx, dif_pos hex]
  obtain ⟨h1, h2, h3⟩ := root_inj' hex.choose_spec
  congr 1
  exact Prod.ext (by omega) (Prod.ext h2.symm h3.symm)

theorem rootIdx_none {v : Plane} (h : ∀ k m1 m2, v ≠ root τ (k + 1) m1 m2) :
    rootIdx τ v = none := by
  rw [rootIdx, dif_neg]
  rintro ⟨p, hp⟩
  exact h _ _ _ hp

theorem mem_edgesAt (v : Plane) (e : Ed) :
    e ∈ edgesAt τ v ↔ etail τ e = v ∨ ehead τ e = v := by
  by_cases hv : ∃ k m1 m2, v = root τ (k + 1) m1 m2
  · obtain ⟨k, m1, m2, rfl⟩ := hv
    rw [edgesAt, rootIdx_root]
    rcases e with ξ | ⟨k', m1', m2', w⟩
    · simp [etail, ehead, eq_comm]
    · simp only [Finset.mem_insert, Finset.mem_singleton, reduceCtorEq, Sum.inr.injEq,
        Prod.mk.injEq, false_or, etail, ehead, rtail, rhead]
      constructor
      · rintro (⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
          ⟨rfl, rfl, rfl, rfl⟩) <;> simp
      · intro h
        cases w <;> simp only [Bool.false_eq_true, ↓reduceIte] at h <;>
          rcases h with h | h <;> obtain ⟨h1, h2, h3⟩ := root_inj' h <;>
          simp only [Nat.add_right_cancel_iff] at h1 <;> subst h1 <;> simp <;> omega
  · push Not at hv
    rw [edgesAt, rootIdx_none hv]
    rcases e with ξ | ⟨k', m1', m2', w⟩
    · simp [etail, ehead, eq_comm]
    · simp only [Finset.mem_singleton, reduceCtorEq, false_iff, not_or, etail, ehead, rtail,
        rhead]
      constructor
      · cases w <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> exact fun h => hv _ _ _ h.symm
      · exact fun h => hv _ _ _ h.symm

/-! ## The factors (`pay:factor`(b)) -/

/-- The fixed value of a coordinate of a site edge (`pay:factor`(a)): `□` for wire values, `0`
for bits. -/
def fixedVal : PFld → PV
  | .spin => .sp .plus
  | .wW => .wire none
  | .wE => .wire none
  | .wS => .wire none
  | .wN => .wire none
  | .kx _ => .bit false
  | .ky _ => .bit false
  | .lSx _ => .bit false
  | .lNx _ => .bit false

variable (τ U) in
open Classical in
/-- The switch `x_ι` of the sensor of `r`, read at the root `v = rhead r` (`0` if it is not a
private coordinate of `r`, i.e. for a non-ready depth or a component of the other edge). -/
def swv (r : REdge) (ζ : Q τ U (Sum.inr r) → PV) (ι : Fin 4) : Bool :=
  if h : (rhead τ r, PFld.kx ι).2 ≠ .spin ∧ owner τ U (rhead τ r, PFld.kx ι) = Sum.inr r then
    (ζ ⟨_, h⟩).bitOf
  else false

variable (τ U) in
/-- The value that `pay:factor`(b) forces at a private coordinate of `r`, given the tail spin `a`
and the switches and free bits: the arm equals `σ_u`, the copies equal the switch, and a free bit
`y_ι(0, j)` is kept only if `x_ι = g_ι(0, j) = 1`. -/
def tgt (r : REdge) (a : PV) (ζ : Q τ U (Sum.inr r) → PV) (q : Q τ U (Sum.inr r)) : PV :=
  match q.1.2 with
  | .spin => .sp a.spinOf
  | .wW => .wire (some a.spinOf)
  | .wE => .wire (some a.spinOf)
  | .wS => .wire (some a.spinOf)
  | .wN => .wire (some a.spinOf)
  | .kx ι => .bit (swv τ U r ζ ι)
  | .ky ι => .bit ((ζ q).bitOf && swv τ U r ζ ι && gB U (bgMap U τ q.1.1) ι)
  | .lSx ι => .bit (swv τ U r ζ ι)
  | .lNx ι => .bit (swv τ U r ζ ι)

/-- The first switch component of an edge (`x⁻`): `0` horizontal, `2` vertical. -/
def iMinus (r : REdge) : Fin 4 := if r.2.2.2 then 2 else 0

/-- The second switch component of an edge (`x⁺`): `1` horizontal, `3` vertical. -/
def iPlus (r : REdge) : Fin 4 := if r.2.2.2 then 3 else 1

variable (τ U) in
/-- The support of `W_e` (`pay:factor`(b)): for a site edge, the fixed values; for a real edge,
"arm `≡ σ_u`", "sensor consistent" (`ζ = tgt`), and (P3): `(x⁻, x⁺) = (0, 1) ⇒ σ_v = σ_u`. -/
def Good : (e : Ed) → (Q τ U e → PV) → PV → PV → Prop
  | Sum.inl _, ζ, _, _ => ∀ q, ζ q = fixedVal q.1.2
  | Sum.inr r, ζ, a, b => (∀ q, ζ q = tgt τ U r a ζ q) ∧
      (swv τ U r ζ (iMinus r) = false → swv τ U r ζ (iPlus r) = true → a = b)

/-- A payload value (any one: the predicates of a merged site value read only the background). -/
def p0 : PayVal := ⟨.plus, none, none, none, none, fun _ => false, fun _ => false, fun _ => false,
  fun _ => false⟩

variable (τ U) in
open Classical in
/-- The charge carried by the coordinate `q` with value `w`: the bit `x_ι` at a site where the
charge of `int:sub-charge` reads the component `ι` (an active site with `f_W = 1`, `rc ≤ 79`,
`ι = ⌊rc/20⌋`), and `0` otherwise. -/
def chW (q : Coord) (w : PV) : ℝ :=
  match q.2 with
  | .kx ι =>
    if ∃ c, (bgMap U τ q.1).k = some c ∧ (merge (bgMap U τ q.1) p0).IsActive ∧
        (merge (bgMap U τ q.1) p0).fW = true ∧ c.rc.val ≤ 79 ∧ ι.val = c.rc.val / 20 then
      Sensor.bitR w.bitOf
    else 0
  | _ => 0

variable (τ U) in
open Classical in
/-- **The factor `W_e`** of `pay:factor`(b): the indicator of `Good` times `e^{-β}` to the charge
of the private coordinates (on the support: `e^{-20β(x⁻ + x⁺)}` for a ready edge, `1` otherwise). -/
def Wf (β : ℝ) (e : Ed) (ζ : Q τ U e → PV) (a b : PV) : ℝ :=
  (if Good τ U e ζ a b then 1 else 0) * Real.exp (-β * ∑ q, chW τ U q.1 (ζ q))

theorem Wf_nonneg (β : ℝ) (e : Ed) (ζ : Q τ U e → PV) (a b : PV) : 0 ≤ Wf τ U β e ζ a b := by
  unfold Wf; positivity

/-- A configuration of the private coordinates on the support of `W_e` (all switches `0`). -/
def zeta0 : (e : Ed) → PV → Q τ U e → PV
  | Sum.inl _, _, q => fixedVal q.1.2
  | Sum.inr _, a, q => match q.1.2 with
    | .spin => .sp a.spinOf
    | .wW => .wire (some a.spinOf)
    | .wE => .wire (some a.spinOf)
    | .wS => .wire (some a.spinOf)
    | .wN => .wire (some a.spinOf)
    | _ => .bit false

theorem swv_zeta0 (r : REdge) (a : PV) (ι : Fin 4) :
    swv τ U r (zeta0 (Sum.inr r) a) ι = false := by
  unfold swv
  split_ifs
  · rfl
  · rfl

theorem good_zeta0 (e : Ed) (a b : PV) : Good τ U e (zeta0 e a) a b := by
  rcases e with ξ | r
  · intro q; rfl
  · refine ⟨fun q => ?_, fun h => by rw [swv_zeta0] at h ⊢; simp at *⟩
    obtain ⟨⟨ξ, f⟩, hq, ho⟩ := q
    cases f <;> simp [zeta0, tgt, swv_zeta0, PV.bitOf]

theorem Zf_pos (β : ℝ) (e : Ed) (a b : PV) : 0 < ∑ ζ : Q τ U e → PV, Wf τ U β e ζ a b := by
  classical
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun ζ _ => Wf_nonneg β e ζ a b)
    (Finset.mem_univ (zeta0 e a)))
  unfold Wf
  rw [if_pos (good_zeta0 e a b), one_mul]
  exact Real.exp_pos _

variable (τ U) in
/-- **The data of `pay:elim` for `𝔟_τ`**: vertices the sites, edges the real edges and the site
edges, private coordinates `Q e`, factors `W_e`, and the vertex factor `κ_v = 1[σ_v` is a spin`]`. -/
def elimData (β : ℝ) : Gibbs.ElimData Plane Ed (Q τ U) PV where
  tail := etail τ
  head := ehead τ
  edgesAt := edgesAt τ
  mem_edgesAt := mem_edgesAt
  Wf := Wf τ U β
  Wf_nonneg := Wf_nonneg β
  Zf_pos := Zf_pos β
  κ _ a := if PFld.spin.ok a = true then 1 else 0
  κ_nonneg _ a := by split_ifs <;> norm_num

end UPD.BG

/-
# Section 6: the legal payloads of `𝔟_τ` are the explicit payloads `payX`

New in this project (session 10). The combinatorial core of `pay:factor`(a), (b): for typical `τ`,
the payloads `p` with `(𝔟_τ, p)` legal are exactly the payloads `payX U τ σ sw yv` with `(P3)` on
the free data (`P3X`).

* Evaluations of the explicit payload: `kxX_gsite`, `kxX_eq_false`, `kxX_gpos` (the switch copies
  at the cell records), `lNxX_col`, `lNxX_eq_false`, `lNxX_vseg` (the copies on the first columns),
  `wEc_arm`, `wEc_unmarked`, `wNc_arm`, `wNc_unmarked` (the wire values: "the arm has all values
  equal to `σ_u`").
* `compatible_payX`, `payOf_cfg` (the payload of `cfg U τ σ` is `payX U τ σ 0 0`), `cfg_site`.
* **Legal ⇒ explicit** (`payOf_eq_payX`, `p3X_of_legal`): (P1)/(P2) with matching force the wire
  values (`wE_legal`, `wN_legal`); (C8) with (K2) and matching along the first column copies the
  switch at the root, `x = 0` outside first columns and in non-ready grids (`kx_legal`,
  `lNx_legal`); (C9) gives `y = y ∧ x ∧ g`; (P3) at a root gives `P3X`.
* **Explicit ⇒ legal** (`legal_payX`): every rule except (K2), (C8), (C9), (P3) and the `x` part of
  vertical matching reads no `x`, `y` (`allowed_merge`, the transfer from `cfg U τ σ`); these are
  checked directly.
* `legal_iff_payX`: both directions together, for payloads compatible with `𝔟_τ`.
-/
import UndecidablePhaseDiagram.Payload.PayX

set_option autoImplicit false

noncomputable section

namespace UPD.BG

open UPD.Scaffold

/-! ## Roots along a line -/

theorem rootBelow_le (a : ℕ → ℤ) (d : ℕ) (z : ℤ) : rootBelow a d z ≤ z := by
  have hP : (4 : ℤ) ^ (d + 1) ≠ 0 := by positivity
  have h := Int.ediv_mul_le (z - rfree a d 0) hP
  unfold rootBelow
  rw [rfree_eq_add a d ((z - rfree a d 0) / 4 ^ (d + 1))]
  linarith

theorem rootBelow_eq {a : ℕ → ℤ} {d : ℕ} {m z : ℤ} (h0 : rfree a d m ≤ z)
    (h1 : z < rfree a d (m + 1)) : rootBelow a d z = rfree a d m := by
  have hP : (0 : ℤ) < 4 ^ (d + 1) := by positivity
  have e := rfree_eq_add a d m
  have e1 := rfree_succ a d m
  unfold rootBelow
  congr 1
  rw [show z - rfree a d 0 = (z - rfree a d m) + m * 4 ^ (d + 1) by linarith,
    Int.add_mul_ediv_right _ _ hP.ne', Int.ediv_eq_zero_of_lt (by linarith) (by linarith),
    zero_add]

theorem rfree_succ_eq (a : ℕ → ℤ) (d : ℕ) (m : ℤ) :
    rfree a d (m + 1) = frameHi a d m + 2 * 4 ^ d + 2 := by
  simp only [rfree, frameLo, frameHi]; ring

theorem rootBelow_of_frame {a : ℕ → ℤ} {d : ℕ} {m z : ℤ} (h0 : rfree a d m ≤ z)
    (h1 : z < frameHi a d m) : rootBelow a d z = rfree a d m := by
  have hp : (0 : ℤ) < 4 ^ d := by positivity
  have e := rfree_succ_eq a d m
  exact rootBelow_eq h0 (by linarith)

/-- (P1)/(P2) along a marked line: a value equal to the spin at every root and copied at every
other site is the spin at the nearest root at or below. -/
theorem wire_line {a : ℕ → ℤ} {d : ℕ} {f : ℤ → Option Spin} {s : ℤ → Spin}
    (hroot : ∀ m, f (rfree a d m) = some (s (rfree a d m)))
    (hcopy : ∀ z, (∀ m, z ≠ rfree a d m) → f z = f (z - 1)) (z : ℤ) :
    f z = some (s (rootBelow a d z)) := by
  suffices H : ∀ n : ℕ, ∀ z, z - rootBelow a d z = n → f z = some (s (rootBelow a d z)) from
    H (z - rootBelow a d z).toNat z (by have := rootBelow_le a d z; omega)
  intro n
  induction n with
  | zero =>
    intro z hz
    obtain ⟨q, hq⟩ : ∃ q, rootBelow a d z = rfree a d q := ⟨_, rfl⟩
    have hzq : z = rfree a d q := by omega
    subst hzq
    rw [rootBelow_self]
    exact hroot q
  | succ n ih =>
    intro z hz
    have hnr : ∀ m, z ≠ rfree a d m := by
      intro m hm
      rw [hm, rootBelow_self] at hz
      omega
    rw [hcopy z hnr, rootBelow_pred hnr]
    exact ih (z - 1) (by rw [← rootBelow_pred hnr]; omega)

/-- A function copied upward across an interval is constant on it. -/
theorem const_up {α : Type} {f : ℤ → α} {p q : ℤ} (h : ∀ z, p < z → z < q → f z = f (z - 1)) :
    ∀ z, p ≤ z → z < q → f z = f p := by
  intro z h0 h1
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, z = p + k := ⟨(z - p).toNat, by omega⟩
  induction k with
  | zero => simp
  | succ k ih =>
    rw [h _ (by omega) h1, show p + ((k + 1 : ℕ) : ℤ) - 1 = p + k by push_cast; ring]
    exact ih (by omega) (by omega)

/-! ## Free coordinates -/

theorem zeta_le_zeta {a : ℕ → ℤ} (ha : FrameOffsets a) {d : ℕ} (hd : 1 ≤ d) (m : ℤ) {i i' : ℕ}
    (hi' : i' < MachineM.Nd d) (h : i ≤ i') : zeta a d m i ≤ zeta a d m i' := by
  rcases h.lt_or_eq with h | rfl
  · exact ((zeta_lt_iff ha hd m (by omega) hi').2 h).le
  · exact le_rfl

/-- Every point of `[ζ_0, ζ_{N-1})` lies in a channel `[ζ_j, ζ_{j+1})`. -/
theorem exists_zeta_interval {a : ℕ → ℤ} {d : ℕ} (m : ℤ) {z : ℤ} (h0 : zeta a d m 0 ≤ z)
    (h1 : z < zeta a d m (MachineM.Nd d - 1)) :
    ∃ j, j + 1 < MachineM.Nd d ∧ zeta a d m j ≤ z ∧ z < zeta a d m (j + 1) := by
  have key : ∀ n : ℕ, z < zeta a d m n →
      ∃ j, j + 1 ≤ n ∧ zeta a d m j ≤ z ∧ z < zeta a d m (j + 1) := by
    intro n
    induction n with
    | zero => intro h; exact absurd h0 (not_le.2 h)
    | succ n ih =>
      intro h
      by_cases hz : zeta a d m n ≤ z
      · exact ⟨n, le_rfl, hz, h⟩
      · obtain ⟨j, hj, h2⟩ := ih (not_le.1 hz)
        exact ⟨j, by omega, h2⟩
  have hN := MachineM.two_le_Nd d
  obtain ⟨j, hj, h2⟩ := key (MachineM.Nd d - 1) h1
  exact ⟨j, by omega, h2⟩

variable {U : Machine} {τ : ℕ → Bool × Bool}

theorem colRoot_gsite {d : ℕ} (hd : 1 ≤ d) (m1 m2 : ℤ) {i j : ℕ} (hj : j < MachineM.Nd d) :
    colRoot τ d (gsite τ d m1 m2 i j) = (zeta (a1 τ) d m1 i, rfree (a2 τ) d m2) := by
  have ha2 : FrameOffsets (a2 τ) := frameOffsets_phase _
  have hf := zeta_free ha2 hd m2 hj
  have h0 : rfree (a2 τ) d m2 ≤ zeta (a2 τ) d m2 j := by
    have := hf.1; simp only [rfree]; omega
  simp only [colRoot, gsite]
  rw [rootBelow_of_frame h0 hf.2.1]

/-! ## Evaluation of the explicit switch copies -/

section Eval

variable (sw : Plane → Fin 4 → Bool)

theorem kxX_gsite {d : ℕ} (hd : 1 ≤ d) (hr : MachineM.ready U d) (m1 m2 : ℤ) {j : ℕ}
    (hj : j < MachineM.Nd d) (ι : Fin 4) :
    kxX U τ sw (gsite τ d m1 m2 0 j) ι = sw (root τ d m1 m2) ι := by
  classical
  have ha1 : FrameOffsets (a1 τ) := frameOffsets_phase _
  have h0 : 0 < MachineM.Nd d := by have := MachineM.two_le_Nd d; omega
  have hpos : GPos τ (d, 0, j) (gsite τ d m1 m2 0 j) := ⟨hd, h0, hj, m1, m2, rfl⟩
  have hroot : colRoot τ d (gsite τ d m1 m2 0 j) = root τ d m1 m2 := by
    rw [colRoot_gsite hd m1 m2 hj, zeta_zero ha1 hd]; rfl
  rw [Bool.eq_iff_iff, kxX, decide_eq_true_iff]
  constructor
  · rintro ⟨d', j', ⟨hp', -⟩, hsw⟩
    have e : d' = d := congrArg Prod.fst (GPos_unique hp' hpos)
    subst e
    rwa [hroot] at hsw
  · intro h
    exact ⟨d, j, ⟨hpos, hr⟩, by rw [hroot]; exact h⟩

theorem kxX_eq_false {ξ : Plane}
    (h : ¬ ∃ d m1 m2 j, 1 ≤ d ∧ MachineM.ready U d ∧ j < MachineM.Nd d ∧
      ξ = gsite τ d m1 m2 0 j) (ι : Fin 4) : kxX U τ sw ξ ι = false := by
  rw [kxX, decide_eq_false_iff_not]
  rintro ⟨d, j, ⟨⟨hd, -, hj, m1, m2, hξ⟩, hr⟩, -⟩
  exact h ⟨d, m1, m2, j, hd, hr, hj, hξ⟩

/-- The switch copy at a site `ξ(i, j)` of a grid. -/
theorem kxX_gpos {d : ℕ} (hd : 1 ≤ d) (m1 m2 : ℤ) {i j : ℕ} (hi : i < MachineM.Nd d)
    (hj : j < MachineM.Nd d) (ι : Fin 4) :
    kxX U τ sw (gsite τ d m1 m2 i j) ι =
      if i = 0 ∧ MachineM.ready U d then sw (root τ d m1 m2) ι else false := by
  by_cases h : i = 0 ∧ MachineM.ready U d
  · rw [if_pos h]
    obtain ⟨rfl, hr⟩ := h
    exact kxX_gsite sw hd hr m1 m2 hj ι
  · rw [if_neg h, kxX, decide_eq_false_iff_not]
    rintro ⟨d', j', ⟨hp', hr'⟩, -⟩
    have e := GPos_unique hp' (⟨hd, hi, hj, m1, m2, rfl⟩ : GPos τ (d, i, j) (gsite τ d m1 m2 i j))
    simp only [Prod.mk.injEq] at e
    obtain ⟨rfl, rfl, -⟩ := e
    exact h ⟨rfl, hr'⟩

theorem kxX_of_not_gpos {ξ : Plane} (h : ¬ ∃ p, GPos τ p ξ) :
    kxX U τ sw ξ = fun _ => false := by
  funext ι
  rw [kxX, decide_eq_false_iff_not]
  rintro ⟨d, j, ⟨hp, -⟩, -⟩
  exact h ⟨_, hp⟩

theorem lNxX_col {d : ℕ} (hd : 1 ≤ d) (hr : MachineM.ready U d) (m1 m2 : ℤ) {z : ℤ}
    (h0 : zeta (a2 τ) d m2 0 ≤ z) (h1 : z < zeta (a2 τ) d m2 (MachineM.Nd d - 1)) (ι : Fin 4) :
    lNxX U τ sw (rfree (a1 τ) d m1, z) ι = sw (root τ d m1 m2) ι := by
  classical
  have ha1 : FrameOffsets (a1 τ) := frameOffsets_phase _
  have ha2 : FrameOffsets (a2 τ) := frameOffsets_phase _
  obtain ⟨j, hj, hz0, hz1⟩ := exists_zeta_interval m2 h0 h1
  have h0' : 0 < MachineM.Nd d := by omega
  have hseg : VSeg τ (d, 0, j) (rfree (a1 τ) d m1, z) :=
    ⟨hd, h0', hj, m1, m2, (zeta_zero ha1 hd m1).symm, hz0, hz1⟩
  have hroot : colRoot τ d (rfree (a1 τ) d m1, z) = root τ d m1 m2 := by
    have hl := zeta_last ha2 hd m2
    rw [zeta_zero ha2 hd] at h0
    simp only [colRoot, root]
    rw [rootBelow_of_frame h0 (by omega)]
  rw [Bool.eq_iff_iff, lNxX, decide_eq_true_iff]
  constructor
  · rintro ⟨d', j', ⟨hs', -⟩, hsw⟩
    have e : d' = d := congrArg Prod.fst (VSeg_unique hs' hseg)
    subst e
    rwa [hroot] at hsw
  · intro h
    exact ⟨d, j, ⟨hseg, hr⟩, by rw [hroot]; exact h⟩

theorem lNxX_eq_false {ξ : Plane}
    (h : ¬ ∃ d m1 m2 z, 1 ≤ d ∧ MachineM.ready U d ∧ zeta (a2 τ) d m2 0 ≤ z ∧
      z < zeta (a2 τ) d m2 (MachineM.Nd d - 1) ∧ ξ = (rfree (a1 τ) d m1, z)) (ι : Fin 4) :
    lNxX U τ sw ξ ι = false := by
  have ha1 : FrameOffsets (a1 τ) := frameOffsets_phase _
  have ha2 : FrameOffsets (a2 τ) := frameOffsets_phase _
  rw [lNxX, decide_eq_false_iff_not]
  rintro ⟨d, j, ⟨⟨hd, -, hj, m1, m2, hx, hz0, hz1⟩, hr⟩, -⟩
  simp only at hd hj hx hz0 hz1
  refine h ⟨d, m1, m2, ξ.2, hd, hr,
    le_trans (zeta_le_zeta ha2 hd m2 (by omega) (Nat.zero_le j)) hz0,
    lt_of_lt_of_le hz1 (zeta_le_zeta ha2 hd m2 (by omega) (by omega)), ?_⟩
  exact Prod.ext (hx.trans (zeta_zero ha1 hd m1)) rfl

/-- The switch copy on a column channel of a grid. -/
theorem lNxX_vseg {d : ℕ} (hd : 1 ≤ d) (m1 m2 : ℤ) {i j : ℕ} (hi : i < MachineM.Nd d)
    (hj : j + 1 < MachineM.Nd d) {z : ℤ} (h0 : zeta (a2 τ) d m2 j ≤ z)
    (h1 : z < zeta (a2 τ) d m2 (j + 1)) (ι : Fin 4) :
    lNxX U τ sw (zeta (a1 τ) d m1 i, z) ι =
      if i = 0 ∧ MachineM.ready U d then sw (root τ d m1 m2) ι else false := by
  have ha1 : FrameOffsets (a1 τ) := frameOffsets_phase _
  have ha2 : FrameOffsets (a2 τ) := frameOffsets_phase _
  by_cases h : i = 0 ∧ MachineM.ready U d
  · rw [if_pos h]
    obtain ⟨rfl, hr⟩ := h
    rw [zeta_zero ha1 hd]
    exact lNxX_col sw hd hr m1 m2
      (le_trans (zeta_le_zeta ha2 hd m2 (by omega) (Nat.zero_le j)) h0)
      (lt_of_lt_of_le h1 (zeta_le_zeta ha2 hd m2 (by omega) (by omega))) ι
  · rw [if_neg h, lNxX, decide_eq_false_iff_not]
    rintro ⟨d', j', ⟨hs', hr'⟩, -⟩
    have e := VSeg_unique hs'
      (⟨hd, hi, hj, m1, m2, rfl, h0, h1⟩ : VSeg τ (d, i, j) (zeta (a1 τ) d m1 i, z))
    simp only [Prod.mk.injEq] at e
    obtain ⟨rfl, rfl, -⟩ := e
    exact h ⟨rfl, hr'⟩

theorem lNxX_of_not_vseg {ξ : Plane} (h : ¬ ∃ p, VSeg τ p ξ) :
    lNxX U τ sw ξ = fun _ => false := by
  funext ι
  rw [lNxX, decide_eq_false_iff_not]
  rintro ⟨d, j, ⟨hp, -⟩, -⟩
  exact h ⟨_, hp⟩

end Eval

/-! ## Evaluation of the wire values -/

section Wires

variable (σ : Plane → Spin)

theorem wEc_arm {d : ℕ} (hd : 1 ≤ d) {m1 m2 z : ℤ} (h0 : rfree (a1 τ) d m1 ≤ z)
    (h1 : z < rfree (a1 τ) d (m1 + 1)) :
    wEc τ σ (z, rfree (a2 τ) d m2) = some (σ (root τ d m1 m2)) := by
  classical
  have hm : rowMc τ (z, rfree (a2 τ) d m2) = true := by
    unfold rowMc; exact decide_eq_true ⟨d, m2, hd, rfl⟩
  rw [wEc, if_pos hm]
  show some (σ (rootBelow (a1 τ) (rowDepth τ (rfree (a2 τ) d m2)) z, rfree (a2 τ) d m2)) = _
  rw [rowDepth_eq hd rfl, rootBelow_eq h0 h1]
  rfl

theorem wEc_unmarked {z y : ℤ} (h : ¬ ∃ d m, 1 ≤ d ∧ y = rfree (a2 τ) d m) :
    wEc τ σ (z, y) = none := by
  classical
  have hm : rowMc τ (z, y) = false := by unfold rowMc; exact decide_eq_false h
  rw [wEc, if_neg (by rw [hm]; decide)]

theorem wNc_arm {d : ℕ} (hd : 1 ≤ d) {m1 m2 z : ℤ} (h0 : rfree (a2 τ) d m2 ≤ z)
    (h1 : z < rfree (a2 τ) d (m2 + 1)) :
    wNc τ σ (rfree (a1 τ) d m1, z) = some (σ (root τ d m1 m2)) := by
  classical
  have hm : colMc τ (rfree (a1 τ) d m1, z) = true := by
    unfold colMc; exact decide_eq_true ⟨d, m1, hd, rfl⟩
  rw [wNc, if_pos hm]
  show some (σ (rfree (a1 τ) d m1, rootBelow (a2 τ) (colDepth τ (rfree (a1 τ) d m1)) z)) = _
  rw [colDepth_eq hd rfl, rootBelow_eq h0 h1]
  rfl

theorem wNc_unmarked {x z : ℤ} (h : ¬ ∃ d m, 1 ≤ d ∧ x = rfree (a1 τ) d m) :
    wNc τ σ (x, z) = none := by
  classical
  have hm : colMc τ (x, z) = false := by unfold colMc; exact decide_eq_false h
  rw [wNc, if_neg (by rw [hm]; decide)]

end Wires

/-! ## Compatibility, and the payload of `cfg` -/

theorem payVal_ext {p q : PayVal} (h1 : p.spin = q.spin) (h2 : p.wW = q.wW) (h3 : p.wE = q.wE)
    (h4 : p.wS = q.wS) (h5 : p.wN = q.wN) (h6 : p.kx = q.kx) (h7 : p.ky = q.ky)
    (h8 : p.lSx = q.lSx) (h9 : p.lNx = q.lNx) : p = q := by
  obtain ⟨_, _, _, _, _, _, _, _, _⟩ := p
  obtain ⟨_, _, _, _, _, _, _, _, _⟩ := q
  dsimp only at h1 h2 h3 h4 h5 h6 h7 h8 h9
  subst h1 h2 h3 h4 h5 h6 h7 h8 h9
  rfl

theorem compatible_payX (σ : Plane → Spin) (sw yv : Plane → Fin 4 → Bool) (ξ : Plane) :
    Compatible (bgMap U τ ξ) (payX U τ σ sw yv ξ) := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have hk : kF U τ ξ = none := Option.map_eq_none_iff.1 h
    have hng : ¬ ∃ p, GPos τ p ξ := by
      rintro ⟨p, hp⟩
      rw [kF_of U hp] at hk
      cases hk
    have hx := kxX_of_not_gpos (U := U) sw hng
    refine ⟨hx, ?_⟩
    funext ι
    show (yv ξ ι && kxX U τ sw ξ ι && gB U (bgMap U τ ξ) ι) = false
    rw [hx]
    simp
  · have hl : lNc U τ (ξ.1, ξ.2 - 1) = none := Option.map_eq_none_iff.1 h
    refine lNxX_of_not_vseg (U := U) sw ?_
    rintro ⟨p, hp⟩
    rw [lNc_of U hp] at hl
    cases hl
  · have hl : lNc U τ ξ = none := Option.map_eq_none_iff.1 h
    refine lNxX_of_not_vseg (U := U) sw ?_
    rintro ⟨p, hp⟩
    rw [lNc_of U hp] at hl
    cases hl

theorem xOf_lNc (ξ : Plane) : xOf (lNc U τ ξ) = fun _ => false := by
  unfold lNc
  split_ifs <;> rfl

theorem kF_x (ξ : Plane) : ((kF U τ ξ).map CellRec.x).getD (fun _ => false) = fun _ => false := by
  rcases h : kF U τ ξ with _ | k
  · rfl
  · exact (kF_xy U h).1

theorem kF_y (ξ : Plane) : ((kF U τ ξ).map CellRec.y).getD (fun _ => false) = fun _ => false := by
  rcases h : kF U τ ξ with _ | k
  · rfl
  · exact (kF_xy U h).2

/-- The payload of `cfg U τ σ` is the explicit payload with all switches and free bits `0`. -/
theorem payOf_cfg (σ : Plane → Spin) :
    payOf (cfg U τ σ) = payX U τ σ (fun _ _ => false) (fun _ _ => false) := by
  funext ξ
  have hk0 : kxX U τ (fun _ _ => false) ξ = fun _ => false := by
    funext ι
    rw [kxX, decide_eq_false_iff_not]
    rintro ⟨_, _, _, h⟩
    exact Bool.false_ne_true h
  have hl0 : ∀ ξ', lNxX U τ (fun _ _ => false) ξ' = fun _ => false := by
    intro ξ'
    funext ι
    rw [lNxX, decide_eq_false_iff_not]
    rintro ⟨_, _, _, h⟩
    exact Bool.false_ne_true h
  refine payVal_ext rfl rfl rfl rfl rfl ?_ ?_ ?_ ?_
  · show ((kF U τ ξ).map CellRec.x).getD _ = kxX U τ (fun _ _ => false) ξ
    rw [kF_x, hk0]
  · show ((kF U τ ξ).map CellRec.y).getD _ = _
    rw [kF_y]
    rfl
  · show xOf (lNc U τ (ξ.1, ξ.2 - 1)) = lNxX U τ (fun _ _ => false) (ξ.1, ξ.2 - 1)
    rw [xOf_lNc, hl0]
  · show xOf (lNc U τ ξ) = lNxX U τ (fun _ _ => false) ξ
    rw [xOf_lNc, hl0]

theorem cfg_eq_assemble (σ : Plane → Spin) :
    cfg U τ σ = assemble (bgMap U τ) (payX U τ σ (fun _ _ => false) (fun _ _ => false)) := by
  rw [← payOf_cfg σ, ← bgOf_cfg τ σ]
  exact (assemble_split (cfg U τ σ)).symm

theorem cfg_site (σ : Plane → Spin) (ξ : Plane) :
    cfg U τ σ ξ = merge (bgMap U τ ξ) (payX U τ σ (fun _ _ => false) (fun _ _ => false) ξ) :=
  congrFun (cfg_eq_assemble σ) ξ


/-! ## Transfer: the rules that read no switch or free bit -/

section Transfer

variable {b : BgVal U} {p p' : PayVal}

theorem merge_lS : (merge b p).lS = b.lS.map (fun l => l.withX p.lSx) := rfl

theorem merge_lN : (merge b p).lN = b.lN.map (fun l => l.withX p.lNx) := rfl

theorem merge_k : (merge b p).k = b.k.map (fun c => c.withXY p.kx p.ky) := rfl

theorem onColour_map {α β : Type} (o : Option α) (f : α → β) (P : β → Prop) :
    OnColour (o.map f) P ↔ OnColour o (fun a => P (f a)) := by
  cases o with
  | none => exact ⟨fun _ => onColour_none, fun _ => onColour_none⟩
  | some a => exact ⟨fun h => onColour_some (h _ rfl), fun h => onColour_some (h _ rfl)⟩

variable {c : CellRecB U} {x y x' y' : Fin 4 → Bool}

theorem C0_merge (h : (merge b p').C0) : (merge b p).C0 := by
  unfold SiteVal.C0 at h ⊢
  simp only [merge_lS, merge_lN, Option.map_eq_none_iff] at h ⊢
  exact h

theorem C1_merge (h : (merge b p').C1 (c.withXY x' y')) : (merge b p).C1 (c.withXY x y) := by
  unfold SiteVal.C1 at h ⊢
  simp only [merge_lS, merge_lN, onColour_map] at h ⊢
  exact h

theorem C2_merge (h : (merge b p').C2 (c.withXY x' y')) : (merge b p).C2 (c.withXY x y) := by
  unfold SiteVal.C2 at h ⊢
  simp only [merge_lS, merge_lN, onColour_map] at h ⊢
  exact h

theorem C3_merge (h : (merge b p').C3 (c.withXY x' y')) : (merge b p).C3 (c.withXY x y) := by
  unfold SiteVal.C3 at h ⊢
  simp only [merge_lS, merge_lN, onColour_map] at h ⊢
  exact h

theorem C4_merge (h : (merge b p').C4 (c.withXY x' y')) : (merge b p).C4 (c.withXY x y) := h

theorem C5_merge (h : (merge b p').C5 (c.withXY x' y')) : (merge b p).C5 (c.withXY x y) := by
  unfold SiteVal.C5 at h ⊢
  simp only [merge_lS, merge_lN, onColour_map] at h ⊢
  exact h

theorem C6_merge (h : (merge b p').C6 (c.withXY x' y')) : (merge b p).C6 (c.withXY x y) := by
  unfold SiteVal.C6 at h ⊢
  simp only [merge_lS, merge_lN, onColour_map] at h ⊢
  exact h

theorem C7_merge (h : (merge b p').C7 (c.withXY x' y')) : (merge b p).C7 (c.withXY x y) := h

theorem P1_merge (h : (merge b p').P1) (h1 : p.spin = p'.spin) (h2 : p.wW = p'.wW)
    (h3 : p.wE = p'.wE) : (merge b p).P1 := by
  obtain ⟨_, _, _, _, _, _, _, _, _⟩ := p
  obtain ⟨_, _, _, _, _, _, _, _, _⟩ := p'
  dsimp only at h1 h2 h3
  subst h1 h2 h3
  exact h

theorem P2_merge (h : (merge b p').P2) (h1 : p.spin = p'.spin) (h2 : p.wS = p'.wS)
    (h3 : p.wN = p'.wN) : (merge b p).P2 := by
  obtain ⟨_, _, _, _, _, _, _, _, _⟩ := p
  obtain ⟨_, _, _, _, _, _, _, _, _⟩ := p'
  dsimp only at h1 h2 h3
  subst h1 h2 h3
  exact h

/-- **Transfer**: a site value `(b, p)` is allowed if `(b, p')` is, `p` and `p'` have the same spin
and wire values, and (K2) (for the `x` of the vertical colours), (C8), (C9) and (P3) hold for
`(b, p)`. -/
theorem allowed_merge (h : (merge b p').Allowed) (h1 : p.spin = p'.spin) (hW : p.wW = p'.wW)
    (hE : p.wE = p'.wE) (hS : p.wS = p'.wS) (hN : p.wN = p'.wN)
    (hK2 : (merge b p).IsVertical → b.lN ≠ none → p.lSx = p.lNx)
    (hC8 : ∀ c, b.k = some c → (merge b p).IsActive → (merge b p).C8 (c.withXY p.kx p.ky))
    (hC9 : ∀ c, b.k = some c → (merge b p).IsActive → (merge b p).C9 (c.withXY p.kx p.ky))
    (hP3 : (merge b p).P3) : (merge b p).Allowed := by
  obtain ⟨o1, o2, e1, e2, e3, k1, k2, k3, q1, q2, p1, p2, -⟩ := h
  refine ⟨o1, o2, e1, e2, e3, k1, ⟨fun hv => ?_, fun hv => ?_⟩, ⟨fun ha => ?_, fun ha => ?_⟩,
    q1, q2, P1_merge p1 h1 hW hE, P2_merge p2 h1 hS hN, hP3⟩
  · obtain ⟨hS0, hN0⟩ := k2.1 hv
    rw [merge_lS, Option.map_eq_none_iff] at hS0
    rw [merge_lN, Option.map_eq_none_iff] at hN0
    rw [merge_lS, merge_lN, hS0, hN0]
    exact ⟨rfl, rfl⟩
  · have e := k2.2 hv
    rw [merge_lS, merge_lN] at e ⊢
    revert e
    rcases hbS : b.lS with _ | lS <;> rcases hbN : b.lN with _ | lN <;> intro e
    · rfl
    · cases e
    · cases e
    · have e' : lS = lN := congrArg VCol.bg (Option.some.inj e)
      subst e'
      rw [hK2 hv (by rw [hbN]; exact Option.some_ne_none _)]
  · have e := k3.1 ha
    rw [merge_k, Option.map_eq_none_iff] at e
    rw [merge_k, e]
    rfl
  · obtain ⟨k0, hk0, c0, c1, c2, c3, c4, c5, c6, c7, -, -⟩ := k3.2 ha
    rw [merge_k] at hk0
    obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.1 hk0
    exact ⟨c.withXY p.kx p.ky, by rw [merge_k, hc]; rfl, C0_merge c0, C1_merge c1, C2_merge c2,
      C3_merge c3, C4_merge c4, C5_merge c5, C6_merge c6, C7_merge c7, hC8 c hc ha, hC9 c hc ha⟩

end Transfer

/-! ## Explicit ⇒ legal -/

theorem bool_and3 {y x g : Bool} (h : ¬ (x = true ∧ g = true)) : (y && x && g) = false := by
  cases x <;> cases g <;> simp_all

section Explicit

theorem bgMap_k_gsite {d : ℕ} (hd : 1 ≤ d) (m1 m2 : ℤ) {i j : ℕ} (hi : i < MachineM.Nd d)
    (hj : j < MachineM.Nd d) :
    (bgMap U τ (gsite τ d m1 m2 i j)).k = some (cellFormula U d i j) := by
  show (kF U τ (gsite τ d m1 m2 i j)).map CellRec.bg = _
  rw [k_gsite U hd m1 m2 hi hj]
  rfl

theorem bgMap_lN_gsite {d : ℕ} (hd : 1 ≤ d) (m1 m2 : ℤ) {i j : ℕ} (hi : i < MachineM.Nd d)
    (hj : j < MachineM.Nd d) (h : (bgMap U τ (gsite τ d m1 m2 i j)).lN ≠ none) :
    j + 1 < MachineM.Nd d := by
  by_contra hc
  apply h
  show (lNc U τ (gsite τ d m1 m2 i j)).map VCol.bg = none
  rw [lN_gsite U hd m1 m2 hi hj, if_neg hc]
  rfl

section Grid

variable (σ : Plane → Spin) (sw yv : Plane → Fin 4 → Bool) {d : ℕ} (hd : 1 ≤ d) (m1 m2 : ℤ)
  {i j : ℕ} (hi : i < MachineM.Nd d) (hj : j < MachineM.Nd d) (ι : Fin 4)
include hd hi hj

theorem payX_kx_grid : (payX U τ σ sw yv (gsite τ d m1 m2 i j)).kx ι =
    if i = 0 ∧ MachineM.ready U d then sw (root τ d m1 m2) ι else false :=
  kxX_gpos sw hd m1 m2 hi hj ι

theorem payX_lNx_grid (hj1 : j + 1 < MachineM.Nd d) :
    (payX U τ σ sw yv (gsite τ d m1 m2 i j)).lNx ι =
      if i = 0 ∧ MachineM.ready U d then sw (root τ d m1 m2) ι else false := by
  have ha2 : FrameOffsets (a2 τ) := frameOffsets_phase _
  exact lNxX_vseg sw hd m1 m2 hi hj1 (z := zeta (a2 τ) d m2 j) le_rfl
    ((zeta_lt_iff ha2 hd m2 hj hj1).2 (by omega)) ι

theorem payX_lSx_grid (hj0 : j ≠ 0) :
    (payX U τ σ sw yv (gsite τ d m1 m2 i j)).lSx ι =
      if i = 0 ∧ MachineM.ready U d then sw (root τ d m1 m2) ι else false := by
  have ha2 : FrameOffsets (a2 τ) := frameOffsets_phase _
  have hpos : 0 < j := Nat.pos_of_ne_zero hj0
  have hlt := (zeta_lt_iff ha2 hd m2 (show j - 1 < MachineM.Nd d by omega) hj).2 (by omega)
  have e : zeta (a2 τ) d m2 (j - 1 + 1) = zeta (a2 τ) d m2 j := by rw [Nat.sub_add_cancel hpos]
  show lNxX U τ sw (zeta (a1 τ) d m1 i, zeta (a2 τ) d m2 j - 1) ι = _
  exact lNxX_vseg sw hd m1 m2 hi (j := j - 1) (by omega) (by omega) (by rw [e]; omega) ι

end Grid

variable (hτ : Typical τ) (σ : Plane → Spin) (sw yv : Plane → Fin 4 → Bool)
include hτ

theorem allowed_payX (h3 : P3X U τ σ sw) (ξ : Plane) :
    (merge (bgMap U τ ξ) (payX U τ σ sw yv ξ)).Allowed := by
  have ha1 : FrameOffsets (a1 τ) := frameOffsets_phase _
  have ha2 : FrameOffsets (a2 τ) := frameOffsets_phase _
  have h0 : (merge (bgMap U τ ξ) (payX U τ σ (fun _ _ => false) (fun _ _ => false) ξ)).Allowed := by
    rw [← cfg_site]; exact cfg_allowed hτ σ ξ
  have hgrid : (merge (bgMap U τ ξ) (payX U τ σ sw yv ξ)).IsActive →
      ∃ d m1 m2 i j, 1 ≤ d ∧ i < MachineM.Nd d ∧ j < MachineM.Nd d ∧
        ξ = gsite τ d m1 m2 i j := by
    intro ha
    have ha' : (cfg U τ σ ξ).IsActive := by rw [cfg_site]; exact ha
    obtain ⟨d, m1, m2, hd, h1, h2⟩ := (cfg_active hτ σ ξ).1 ha'
    obtain ⟨i, j, hi, hj, e⟩ := (mem_grid_iff hd).1 ⟨h1, h2⟩
    exact ⟨d, m1, m2, i, j, hd, hi, hj, e⟩
  refine allowed_merge h0 rfl rfl rfl rfl rfl ?_ ?_ ?_ ?_
  · -- (K2): the copies of the switches along a column channel
    intro hv hne
    have hne' : lNc U τ ξ ≠ none := fun h => hne (by
      show (lNc U τ ξ).map VCol.bg = none
      rw [h]; rfl)
    obtain ⟨⟨d, i, j⟩, hseg⟩ : ∃ q, VSeg τ q ξ := by
      by_contra hc; exact hne' (lNc_none U hc)
    obtain ⟨hd, hi, hj, m1, m2, hx, hz0, hz1⟩ := hseg
    simp only at hd hi hj hx hz0 hz1
    have hlt : zeta (a2 τ) d m2 j < ξ.2 := by
      rcases hz0.lt_or_eq with h | h
      · exact h
      · exfalso
        have ha : (cfg U τ σ ξ).IsActive := (cfg_active hτ σ ξ).2
          ⟨d, m1, m2, hd, by rw [hx]; exact zeta_free ha1 hd m1 hi,
            by rw [← h]; exact zeta_free ha2 hd m2 (by omega)⟩
        rw [cfg_site] at ha
        exact hv.2 ha.1
    obtain ⟨x, z⟩ := ξ
    simp only at hx hz0 hz1 hlt
    subst hx
    funext ι
    show lNxX U τ sw (zeta (a1 τ) d m1 i, z - 1) ι = lNxX U τ sw (zeta (a1 τ) d m1 i, z) ι
    rw [lNxX_vseg sw hd m1 m2 hi hj (by omega) (by omega), lNxX_vseg sw hd m1 m2 hi hj hz0 hz1]
  · -- (C8)
    intro c hc ha
    obtain ⟨d, m1, m2, i, j, hd, hi, hj, rfl⟩ := hgrid ha
    rw [bgMap_k_gsite hd m1 m2 hi hj] at hc
    obtain rfl : cellFormula U d i j = c := Option.some.inj hc
    obtain ⟨fW, -, fS, -⟩ := cfg_grids_c (U := U) hτ σ hd m1 m2 hi hj
    rw [cfg_site] at fW fS
    have fW' : (merge (bgMap U τ (gsite τ d m1 m2 i j)) (payX U τ σ sw yv (gsite τ d m1 m2 i j))).fW
        = decide (i = 0) := fW
    have fS' : (merge (bgMap U τ (gsite τ d m1 m2 i j)) (payX U τ σ sw yv (gsite τ d m1 m2 i j))).fS
        = decide (j = 0) := fS
    intro ι
    have hkx := payX_kx_grid (U := U) (τ := τ) σ sw yv hd m1 m2 hi hj ι
    refine ⟨fun hW => ⟨?_, ?_⟩, fun hWS hr => ?_, fun hWS => ?_, fun hW => ?_⟩
    · rw [fW', decide_eq_false_iff_not] at hW
      show (payX U τ σ sw yv (gsite τ d m1 m2 i j)).kx ι = false
      rw [hkx, if_neg (fun h => hW h.1)]
    · rw [fW', decide_eq_false_iff_not] at hW
      rw [merge_lN, onColour_map]
      intro l hl
      have hj1 := bgMap_lN_gsite hd m1 m2 hi hj (by rw [hl]; exact Option.some_ne_none _)
      show (payX U τ σ sw yv (gsite τ d m1 m2 i j)).lNx ι = false
      rw [payX_lNx_grid σ sw yv hd m1 m2 hi hj ι hj1, if_neg (fun h => hW h.1)]
    · have hnr : ¬ MachineM.ready U d := by
        have e : decide (MachineM.ready U d) = false := hr
        exact of_decide_eq_false e
      show (payX U τ σ sw yv (gsite τ d m1 m2 i j)).kx ι = false
      rw [hkx, if_neg (fun h => hnr h.2)]
    · obtain ⟨hW, hS⟩ := hWS
      rw [fS', decide_eq_false_iff_not] at hS
      rw [merge_lS, onColour_map]
      intro l hl
      show (payX U τ σ sw yv (gsite τ d m1 m2 i j)).kx ι =
        (payX U τ σ sw yv (gsite τ d m1 m2 i j)).lSx ι
      rw [hkx, payX_lSx_grid σ sw yv hd m1 m2 hi hj ι hS]
    · rw [merge_lN, onColour_map]
      intro l hl
      have hj1 := bgMap_lN_gsite hd m1 m2 hi hj (by rw [hl]; exact Option.some_ne_none _)
      show (payX U τ σ sw yv (gsite τ d m1 m2 i j)).lNx ι =
        (payX U τ σ sw yv (gsite τ d m1 m2 i j)).kx ι
      rw [hkx, payX_lNx_grid σ sw yv hd m1 m2 hi hj ι hj1]
  · -- (C9)
    intro c hc ha
    have hg : ∀ ι, gB U (bgMap U τ ξ) ι = SiteVal.gOf (c.withXY (payX U τ σ sw yv ξ).kx
        (payX U τ σ sw yv ξ).ky) ι := by
      intro ι; unfold gB; rw [hc]; rfl
    obtain ⟨d, m1, m2, i, j, hd, hi, hj, rfl⟩ := hgrid ha
    obtain ⟨fW, -, -, -⟩ := cfg_grids_c (U := U) hτ σ hd m1 m2 hi hj
    rw [cfg_site] at fW
    have fW' : (merge (bgMap U τ (gsite τ d m1 m2 i j)) (payX U τ σ sw yv (gsite τ d m1 m2 i j))).fW
        = decide (i = 0) := fW
    refine ⟨fun hW ι => ?_, fun _ ι hn => ?_⟩
    · rw [fW', decide_eq_false_iff_not] at hW
      have hkx := payX_kx_grid (U := U) (τ := τ) σ sw yv hd m1 m2 hi hj ι
      rw [if_neg (fun h => hW h.1)] at hkx
      show (yv _ ι && kxX U τ sw (gsite τ d m1 m2 i j) ι &&
        gB U (bgMap U τ (gsite τ d m1 m2 i j)) ι) = false
      have hkx' : kxX U τ sw (gsite τ d m1 m2 i j) ι = false := hkx
      rw [hkx']
      simp
    · show (yv _ ι && kxX U τ sw (gsite τ d m1 m2 i j) ι &&
        gB U (bgMap U τ (gsite τ d m1 m2 i j)) ι) = false
      rw [hg ι]
      exact bool_and3 hn
  · -- (P3)
    intro hr k hk hrdy
    have hr' : (cfg U τ σ ξ).IsRoot := by rw [cfg_site]; exact hr
    obtain ⟨d, m1, m2, hd, rfl⟩ := (cfg_isRoot hτ σ ξ).1 hr'
    have h0' : 0 < MachineM.Nd d := by have := MachineM.two_le_Nd d; omega
    have hbk : (bgMap U τ (root τ d m1 m2)).k = some (cellFormula U d 0 0) := by
      rw [← gsite_zero hd]; exact bgMap_k_gsite hd m1 m2 h0' h0'
    rw [merge_k, hbk] at hk
    obtain rfl := Option.some.inj hk
    have hready : MachineM.ready U d := of_decide_eq_true hrdy
    have hkx : ∀ ι, (payX U τ σ sw yv (root τ d m1 m2)).kx ι = sw (root τ d m1 m2) ι := by
      intro ι
      have := kxX_gsite (τ := τ) sw hd hready m1 m2 h0' ι
      rw [gsite_zero hd] at this
      exact this
    have hP : (0 : ℤ) < 4 ^ (d + 1) := by positivity
    have hW : (payX U τ σ sw yv (root τ d m1 m2)).wW = some (σ (root τ d (m1 - 1) m2)) := by
      show wEc τ σ (rfree (a1 τ) d m1 - 1, rfree (a2 τ) d m2) = _
      have e := rfree_succ (a1 τ) d (m1 - 1)
      rw [sub_add_cancel] at e
      exact wEc_arm σ hd (by linarith) (by rw [sub_add_cancel]; linarith)
    have hS : (payX U τ σ sw yv (root τ d m1 m2)).wS = some (σ (root τ d m1 (m2 - 1))) := by
      show wNc τ σ (rfree (a1 τ) d m1, rfree (a2 τ) d m2 - 1) = _
      have e := rfree_succ (a2 τ) d (m2 - 1)
      rw [sub_add_cancel] at e
      exact wNc_arm σ hd (by linarith) (by rw [sub_add_cancel]; linarith)
    obtain ⟨hP3h, hP3v⟩ := h3 d m1 m2 hd hready
    refine ⟨fun hx => ?_, fun hx => ?_⟩
    · have hx' : sw (root τ d m1 m2) 0 = false ∧ sw (root τ d m1 m2) 1 = true := by
        rw [← hkx, ← hkx]; exact hx
      show (payX U τ σ sw yv (root τ d m1 m2)).wW = some (σ (root τ d m1 m2))
      rw [hW, hP3h hx']
    · have hx' : sw (root τ d m1 m2) 2 = false ∧ sw (root τ d m1 m2) 3 = true := by
        rw [← hkx, ← hkx]; exact hx
      show (payX U τ σ sw yv (root τ d m1 m2)).wS = some (σ (root τ d m1 m2))
      rw [hS, hP3v hx']

theorem matchH_payX (ξ : Plane) :
    (merge (bgMap U τ ξ) (payX U τ σ sw yv ξ)).cE =
      (merge (bgMap U τ (ξ + e1)) (payX U τ σ sw yv (ξ + e1))).cW := by
  have h := cfg_matchH (U := U) hτ σ ξ
  rw [cfg_site, cfg_site] at h
  obtain ⟨hb, hw⟩ := (cE_eq_cW_iff _ _).1 h
  rw [bgPart_merge, bgPart_merge] at hb
  exact (cE_eq_cW_iff _ _).2 ⟨by rw [bgPart_merge, bgPart_merge]; exact hb, hw⟩

theorem matchV_payX (ξ : Plane) :
    (merge (bgMap U τ ξ) (payX U τ σ sw yv ξ)).cN =
      (merge (bgMap U τ (ξ + e2)) (payX U τ σ sw yv (ξ + e2))).cS := by
  obtain ⟨x, z⟩ := ξ
  have h := cfg_matchV (U := U) hτ σ (x, z)
  rw [cfg_site, cfg_site] at h
  obtain ⟨hb, hw, -⟩ := (cN_eq_cS_iff _ _).1 h
  rw [bgPart_merge, bgPart_merge] at hb
  have hl : (bgMap U τ (x, z)).lN = (bgMap U τ ((x, z) + e2)).lS :=
    congrArg (fun t => t.2.2.2.1) hb
  refine (cN_eq_cS_iff _ _).2 ⟨by rw [bgPart_merge, bgPart_merge]; exact hb, hw, ?_⟩
  have e : (payX U τ σ sw yv ((x, z) + e2)).lSx = (payX U τ σ sw yv (x, z)).lNx := by
    show lNxX U τ sw (((x, z) + e2).1, ((x, z) + e2).2 - 1) = lNxX U τ sw (x, z)
    rw [add_e2]
    simp only [add_sub_cancel_right]
  rw [merge_lN, merge_lS, hl, e]

/-- **`pay:factor`, explicit ⇒ legal**: for typical `τ`, every explicit payload whose free data
satisfy (P3) at the roots of the ready grids is a legal payload of `𝔟_τ`. -/
theorem legal_payX (h3 : P3X U τ σ sw) :
    IsLegal (Phi U) (assemble (bgMap U τ) (payX U τ σ sw yv)) :=
  legal_of (fun ξ => allowed_payX hτ σ sw yv h3 ξ) (fun ξ => matchH_payX hτ σ sw yv ξ)
    (fun ξ => matchV_payX hτ σ sw yv ξ)

end Explicit


/-! ## Legal ⇒ explicit -/

section LegalExplicit

variable {ω : Config (SiteVal U)}

/-- (P1) with matching along a row: the wire values `w^E` are the spins at the nearest roots at or
west of the sites, and `□` off the marked rows. -/
theorem wE_legal (hs : Setting ω τ) (ξ : Plane) :
    (ω ξ).wE = wEc τ (fun ξ => (ω ξ).spin) ξ := by
  classical
  have ha2 : FrameOffsets (a2 τ) := frameOffsets_phase _
  obtain ⟨z, y⟩ := ξ
  by_cases hm : ∃ d m, 1 ≤ d ∧ y = rfree (a2 τ) d m
  · obtain ⟨d, m2, hd, hy⟩ := hm
    have hrow : ∀ z', (ω (z', y)).rowM = true := fun z' =>
      (hs.markers_a_row (z', y)).2 ⟨d, m2, hd, hy⟩
    have hmk : rowMc τ (z, y) = true := by unfold rowMc; exact decide_eq_true ⟨d, m2, hd, hy⟩
    rw [wEc, if_pos hmk]
    show (ω (z, y)).wE = some ((ω (rootBelow (a1 τ) (rowDepth τ y) z, y)).spin)
    rw [rowDepth_eq hd hy]
    refine wire_line (f := fun z => (ω (z, y)).wE) (s := fun z => (ω (z, y)).spin)
      (fun m => ?_) (fun z' hz' => ?_) z
    · exact ((hs.P1 _).2 (hrow _)).2.2.1 ((hs.isRoot_iff _).2 ⟨d, m, m2, hd, by rw [hy]; rfl⟩)
    · have hnr : ¬ (ω (z', y)).IsRoot := by
        intro hr
        obtain ⟨d', m1, m2', hd', he⟩ := (hs.isRoot_iff _).1 hr
        simp only [root, Prod.mk.injEq] at he
        have e : d' = d := rfree_depth_unique ha2 (he.2.symm.trans hy)
        subst e
        exact hz' m1 he.1
      show (ω (z', y)).wE = (ω (z' - 1, y)).wE
      rw [((hs.P1 _).2 (hrow _)).2.2.2 hnr, hs.wE_eq (z' - 1) y, sub_add_cancel]
  · have hmk : rowMc τ (z, y) = false := by unfold rowMc; exact decide_eq_false hm
    rw [wEc, if_neg (by rw [hmk]; decide)]
    have h0 : (ω (z, y)).rowM = false := by
      rcases h : (ω (z, y)).rowM
      · rfl
      · exact absurd ((hs.markers_a_row (z, y)).1 h) hm
    exact ((hs.P1 _).1 h0).2

/-- (P2) with matching along a column. -/
theorem wN_legal (hs : Setting ω τ) (ξ : Plane) :
    (ω ξ).wN = wNc τ (fun ξ => (ω ξ).spin) ξ := by
  classical
  have ha1 : FrameOffsets (a1 τ) := frameOffsets_phase _
  obtain ⟨x, z⟩ := ξ
  by_cases hm : ∃ d m, 1 ≤ d ∧ x = rfree (a1 τ) d m
  · obtain ⟨d, m1, hd, hx⟩ := hm
    have hcol : ∀ z', (ω (x, z')).colM = true := fun z' =>
      (hs.markers_a_col (x, z')).2 ⟨d, m1, hd, hx⟩
    have hmk : colMc τ (x, z) = true := by unfold colMc; exact decide_eq_true ⟨d, m1, hd, hx⟩
    rw [wNc, if_pos hmk]
    show (ω (x, z)).wN = some ((ω (x, rootBelow (a2 τ) (colDepth τ x) z)).spin)
    rw [colDepth_eq hd hx]
    refine wire_line (f := fun z => (ω (x, z)).wN) (s := fun z => (ω (x, z)).spin)
      (fun m => ?_) (fun z' hz' => ?_) z
    · exact ((hs.P2 _).2 (hcol _)).2.2.1 ((hs.isRoot_iff _).2 ⟨d, m1, m, hd, by rw [hx]; rfl⟩)
    · have hnr : ¬ (ω (x, z')).IsRoot := by
        intro hr
        obtain ⟨d', m1', m2, hd', he⟩ := (hs.isRoot_iff _).1 hr
        simp only [root, Prod.mk.injEq] at he
        have e : d' = d := rfree_depth_unique ha1 (he.1.symm.trans hx)
        subst e
        exact hz' m2 he.2
      show (ω (x, z')).wN = (ω (x, z' - 1)).wN
      rw [((hs.P2 _).2 (hcol _)).2.2.2 hnr, hs.wN_eq x (z' - 1), sub_add_cancel]
  · have hmk : colMc τ (x, z) = false := by unfold colMc; exact decide_eq_false hm
    rw [wNc, if_neg (by rw [hmk]; decide)]
    have h0 : (ω (x, z)).colM = false := by
      rcases h : (ω (x, z)).colM
      · rfl
      · exact absurd ((hs.markers_a_col (x, z)).1 h) hm
    exact ((hs.P2 _).1 h0).2

section Grid

variable (hs : Setting ω τ) {d : ℕ} (hd : 1 ≤ d) (m1 m2 : ℤ)
include hs hd

/-- (K2) and matching along a column channel: `ℓ^N` is constant on `[ζ_j, ζ_{j+1})`. -/
theorem lN_chan {i j : ℕ} (hi : i < MachineM.Nd d) (hj : j + 1 < MachineM.Nd d) {z : ℤ}
    (h0 : zeta (a2 τ) d m2 j ≤ z) (h1 : z < zeta (a2 τ) d m2 (j + 1)) :
    (ω (zeta (a1 τ) d m1 i, z)).lN = (ω (gsite τ d m1 m2 i j)).lN := by
  refine const_up (f := fun z => (ω (zeta (a1 τ) d m1 i, z)).lN) (fun z' h0' h1' => ?_) z h0 h1
  show (ω (zeta (a1 τ) d m1 i, z')).lN = (ω (zeta (a1 τ) d m1 i, z' - 1)).lN
  have hv := hs.grids_a_v hd m1 m2 hi hj h0' h1'
  rw [← (hs.K2 _).2 hv, hs.lN_eq _ (z' - 1), sub_add_cancel]

/-- (C8) at `ξ(i, j)`: the `x` of `ℓ^N` is the switch of the record on a first column and `0`
elsewhere. -/
theorem lNx_grid {i j : ℕ} (hi : i < MachineM.Nd d) (hj : j + 1 < MachineM.Nd d) :
    xOf (ω (gsite τ d m1 m2 i j)).lN =
      if i = 0 then (payOf ω (gsite τ d m1 m2 i j)).kx else fun _ => false := by
  obtain ⟨hk, -, -, -, -, -, -, -, -, c8, -⟩ :=
    hs.rules hd m1 m2 hi (show j < MachineM.Nd d by omega)
  obtain ⟨fW, -, -, -⟩ := hs.grids_c hd m1 m2 hi (show j < MachineM.Nd d by omega)
  obtain ⟨l, hl, -⟩ := hs.chanV_some hd m1 m2 hi hj
  have hkx : (payOf ω (gsite τ d m1 m2 i j)).kx = (cellAt ω τ d m1 m2 i j).x := by
    show (((ω (gsite τ d m1 m2 i j)).k).map CellRec.x).getD _ = _
    rw [hk]; rfl
  rw [hl, hkx]
  funext ι
  show l.x ι = _
  by_cases h0 : i = 0
  · rw [if_pos h0]
    exact (c8 ι).2.2.2 (by rw [fW]; simp [h0]) l hl
  · rw [if_neg h0]
    exact ((c8 ι).1 (by rw [fW]; simp [h0])).2 l hl

/-- (C8) with (K2) and matching: the switch copies along the first column equal the switch at the
root. -/
theorem kx_col : ∀ j, j < MachineM.Nd d →
    (payOf ω (gsite τ d m1 m2 0 j)).kx = (payOf ω (root τ d m1 m2)).kx := by
  have h0 : 0 < MachineM.Nd d := by have := MachineM.two_le_Nd d; omega
  intro j hj
  induction j with
  | zero => rw [gsite_zero hd]
  | succ j ih =>
    rw [← ih (by omega)]
    obtain ⟨hk, -, -, -, -, -, -, -, -, c8, -⟩ := hs.rules hd m1 m2 h0 hj
    obtain ⟨fW, -, fS, -⟩ := hs.grids_c hd m1 m2 h0 hj
    obtain ⟨l, hl, hl'⟩ := hs.chanV_some hd m1 m2 h0 hj
    have e := lNx_grid hs hd m1 m2 h0 hj
    rw [if_pos rfl, hl] at e
    rw [← e]
    show (((ω (gsite τ d m1 m2 0 (j + 1))).k).map CellRec.x).getD _ = l.x
    rw [hk]
    funext ι
    exact (c8 ι).2.2.1 ⟨by rw [fW]; rfl, by rw [fS]; simp⟩ l hl'

/-- (C8) at the root of a grid that is not ready: the switches are `0`. -/
theorem kx_root (hr : ¬ MachineM.ready U d) :
    (payOf ω (root τ d m1 m2)).kx = fun _ => false := by
  have h0 : 0 < MachineM.Nd d := by have := MachineM.two_le_Nd d; omega
  obtain ⟨hk, -, -, -, -, -, -, -, -, c8, -⟩ := hs.rules hd m1 m2 h0 h0
  obtain ⟨fW, -, fS, -⟩ := hs.grids_c hd m1 m2 h0 h0
  have hrdy := hs.grid_rdy hd m1 m2 h0 h0
  rw [← gsite_zero hd]
  show (((ω (gsite τ d m1 m2 0 0)).k).map CellRec.x).getD _ = _
  rw [hk]
  funext ι
  exact (c8 ι).2.1 ⟨by rw [fW]; rfl, by rw [fS]; rfl⟩ (by rw [hrdy]; exact decide_eq_false hr)

end Grid

/-- **The switch copies of a legal payload of `𝔟_τ`** are the explicit ones built from the
switches at the roots. -/
theorem kx_legal (hs : Setting ω τ) (ξ : Plane) :
    (payOf ω ξ).kx = kxX U τ (fun ξ => (payOf ω ξ).kx) ξ := by
  funext ι
  rcases hk : (ω ξ).k with _ | c
  · have e : (payOf ω ξ).kx = fun _ => false := by
      show (((ω ξ).k).map CellRec.x).getD _ = _
      rw [hk]; rfl
    rw [e, kxX_eq_false]
    rintro ⟨d, m1, m2, j, hd, -, hj, rfl⟩
    rw [(hs.rules hd m1 m2 (by have := MachineM.two_le_Nd d; omega) hj).1] at hk
    cases hk
  · have hact : (ω ξ).IsActive := by
      by_contra hna
      rw [(hs.K3 ξ).1 hna] at hk
      cases hk
    obtain ⟨d, m1, m2, i, j, hd, hi, hj, rfl⟩ := hs.active_grid hact
    rw [kxX_gpos _ hd m1 m2 hi hj]
    by_cases h : i = 0 ∧ MachineM.ready U d
    · rw [if_pos h]
      obtain ⟨rfl, -⟩ := h
      rw [kx_col hs hd m1 m2 j hj]
    · rw [if_neg h]
      by_cases hi0 : i = 0
      · subst hi0
        rw [kx_col hs hd m1 m2 j hj, kx_root hs hd m1 m2 (fun hr => h ⟨rfl, hr⟩)]
      · obtain ⟨hk', -, -, -, -, -, -, -, -, c8, -⟩ := hs.rules hd m1 m2 hi hj
        obtain ⟨fW, -, -, -⟩ := hs.grids_c hd m1 m2 hi hj
        show (((ω (gsite τ d m1 m2 i j)).k).map CellRec.x).getD _ ι = false
        rw [hk']
        exact ((c8 ι).1 (by rw [fW]; simp [hi0])).1

/-- **The switch copies on the columns of a legal payload of `𝔟_τ`** are the explicit ones. -/
theorem lNx_legal (hs : Setting ω τ) (hb : bgOf ω = bgMap U τ) (ξ : Plane) :
    (payOf ω ξ).lNx = lNxX U τ (fun ξ => (payOf ω ξ).kx) ξ := by
  have ha1 : FrameOffsets (a1 τ) := frameOffsets_phase _
  have ha2 : FrameOffsets (a2 τ) := frameOffsets_phase _
  funext ι
  obtain ⟨x, z⟩ := ξ
  rcases hl : (ω (x, z)).lN with _ | l
  · show (xOf (ω (x, z)).lN) ι = _
    rw [hl]
    symm
    apply lNxX_eq_false
    rintro ⟨d, m1, m2, z', hd, -, h0, h1, e⟩
    simp only [Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    obtain ⟨j, hj, hz0, hz1⟩ := exists_zeta_interval m2 h0 h1
    have h0' : 0 < MachineM.Nd d := by omega
    have hc := lN_chan hs hd m1 m2 h0' hj hz0 hz1
    rw [zeta_zero ha1 hd] at hc
    obtain ⟨l', hl', -⟩ := hs.chanV_some hd m1 m2 h0' hj
    rw [hc, hl'] at hl
    cases hl
  · have hne : lNc U τ (x, z) ≠ none := by
      intro h
      have e : (ω (x, z)).lN.map VCol.bg = (lNc U τ (x, z)).map VCol.bg :=
        congrArg BgVal.lN (congrFun hb (x, z))
      rw [hl, h] at e
      cases e
    obtain ⟨⟨d, i, j⟩, hseg⟩ : ∃ p, VSeg τ p (x, z) := by
      by_contra hc; exact hne (lNc_none U hc)
    obtain ⟨hd, hi, hj, m1, m2, hx, hz0, hz1⟩ := hseg
    simp only at hd hi hj hx hz0 hz1
    subst hx
    rw [lNxX_vseg _ hd m1 m2 hi hj hz0 hz1]
    have hc := lN_chan hs hd m1 m2 hi hj hz0 hz1
    have hg := lNx_grid hs hd m1 m2 hi hj
    show (xOf (ω (zeta (a1 τ) d m1 i, z)).lN) ι = _
    rw [hc, hg]
    by_cases h : i = 0 ∧ MachineM.ready U d
    · obtain ⟨rfl, hr⟩ := h
      rw [if_pos rfl, if_pos ⟨rfl, hr⟩, kx_col hs hd m1 m2 j (by omega)]
    · rw [if_neg h]
      by_cases hi0 : i = 0
      · subst hi0
        rw [if_pos rfl, kx_col hs hd m1 m2 j (by omega),
          kx_root hs hd m1 m2 (fun hr => h ⟨rfl, hr⟩)]
      · rw [if_neg hi0]

theorem bool_y {y x g : Bool} (h : ¬ (x = true ∧ g = true) → y = false) :
    y = (y && x && g) := by
  cases y <;> cases x <;> cases g <;> simp_all

/-- **`pay:factor`(a), (b), legal ⇒ explicit**: for typical `τ`, the payload of a legal
configuration with background `𝔟_τ` is the explicit payload built from its spins, the switches at
the roots and its free bits. -/
theorem payOf_eq_payX (hτ : Typical τ) (hω : IsLegal (Phi U) ω) (hb : bgOf ω = bgMap U τ) :
    payOf ω = payX U τ (fun ξ => (ω ξ).spin) (fun ξ => (payOf ω ξ).kx)
      (fun ξ => (payOf ω ξ).ky) := by
  have hs := setting_of_bgOf hτ hω hb
  funext ξ
  obtain ⟨x, z⟩ := ξ
  refine payVal_ext rfl ?_ (wE_legal hs (x, z)) ?_ (wN_legal hs (x, z)) (kx_legal hs (x, z)) ?_ ?_
    (lNx_legal hs hb (x, z))
  · show (ω (x, z)).wW = wEc τ (fun ξ => (ω ξ).spin) (x - 1, z)
    rw [← wE_legal hs (x - 1, z), hs.wE_eq (x - 1) z, sub_add_cancel]
  · show (ω (x, z)).wS = wNc τ (fun ξ => (ω ξ).spin) (x, z - 1)
    rw [← wN_legal hs (x, z - 1), hs.wN_eq x (z - 1), sub_add_cancel]
  · funext ι
    show (payOf ω (x, z)).ky ι = ((payOf ω (x, z)).ky ι &&
      kxX U τ (fun ξ => (payOf ω ξ).kx) (x, z) ι && gB U (bgMap U τ (x, z)) ι)
    rw [← kx_legal hs (x, z)]
    by_cases hact : (ω (x, z)).IsActive
    · obtain ⟨k, hk, -, -, -, -, -, -, -, -, -, c9⟩ := (hs.K3 _).2 hact
      have hy : ¬ (k.x ι = true ∧ SiteVal.gOf k ι = true) → k.y ι = false := by
        rcases hf : (ω (x, z)).fW
        · exact fun _ => c9.1 hf ι
        · exact c9.2 hf ι
      have hbk : (bgMap U τ (x, z)).k = some k.bg := by
        rw [← hb]
        show (ω (x, z)).k.map CellRec.bg = _
        rw [hk]; rfl
      have hg : gB U (bgMap U τ (x, z)) ι = SiteVal.gOf k ι := by
        unfold gB; rw [hbk]; rfl
      have ey : (payOf ω (x, z)).ky ι = k.y ι := by
        show (((ω (x, z)).k).map CellRec.y).getD _ ι = _
        rw [hk]; rfl
      have ex : (payOf ω (x, z)).kx ι = k.x ι := by
        show (((ω (x, z)).k).map CellRec.x).getD _ ι = _
        rw [hk]; rfl
      rw [ey, ex, hg]
      exact bool_y hy
    · have e : (payOf ω (x, z)).ky = fun _ => false := by
        show (((ω (x, z)).k).map CellRec.y).getD _ = _
        rw [(hs.K3 _).1 hact]; rfl
      rw [e]
      rfl
  · show xOf (ω (x, z)).lS = lNxX U τ (fun ξ => (payOf ω ξ).kx) (x, z - 1)
    rw [← lNx_legal hs hb (x, z - 1)]
    show xOf (ω (x, z)).lS = xOf (ω (x, z - 1)).lN
    rw [hs.lN_eq x (z - 1), sub_add_cancel]

/-- **`pay:factor`(b), (P3)**: the spins and the switches at the roots of a legal configuration
with background `𝔟_τ` satisfy `P3X`. -/
theorem p3X_of_legal (hτ : Typical τ) (hω : IsLegal (Phi U) ω) (hb : bgOf ω = bgMap U τ) :
    P3X U τ (fun ξ => (ω ξ).spin) (fun ξ => (payOf ω ξ).kx) := by
  have hs := setting_of_bgOf hτ hω hb
  intro d m1 m2 hd hr
  have h0 : 0 < MachineM.Nd d := by have := MachineM.two_le_Nd d; omega
  have hroot : (ω (root τ d m1 m2)).IsRoot := (hs.isRoot_iff _).2 ⟨d, m1, m2, hd, rfl⟩
  obtain ⟨hk, -⟩ := hs.rules hd m1 m2 h0 h0
  rw [gsite_zero hd] at hk
  have hrdy : (cellAt ω τ d m1 m2 0 0).rdy = true := by
    rw [hs.grid_rdy hd m1 m2 h0 h0]; exact decide_eq_true hr
  obtain ⟨hp3h, hp3v⟩ := hs.P3 _ hroot _ hk hrdy
  have hkx : (payOf ω (root τ d m1 m2)).kx = (cellAt ω τ d m1 m2 0 0).x := by
    show (((ω (root τ d m1 m2)).k).map CellRec.x).getD _ = _
    rw [hk]; rfl
  have hP : (0 : ℤ) < 4 ^ (d + 1) := by positivity
  have hW : (ω (root τ d m1 m2)).wW = some ((ω (root τ d (m1 - 1) m2)).spin) := by
    have e := rfree_succ (a1 τ) d (m1 - 1)
    rw [sub_add_cancel] at e
    have h1 := wE_legal hs (rfree (a1 τ) d m1 - 1, rfree (a2 τ) d m2)
    have h2 : wEc τ (fun ξ => (ω ξ).spin) (rfree (a1 τ) d m1 - 1, rfree (a2 τ) d m2) =
        some ((ω (root τ d (m1 - 1) m2)).spin) :=
      wEc_arm _ hd (by linarith) (by rw [sub_add_cancel]; linarith)
    rw [h2, hs.wE_eq, sub_add_cancel] at h1
    exact h1
  have hS : (ω (root τ d m1 m2)).wS = some ((ω (root τ d m1 (m2 - 1))).spin) := by
    have e := rfree_succ (a2 τ) d (m2 - 1)
    rw [sub_add_cancel] at e
    have h1 := wN_legal hs (rfree (a1 τ) d m1, rfree (a2 τ) d m2 - 1)
    have h2 : wNc τ (fun ξ => (ω ξ).spin) (rfree (a1 τ) d m1, rfree (a2 τ) d m2 - 1) =
        some ((ω (root τ d m1 (m2 - 1))).spin) :=
      wNc_arm _ hd (by linarith) (by rw [sub_add_cancel]; linarith)
    rw [h2, hs.wN_eq, sub_add_cancel] at h1
    exact h1
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h' : (cellAt ω τ d m1 m2 0 0).x 0 = false ∧ (cellAt ω τ d m1 m2 0 0).x 1 = true := by
      rw [← hkx]; exact h
    have := hp3h h'
    rw [hW] at this
    exact (Option.some.inj this).symm
  · have h' : (cellAt ω τ d m1 m2 0 0).x 2 = false ∧ (cellAt ω τ d m1 m2 0 0).x 3 = true := by
      rw [← hkx]; exact h
    have := hp3v h'
    rw [hS] at this
    exact (Option.some.inj this).symm

/-- **`pay:factor`(a), (b)**: for typical `τ`, the payloads `p` compatible with `𝔟_τ` for which
`(𝔟_τ, p)` is legal are exactly the explicit payloads `payX U τ σ sw yv` with `P3X U τ σ sw`. -/
theorem legal_iff_payX (hτ : Typical τ) (p : Plane → PayVal) :
    (IsLegal (Phi U) (assemble (bgMap U τ) p) ∧ ∀ ξ, Compatible (bgMap U τ ξ) (p ξ)) ↔
      ∃ σ sw yv, P3X U τ σ sw ∧ p = payX U τ σ sw yv := by
  constructor
  · rintro ⟨hl, hc⟩
    have hb : bgOf (assemble (bgMap U τ) p) = bgMap U τ := funext fun ξ => bgPart_merge _ _
    have hp : payOf (assemble (bgMap U τ) p) = p := payOf_assemble hc
    exact ⟨_, _, _, p3X_of_legal hτ hl hb, hp.symm.trans (payOf_eq_payX hτ hl hb)⟩
  · rintro ⟨σ, sw, yv, h3, rfl⟩
    exact ⟨legal_payX hτ σ sw yv h3, compatible_payX σ sw yv⟩

end LegalExplicit

end UPD.BG

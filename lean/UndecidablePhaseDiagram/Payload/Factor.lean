/-
# `pay:factor`: the frozen kernels are the kernels of the edge factors

New in this project (session 10). For a typical phase `τ` and `𝔟 = 𝔟_τ`, the frozen weight system
`frozenSystem β 𝔟` on the payload coordinates and the factor system `γ` of `pay:elim` built from
the edges (`elimData`, `Payload/Edges.lean`), read on the same coordinates through the relabelling
`relabel : Coord ≃ Plane ⊕ Σ e, Q e`, have the same Gibbs measures.

* `payX_site` (**`pay:factor`(a)**, fixed coordinates): at a coordinate private to no real edge
  the explicit payloads `payX` have the fixed value (`□` or `0`).
* `payX_priv`: at a private coordinate of a real edge `r` they have the value forced by the factor
  (`tgtX`: the arm is `σ_u`, the copies are the switches at the root, the free bits are kept only
  where `x_ι = g_ι = 1`).
* `pos_iff` (**`pay:factor`(b)**, supports): every frozen weight is positive at `c` iff every
  factor `W_e`, `κ_v` is positive at `c` (both say: `(𝔟, c)` is legal, by `legal_iff_payX`).
* `ratio` (**`pay:factor`(b)**, "up to factors that do not involve the coordinates at the sites of
  `Λ`"): between two such configurations differing inside `Λ` the frozen weight and the factor
  weight change by the same factor `e^{-β ΔH}`, the change of the charge.
* **`pay_factor`**: `isGibbs_iff_of_ratio` (`Gibbs/Compare.lean`).
-/
import UndecidablePhaseDiagram.Payload.Edges
import UndecidablePhaseDiagram.Gibbs.Compare

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace UPD.BG

open UPD.Scaffold

variable {U : Machine} {τ : ℕ → Bool × Bool}

/-! ## Indices of roots -/

/-- The index of the interval `[r_d(m), r_d(m + 1))` containing `z`. -/
def idxOf (a : ℕ → ℤ) (d : ℕ) (z : ℤ) : ℤ := (z - rfree a d 0) / 4 ^ (d + 1)

theorem idxOf_spec (a : ℕ → ℤ) (d : ℕ) (z : ℤ) :
    rfree a d (idxOf a d z) ≤ z ∧ z < rfree a d (idxOf a d z + 1) := by
  have hP : (0 : ℤ) < 4 ^ (d + 1) := by positivity
  have e0 := rfree_eq_add a d (idxOf a d z)
  have e1 := rfree_eq_add a d (idxOf a d z + 1)
  have h1 := Int.ediv_mul_le (z - rfree a d 0) hP.ne'
  have h2 := Int.lt_ediv_add_one_mul_self (z - rfree a d 0) hP
  unfold idxOf at *
  constructor <;> nlinarith

/-- A coordinate on a marked row, `w^E`, lies in an arm. -/
theorem arm_wE {d : ℕ} (hd : 1 ≤ d) {m2 x : ℤ} :
    ∃ r, privPred τ U r ((x, rfree (a2 τ) d m2), .wE) := by
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
  have h := idxOf_spec (a1 τ) (k + 1) x
  refine ⟨(k, idxOf (a1 τ) (k + 1) x + 1, m2, false), Or.inl ?_⟩
  unfold armPred
  rw [if_neg (by simp)]
  exact ⟨rfl, Or.inl ⟨rfl, by simpa using h.1, by simpa using h.2⟩⟩

theorem arm_wW {d : ℕ} (hd : 1 ≤ d) {m2 x : ℤ} :
    ∃ r, privPred τ U r ((x, rfree (a2 τ) d m2), .wW) := by
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
  have h := idxOf_spec (a1 τ) (k + 1) (x - 1)
  refine ⟨(k, idxOf (a1 τ) (k + 1) (x - 1) + 1, m2, false), Or.inl ?_⟩
  unfold armPred
  rw [if_neg (by simp)]
  exact ⟨rfl, Or.inr ⟨rfl, by simp only [add_sub_cancel_right]; omega,
    by simp only [add_sub_cancel_right]; omega⟩⟩

theorem arm_wN {d : ℕ} (hd : 1 ≤ d) {m1 z : ℤ} :
    ∃ r, privPred τ U r ((rfree (a1 τ) d m1, z), .wN) := by
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
  have h := idxOf_spec (a2 τ) (k + 1) z
  refine ⟨(k, m1, idxOf (a2 τ) (k + 1) z + 1, true), Or.inl ?_⟩
  unfold armPred
  rw [if_pos rfl]
  exact ⟨rfl, Or.inl ⟨rfl, by simpa using h.1, by simpa using h.2⟩⟩

theorem arm_wS {d : ℕ} (hd : 1 ≤ d) {m1 z : ℤ} :
    ∃ r, privPred τ U r ((rfree (a1 τ) d m1, z), .wS) := by
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
  have h := idxOf_spec (a2 τ) (k + 1) (z - 1)
  refine ⟨(k, m1, idxOf (a2 τ) (k + 1) (z - 1) + 1, true), Or.inl ?_⟩
  unfold armPred
  rw [if_pos rfl]
  exact ⟨rfl, Or.inr ⟨rfl, by simp only [add_sub_cancel_right]; omega,
    by simp only [add_sub_cancel_right]; omega⟩⟩

/-- The edge of a component `ι`: horizontal for `ι ∈ {0, 1}`, vertical for `ι ∈ {2, 3}`. -/
def dirOf (ι : Fin 4) : Bool := decide (2 ≤ ι.val)

theorem inPair_dirOf (ι : Fin 4) : InPair (dirOf ι) ι := by
  unfold InPair dirOf
  by_cases h : 2 ≤ ι.val <;> simp [h] <;> omega

theorem sens_gsite {d : ℕ} (hd : 1 ≤ d) (hr : MachineM.ready U d) {m1 m2 : ℤ} {j : ℕ}
    (hj : j < MachineM.Nd d) (ι : Fin 4) {f : PFld} (hf : f = .kx ι ∨ f = .ky ι) :
    privPred τ U (d - 1, m1, m2, dirOf ι) (gsite τ d m1 m2 0 j, f) := by
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
  exact Or.inr ⟨hr, ι, inPair_dirOf ι, Or.inl ⟨j, hj, rfl, hf⟩⟩

theorem sens_lNx {d : ℕ} (hd : 1 ≤ d) (hr : MachineM.ready U d) {m1 m2 z : ℤ}
    (h0 : zeta (a2 τ) d m2 0 ≤ z) (h1 : z < zeta (a2 τ) d m2 (MachineM.Nd d - 1)) (ι : Fin 4) :
    privPred τ U (d - 1, m1, m2, dirOf ι) ((rfree (a1 τ) d m1, z), .lNx ι) := by
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
  exact Or.inr ⟨hr, ι, inPair_dirOf ι, Or.inr (Or.inr ⟨rfl, h0, h1, rfl⟩)⟩

theorem sens_lSx {d : ℕ} (hd : 1 ≤ d) (hr : MachineM.ready U d) {m1 m2 z : ℤ}
    (h0 : zeta (a2 τ) d m2 0 < z) (h1 : z ≤ zeta (a2 τ) d m2 (MachineM.Nd d - 1)) (ι : Fin 4) :
    privPred τ U (d - 1, m1, m2, dirOf ι) ((rfree (a1 τ) d m1, z), .lSx ι) := by
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
  exact Or.inr ⟨hr, ι, inPair_dirOf ι, Or.inr (Or.inl ⟨rfl, h0, h1, rfl⟩)⟩

/-! ## The explicit payloads at the coordinates -/

/-- **`pay:factor`(a)**, fixed coordinates: at a non-spin coordinate private to no real edge, the
explicit payloads have the fixed value. -/
theorem payX_site {q : Coord} (hq : q.2 ≠ .spin) (h : ¬ ∃ r, privPred τ U r q)
    (σ : Plane → Spin) (sw yv : Plane → Fin 4 → Bool) :
    encode (payX U τ σ sw yv q.1) q.2 = fixedVal q.2 := by
  obtain ⟨⟨x, y⟩, f⟩ := q
  have hunH : ∀ x' : ℤ, (∀ d m, 1 ≤ d → y = rfree (a2 τ) d m →
      ∃ r, privPred τ U r ((x, y), f)) → wEc τ σ (x', y) = none := by
    intro x' hall
    refine wEc_unmarked σ fun ⟨d, m, hd, hy⟩ => h (hall d m hd hy)
  have hunV : ∀ y' : ℤ, (∀ d m, 1 ≤ d → x = rfree (a1 τ) d m →
      ∃ r, privPred τ U r ((x, y), f)) → wNc τ σ (x, y') = none := by
    intro y' hall
    refine wNc_unmarked σ fun ⟨d, m, hd, hx⟩ => h (hall d m hd hx)
  cases f with
  | spin => exact absurd rfl hq
  | wE =>
    show PV.wire (wEc τ σ (x, y)) = _
    rw [hunH x fun d m hd hy => by subst hy; exact arm_wE hd]; rfl
  | wW =>
    show PV.wire (wEc τ σ (x - 1, y)) = _
    rw [hunH (x - 1) fun d m hd hy => by subst hy; exact arm_wW hd]; rfl
  | wN =>
    show PV.wire (wNc τ σ (x, y)) = _
    rw [hunV y fun d m hd hx => by subst hx; exact arm_wN hd]; rfl
  | wS =>
    show PV.wire (wNc τ σ (x, y - 1)) = _
    rw [hunV (y - 1) fun d m hd hx => by subst hx; exact arm_wS hd]; rfl
  | kx ι =>
    show PV.bit (kxX U τ sw (x, y) ι) = _
    rw [kxX_eq_false sw (fun ⟨d, m1, m2, j, hd, hr, hj, he⟩ =>
      h ⟨_, by rw [he]; exact sens_gsite hd hr hj ι (Or.inl rfl)⟩)]
    rfl
  | ky ι =>
    show PV.bit (yv (x, y) ι && kxX U τ sw (x, y) ι && _) = _
    rw [kxX_eq_false sw (fun ⟨d, m1, m2, j, hd, hr, hj, he⟩ =>
      h ⟨_, by rw [he]; exact sens_gsite hd hr hj ι (Or.inr rfl)⟩)]
    simp [fixedVal]
  | lNx ι =>
    show PV.bit (lNxX U τ sw (x, y) ι) = _
    rw [lNxX_eq_false sw (fun ⟨d, m1, m2, z, hd, hr, h0, h1, he⟩ =>
      h ⟨_, by rw [he]; exact sens_lNx hd hr h0 h1 ι⟩)]
    rfl
  | lSx ι =>
    show PV.bit (lNxX U τ sw (x, y - 1) ι) = _
    rw [lNxX_eq_false sw (fun ⟨d, m1, m2, z, hd, hr, h0, h1, he⟩ => h ⟨_, by
      obtain ⟨hx, hz⟩ := Prod.mk.inj he
      have hy : y = z + 1 := by omega
      rw [hx, hy]
      exact sens_lSx (m2 := m2) hd hr (by omega) (by omega) ι⟩)]
    rfl

variable (τ U) in
/-- The value forced by the factor of `r` at a private coordinate, in terms of the free data. -/
def tgtX (r : REdge) (σ : Plane → Spin) (sw yv : Plane → Fin 4 → Bool) (q : Coord) : PV :=
  match q.2 with
  | .spin => .sp (σ q.1)
  | .wW => .wire (some (σ (rtail τ r)))
  | .wE => .wire (some (σ (rtail τ r)))
  | .wS => .wire (some (σ (rtail τ r)))
  | .wN => .wire (some (σ (rtail τ r)))
  | .kx ι => .bit (sw (rhead τ r) ι)
  | .ky ι => .bit (yv q.1 ι && sw (rhead τ r) ι && gB U (bgMap U τ q.1) ι)
  | .lSx ι => .bit (sw (rhead τ r) ι)
  | .lNx ι => .bit (sw (rhead τ r) ι)

theorem rhead_eq (k : ℕ) (m1 m2 : ℤ) (v : Bool) :
    rhead τ (k, m1, m2, v) = gsite τ (k + 1) m1 m2 0 0 :=
  (gsite_zero (by omega) m1 m2).symm

/-- At a private coordinate of a real edge the explicit payloads have the forced value. -/
theorem payX_priv {r : REdge} {q : Coord} (h : privPred τ U r q)
    (σ : Plane → Spin) (sw yv : Plane → Fin 4 → Bool) :
    encode (payX U τ σ sw yv q.1) q.2 = tgtX U τ r σ sw yv q := by
  obtain ⟨k, m1, m2, v⟩ := r
  obtain ⟨⟨x, y⟩, f⟩ := q
  rcases h with ha | ⟨hr, ι, hι, hs⟩
  · unfold armPred at ha
    cases v <;> simp only [Bool.false_eq_true, ↓reduceIte] at ha
    · obtain ⟨rfl, hw⟩ := ha
      have e := sub_add_cancel m1 1
      rcases hw with ⟨rfl, h0, h1⟩ | ⟨rfl, h0, h1⟩
      · show PV.wire (wEc τ σ (x, _)) = _
        rw [wEc_arm σ (by omega) h0 (by rwa [e])]; rfl
      · show PV.wire (wEc τ σ (x - 1, _)) = _
        rw [wEc_arm σ (by omega) (show rfree (a1 τ) (k + 1) (m1 - 1) ≤ x - 1 by omega)
          (by rw [e]; omega)]; rfl
    · obtain ⟨rfl, hw⟩ := ha
      have e := sub_add_cancel m2 1
      rcases hw with ⟨rfl, h0, h1⟩ | ⟨rfl, h0, h1⟩
      · show PV.wire (wNc τ σ (_, y)) = _
        rw [wNc_arm σ (by omega) h0 (by rwa [e])]; rfl
      · show PV.wire (wNc τ σ (_, y - 1)) = _
        rw [wNc_arm σ (by omega) (show rfree (a2 τ) (k + 1) (m2 - 1) ≤ y - 1 by omega)
          (by rw [e]; omega)]; rfl
  · dsimp only at hr hι hs
    rcases hs with ⟨j, hj, hq, rfl | rfl⟩ | ⟨hx, h0, h1, rfl⟩ | ⟨hx, h0, h1, rfl⟩
    · show PV.bit (kxX U τ sw (x, y) ι) = PV.bit (sw (rhead τ (k, m1, m2, v)) ι)
      try simp only at hq
      rw [hq, kxX_gsite sw (by omega) hr m1 m2 hj ι, rhead]
    · show PV.bit (yv (x, y) ι && kxX U τ sw (x, y) ι && _) =
        PV.bit (yv (x, y) ι && sw (rhead τ (k, m1, m2, v)) ι && _)
      try simp only at hq
      rw [hq, kxX_gsite sw (by omega) hr m1 m2 hj ι, rhead]
    · show PV.bit (lNxX U τ sw (x, y - 1) ι) = PV.bit (sw (rhead τ (k, m1, m2, v)) ι)
      try simp only at hx h0 h1
      rw [hx, lNxX_col sw (by omega) hr m1 m2 (by omega) (by omega) ι, rhead]
    · show PV.bit (lNxX U τ sw (x, y) ι) = PV.bit (sw (rhead τ (k, m1, m2, v)) ι)
      try simp only at hx h0 h1
      rw [hx, lNxX_col sw (by omega) hr m1 m2 h0 h1 ι, rhead]


/-! ## Supports (`pay:factor`(b)) -/

/-- A sensor coordinate of `r` makes the switch at the root a private coordinate of `r`. -/
theorem sens_head {r : REdge} {q : Coord} (h : privPred τ U r q) {ι : Fin 4}
    (hf : q.2 = .kx ι ∨ q.2 = .ky ι ∨ q.2 = .lSx ι ∨ q.2 = .lNx ι) :
    privPred τ U r (rhead τ r, .kx ι) := by
  obtain ⟨k, m1, m2, v⟩ := r
  rcases h with ha | ⟨hr, ι', hι', hs⟩
  · exfalso
    unfold armPred at ha
    split_ifs at ha <;> rcases ha.2 with ⟨h', -⟩ | ⟨h', -⟩ <;>
      rcases hf with h | h | h | h <;> rw [h] at h' <;> simp at h'
  · have hιι : ι' = ι := by
      rcases hs with ⟨j, -, -, h | h⟩ | ⟨-, -, -, h⟩ | ⟨-, -, -, h⟩ <;>
        rcases hf with h' | h' | h' | h' <;> rw [h] at h' <;> simp at h' <;>
          first | exact h' | exact h'.symm
    subst hιι
    refine Or.inr ⟨hr, ι', hι', Or.inl ⟨0, ?_, rhead_eq k m1 m2 v, Or.inl rfl⟩⟩
    show 0 < MachineM.Nd (k + 1)
    have := MachineM.two_le_Nd (k + 1); omega

/-- A switch at the root of a ready edge is a private coordinate of that edge. -/
theorem sens_root {k : ℕ} {m1 m2 : ℤ} {v : Bool} (hr : MachineM.ready U (k + 1)) {ι : Fin 4}
    (hι : InPair v ι) : privPred τ U (k, m1, m2, v) (rhead τ (k, m1, m2, v), .kx ι) := by
  refine Or.inr ⟨hr, ι, hι, Or.inl ⟨0, ?_, rhead_eq k m1 m2 v, Or.inl rfl⟩⟩
  show 0 < MachineM.Nd (k + 1)
  have := MachineM.two_le_Nd (k + 1); omega

theorem ready_of_sens {r : REdge} {ι : Fin 4} (h : privPred τ U r (rhead τ r, .kx ι)) :
    MachineM.ready U (r.1 + 1) ∧ InPair r.2.2.2 ι := by
  rcases h with ha | ⟨hr, ι', hι', hs⟩
  · exfalso
    unfold armPred at ha
    split_ifs at ha <;> rcases ha.2 with ⟨h', -⟩ | ⟨h', -⟩ <;> simp at h'
  · refine ⟨hr, ?_⟩
    rcases hs with ⟨j, -, -, h | h⟩ | ⟨-, -, -, h⟩ | ⟨-, -, -, h⟩ <;> simp at h
    · rw [h]; exact hι'

theorem swv_of {r : REdge} {ζ : Q τ U (Sum.inr r) → PV} {ι : Fin 4}
    (h : privPred τ U r (rhead τ r, .kx ι)) :
    swv τ U r ζ ι = (ζ ⟨(rhead τ r, .kx ι), by simp, owner_of h⟩).bitOf := by
  unfold swv
  rw [dif_pos ⟨by simp, owner_of h⟩]

theorem swv_of_not {r : REdge} {ζ : Q τ U (Sum.inr r) → PV} {ι : Fin 4}
    (h : ¬ privPred τ U r (rhead τ r, .kx ι)) : swv τ U r ζ ι = false := by
  unfold swv
  rw [dif_neg]
  rintro ⟨-, ho⟩
  exact h (privPred_of_owner ho)

theorem inPair_iMinus (r : REdge) : InPair r.2.2.2 (iMinus r) := by
  unfold InPair iMinus; cases r.2.2.2 <;> decide

theorem inPair_iPlus (r : REdge) : InPair r.2.2.2 (iPlus r) := by
  unfold InPair iPlus; cases r.2.2.2 <;> decide

/-- The coordinates of `c` are those of `payX` when `c` has the kinds and decodes to `payX`. -/
theorem coords_eq {c : Coord → PV} (hk : ∀ q : Coord, q.2.ok (c q) = true)
    {σ : Plane → Spin} {sw yv : Plane → Fin 4 → Bool} (hp : decodeC c = payX U τ σ sw yv)
    (q : Coord) : c q = encode (payX U τ σ sw yv q.1) q.2 := by
  rw [← hp]
  exact (congrFun (encode_decode (c := fun f => c (q.1, f)) fun f => hk (q.1, f)) q.2).symm

/-- Every frozen weight is positive iff the coordinates have their kinds, are compatible with `𝔟`,
and `(𝔟, c)` is legal. -/
theorem frozen_pos_iff (β : ℝ) (b : Plane → BgVal U) (c : Coord → PV) :
    (frozenSystem β b).Pos c ↔ (∀ q : Coord, q.2.ok (c q) = true) ∧
      IsLegal (Phi U) (assemble b (decodeC c)) ∧ ∀ ξ, Compatible (b ξ) (decodeC c ξ) := by
  constructor
  · intro h
    exact ⟨fun q => (siteOK_of_pos β h q.1).1 q.2, legal_ofCoords β h,
      fun ξ => (siteOK_of_pos β h ξ).2⟩
  · rintro ⟨hk, hl, hc⟩ Λ
    have e : toCoords (assemble b (decodeC c)) = c := by
      funext q
      show encode (payOf (assemble b (decodeC c)) q.1) q.2 = c q
      rw [payOf_assemble hc]
      exact congrFun (encode_decode (c := fun f => c (q.1, f)) fun f => hk (q.1, f)) q.2
    have := frozen_pos β (ω := ofCoords b c) hl (bgOf_ofCoords b c) Λ
    rwa [show ofCoords b c = assemble b (decodeC c) from rfl, e] at this

/-- Every weight of `γ` is positive iff every factor `W_e` is supported (`Good`) and every spin
coordinate holds a spin. -/
theorem gamma_pos_iff (β : ℝ) (c : Coord → PV) :
    (elimData τ U β).gamma.toHard.Pos (fun i => c ((relabel τ U).symm i)) ↔
      (∀ e : Ed, Good τ U e (fun q => c q.1) (c (etail τ e, .spin)) (c (ehead τ e, .spin))) ∧
        ∀ v : Plane, PFld.spin.ok (c (v, .spin)) = true := by
  constructor
  · intro h
    refine ⟨fun e => ?_, fun v => ?_⟩
    · have hφ := (elimData τ U β).gamma.φ_pos_of_W_pos h (k := Sum.inl e)
        (i := Sum.inl (etail τ e)) (by simp [Gibbs.ElimData.gamma, elimData])
      change 0 < Wf τ U β e (fun q => c q.1) (c (etail τ e, .spin)) (c (ehead τ e, .spin)) at hφ
      unfold Wf at hφ
      by_contra hg
      rw [if_neg hg, zero_mul] at hφ
      exact lt_irrefl 0 hφ
    · have hφ := (elimData τ U β).gamma.φ_pos_of_W_pos h (k := Sum.inr v)
        (i := Sum.inl v) (by simp [Gibbs.ElimData.gamma])
      change 0 < (if PFld.spin.ok (c (v, .spin)) = true then (1 : ℝ) else 0) at hφ
      by_contra hn
      rw [if_neg hn] at hφ
      exact lt_irrefl 0 hφ
  · rintro ⟨hg, hs⟩ Λ
    refine (elimData τ U β).gamma.W_pos_of_φ_pos (fun k => ?_) Λ
    rcases k with e | v
    · change 0 < Wf τ U β e (fun q => c q.1) (c (etail τ e, .spin)) (c (ehead τ e, .spin))
      unfold Wf
      rw [if_pos (hg e), one_mul]
      exact Real.exp_pos _
    · change 0 < (if PFld.spin.ok (c (v, .spin)) = true then (1 : ℝ) else 0)
      rw [if_pos (hs v)]
      exact one_pos

theorem tgt_eq_tgtX {r : REdge} {ζ : Q τ U (Sum.inr r) → PV} {a : PV} {σ : Plane → Spin}
    {sw yv : Plane → Fin 4 → Bool} (q : Q τ U (Sum.inr r)) (ha : a.spinOf = σ (rtail τ r))
    (hsw : ∀ ι, privPred τ U r (rhead τ r, .kx ι) → swv τ U r ζ ι = sw (rhead τ r) ι)
    (hy : ∀ ι, q.1.2 = .ky ι → ((ζ q).bitOf && sw (rhead τ r) ι && gB U (bgMap U τ q.1.1) ι) =
      (yv q.1.1 ι && sw (rhead τ r) ι && gB U (bgMap U τ q.1.1) ι)) :
    tgt τ U r a ζ q = tgtX U τ r σ sw yv q.1 := by
  have hq := privPred_of_owner q.2.2
  obtain ⟨⟨ξ, f⟩, hne, ho⟩ := q
  cases f with
  | spin => exact absurd rfl hne
  | wW => simp only [tgt, tgtX, ha]
  | wE => simp only [tgt, tgtX, ha]
  | wS => simp only [tgt, tgtX, ha]
  | wN => simp only [tgt, tgtX, ha]
  | kx ι => simp only [tgt, tgtX, hsw ι (sens_head hq (Or.inl rfl))]
  | ky ι =>
    simp only [tgt, tgtX, hsw ι (sens_head hq (Or.inr (Or.inl rfl)))]
    rw [hy ι rfl]
  | lSx ι => simp only [tgt, tgtX, hsw ι (sens_head hq (Or.inr (Or.inr (Or.inl rfl))))]
  | lNx ι => simp only [tgt, tgtX, hsw ι (sens_head hq (Or.inr (Or.inr (Or.inr rfl))))]

variable (hτ : Typical τ)
include hτ

/-- **`pay:factor`(b)**, supports: all frozen weights are positive at `c` iff all factors of the
edges are. -/
theorem pos_iff (β : ℝ) (c : Coord → PV) :
    (frozenSystem β (bgMap U τ)).Pos c ↔
      (elimData τ U β).gamma.toHard.Pos (fun i => c ((relabel τ U).symm i)) := by
  rw [frozen_pos_iff, gamma_pos_iff]
  constructor
  · rintro ⟨hk, hl, hc⟩
    obtain ⟨σ, sw, yv, h3, hp⟩ := (legal_iff_payX hτ _).1 ⟨hl, hc⟩
    have hcq := coords_eq hk hp
    have hspin : ∀ v, c (v, .spin) = .sp (σ v) := fun v => hcq (v, .spin)
    have hsw : ∀ (r : REdge) (ι : Fin 4), privPred τ U r (rhead τ r, .kx ι) →
        swv τ U r (fun q => c q.1) ι = sw (rhead τ r) ι := by
      intro r ι h
      rw [swv_of h]
      show (c (rhead τ r, .kx ι)).bitOf = _
      rw [hcq, payX_priv h]; rfl
    refine ⟨fun e => ?_, fun v => by rw [hspin]; rfl⟩
    rcases e with ξ | r
    · intro q
      show c q.1 = fixedVal q.1.2
      rw [hcq, payX_site q.2.1 (of_owner_inl q.2.2).2]
    · refine ⟨fun q => ?_, fun hm hp' => ?_⟩
      · show c q.1 = _
        rw [hcq, payX_priv (privPred_of_owner q.2.2)]
        refine (tgt_eq_tgtX q (by rw [hspin]; rfl) (hsw r) fun ι hι => ?_).symm
        have : (c q.1).bitOf = (yv q.1.1 ι && sw (rhead τ r) ι && gB U (bgMap U τ q.1.1) ι) := by
          rw [hcq, payX_priv (privPred_of_owner q.2.2)]
          simp only [tgtX, hι]; rfl
        rw [this]; cases yv q.1.1 ι <;> cases sw (rhead τ r) ι <;> simp
      · obtain ⟨k, m1, m2, v⟩ := r
        by_cases hrd : MachineM.ready U (k + 1)
        · rw [hsw _ _ (sens_root hrd (inPair_iMinus (k, m1, m2, v)))] at hm
          rw [hsw _ _ (sens_root hrd (inPair_iPlus (k, m1, m2, v)))] at hp'
          have h3' := h3 (k + 1) m1 m2 (by omega) hrd
          show c (rtail τ (k, m1, m2, v), .spin) = c (rhead τ (k, m1, m2, v), .spin)
          rw [hspin, hspin]
          congr 1
          cases v
          · exact (h3'.1 ⟨hm, hp'⟩).symm
          · exact (h3'.2 ⟨hm, hp'⟩).symm
        · have hn : swv τ U (k, m1, m2, v) (fun q => c q.1) (iPlus (k, m1, m2, v)) = false :=
            swv_of_not (r := (k, m1, m2, v)) (ι := iPlus (k, m1, m2, v))
              fun h => hrd (ready_of_sens h).1
          rw [hn] at hp'
          exact absurd hp' Bool.false_ne_true
  · rintro ⟨hg, hs⟩
    set σ : Plane → Spin := fun ξ => (c (ξ, .spin)).spinOf
    set sw : Plane → Fin 4 → Bool := fun v ι => (c (v, .kx ι)).bitOf
    set yv : Plane → Fin 4 → Bool := fun ξ ι => (c (ξ, .ky ι)).bitOf
    have hsw : ∀ (r : REdge) (ι : Fin 4), privPred τ U r (rhead τ r, .kx ι) →
        swv τ U r (fun q => c q.1) ι = sw (rhead τ r) ι := fun r ι h => by rw [swv_of h]
    have hcq : ∀ q : Coord, c q = encode (payX U τ σ sw yv q.1) q.2 := by
      intro q
      by_cases hsp : q.2 = .spin
      · obtain ⟨ξ, f⟩ := q
        simp only at hsp
        subst hsp
        exact (PV.sp_spinOf (hs ξ)).symm
      rcases ho : owner τ U q with ξ | r
      · have hG := hg (Sum.inl ξ) ⟨q, hsp, ho⟩
        rw [payX_site hsp (of_owner_inl ho).2]
        exact hG
      · have hG := (hg (Sum.inr r)).1 ⟨q, hsp, ho⟩
        rw [payX_priv (privPred_of_owner ho)]
        refine hG.trans (tgt_eq_tgtX ⟨q, hsp, ho⟩ rfl (hsw r) fun ι hι => ?_)
        obtain ⟨ξ, f⟩ := q
        simp only at hι
        subst hι
        rfl
    have hp : decodeC c = payX U τ σ sw yv := by
      funext ξ
      show decode (fun f => c (ξ, f)) = _
      simp only [hcq]
      exact decode_encode _
    refine ⟨fun q => by rw [hcq]; exact encode_ok _ _, ?_⟩
    have h3 : P3X U τ σ sw := by
      intro d m1 m2 hd hrd
      obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
      constructor
      · rintro ⟨hm, hp'⟩
        have hP := (hg (Sum.inr (k, m1, m2, false))).2
        rw [hsw _ _ (sens_root hrd (inPair_iMinus (k, m1, m2, false))),
          hsw _ _ (sens_root hrd (inPair_iPlus (k, m1, m2, false)))] at hP
        have := hP hm hp'
        exact (congrArg PV.spinOf this).symm
      · rintro ⟨hm, hp'⟩
        have hP := (hg (Sum.inr (k, m1, m2, true))).2
        rw [hsw _ _ (sens_root hrd (inPair_iMinus (k, m1, m2, true))),
          hsw _ _ (sens_root hrd (inPair_iPlus (k, m1, m2, true)))] at hP
        have := hP hm hp'
        exact (congrArg PV.spinOf this).symm
    exact (legal_iff_payX hτ _).2 ⟨σ, sw, yv, h3, hp⟩

omit hτ in
/-- At a legal configuration the interaction is the charge on singletons and `0` elsewhere. -/
theorem phi_legal {ω : Config (SiteVal U)} (h : IsLegal (Phi U) ω) (A : Finset Plane) :
    Phi U A ω = ∑ ξ ∈ A, if A = {ξ} then ((ω ξ).charge : ENNReal) else 0 := by
  by_cases h0 : ∃ ξ, A = {ξ}
  · obtain ⟨ξ, rfl⟩ := h0
    rw [Phi_singleton, Finset.sum_singleton, if_pos rfl]
    unfold siteEnergy
    rw [if_pos (allowed_of_legal h ξ)]
  · have hz : ∀ ξ ∈ A, (if A = {ξ} then ((ω ξ).charge : ENNReal) else 0) = 0 :=
      fun ξ _ => if_neg fun h' => h0 ⟨ξ, h'⟩
    rw [Finset.sum_eq_zero hz]
    by_cases h1 : ∃ ξ, A = {ξ, ξ + e1}
    · obtain ⟨ξ, rfl⟩ := h1
      rw [Phi_pairH]; unfold edgeEnergyH; rw [if_pos (matchH_of_legal h ξ)]
    by_cases h2 : ∃ ξ, A = {ξ, ξ + e2}
    · obtain ⟨ξ, rfl⟩ := h2
      rw [Phi_pairV]; unfold edgeEnergyV; rw [if_pos (matchV_of_legal h ξ)]
    exact Phi_other h0 h1 h2 ω

omit hτ in
/-- The energy of a finite set at a legal configuration is the sum of the charges. -/
theorem energy_legal {ω : Config (SiteVal U)} (h : IsLegal (Phi U) ω) (S : Finset Plane) :
    energy (Phi U) S ω = ∑ ξ ∈ S, ((ω ξ).charge : ENNReal) := by
  classical
  unfold energy
  have hs : ∀ ξ ∈ S, (({ξ} : Finset Plane) ∩ S).Nonempty := fun ξ hξ =>
    ⟨ξ, Finset.mem_inter.2 ⟨Finset.mem_singleton_self ξ, hξ⟩⟩
  let g : S → {A : Finset Plane // (A ∩ S).Nonempty} := fun ξ => ⟨{ξ.1}, hs ξ.1 ξ.2⟩
  have hg : Function.Injective g := fun a b hab => by
    have := congrArg Subtype.val hab
    exact Subtype.ext (Finset.singleton_inj.1 this)
  rw [tsum_eq_sum (s := S.attach.image g)]
  · rw [Finset.sum_image fun a _ b _ hab => hg hab]
    rw [← Finset.sum_attach S (fun ξ => ((ω ξ).charge : ENNReal))]
    refine Finset.sum_congr rfl fun ξ _ => ?_
    rw [phi_legal h, Finset.sum_singleton, if_pos rfl]
  · intro A hA
    rw [phi_legal h]
    refine Finset.sum_eq_zero fun ξ hξ => if_neg fun hA1 => hA ?_
    have hξS : ξ ∈ S := by
      obtain ⟨z, hz⟩ := A.2
      rw [hA1, Finset.mem_inter, Finset.mem_singleton] at hz
      rw [← hz.1]; exact hz.2
    exact Finset.mem_image.2 ⟨⟨ξ, hξS⟩, Finset.mem_attach _ _, Subtype.ext hA1.symm⟩

omit hτ in
/-- The charge of a site value is carried by one coordinate (`int:sub-charge`). -/
theorem charge_assemble (p : Plane → PayVal) (ξ : Plane) :
    ((assemble (bgMap U τ) p ξ).charge : ℝ) =
      ∑ f : PFld, chW τ U (ξ, f) (encode (p ξ) f) := by
  classical
  set bv := bgMap U τ ξ with hbv
  have hact : (assemble (bgMap U τ) p ξ).IsActive ↔ (merge bv p0).IsActive := Iff.rfl
  have hfW : (assemble (bgMap U τ) p ξ).fW = (merge bv p0).fW := rfl
  rcases hk : bv.k with _ | c
  · have h0 : (assemble (bgMap U τ) p ξ).k = none := by
      show bv.k.map _ = none; rw [hk]; rfl
    rw [SiteVal.charge, h0]
    push_cast
    refine (Finset.sum_eq_zero fun f _ => ?_).symm
    unfold chW
    split
    · rw [if_neg]
      rintro ⟨c', hc', -⟩
      simp only at hc'
      rw [← hbv, hk] at hc'
      exact absurd hc' (by simp)
    · rfl
  · have h1 : (assemble (bgMap U τ) p ξ).k = some (c.withXY (p ξ).kx (p ξ).ky) := by
      show bv.k.map _ = _; rw [hk]; rfl
    by_cases hc : (merge bv p0).IsActive ∧ (merge bv p0).fW = true ∧ c.rc.val ≤ 79
    · have hι : c.rc.val / 20 < 4 := by omega
      have hcond : ∃ c', (bgMap U τ ξ).k = some c' ∧ (merge (bgMap U τ ξ) p0).IsActive ∧
          (merge (bgMap U τ ξ) p0).fW = true ∧ c'.rc.val ≤ 79 ∧
          (⟨c.rc.val / 20, hι⟩ : Fin 4).val = c'.rc.val / 20 :=
        ⟨c, by rw [← hbv, hk], hc.1, hc.2.1, hc.2.2, rfl⟩
      rw [Finset.sum_eq_single (PFld.kx ⟨c.rc.val / 20, hι⟩)]
      · have hL : ((assemble (bgMap U τ) p ξ).charge : ℝ) =
            Sensor.bitR ((p ξ).kx ⟨c.rc.val / 20, hι⟩) := by
          rw [SiteVal.charge, h1]
          dsimp only
          rw [dif_pos ⟨hact.2 hc.1, hfW ▸ hc.2.1, hc.2.2⟩]
          show (((if (p ξ).kx ⟨c.rc.val / 20, hι⟩ = true then 1 else 0 : ℕ)) : ℝ) = _
          cases (p ξ).kx ⟨c.rc.val / 20, hι⟩ <;> simp [Sensor.bitR]
        have hR : chW τ U (ξ, PFld.kx ⟨c.rc.val / 20, hι⟩)
            (encode (p ξ) (PFld.kx ⟨c.rc.val / 20, hι⟩)) =
            Sensor.bitR ((p ξ).kx ⟨c.rc.val / 20, hι⟩) := by
          unfold chW
          dsimp only
          rw [if_pos hcond]
          rfl
        rw [hL, hR]
      · intro f _ hf
        unfold chW
        split
        · rename_i ι heq
          rw [if_neg]
          rintro ⟨c', hc', -, -, -, hιc⟩
          simp only at hc' heq
          rw [← hbv, hk, Option.some.injEq] at hc'
          subst hc'
          exact hf (by rw [heq]; congr 1; exact Fin.ext hιc)
        · rfl
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [SiteVal.charge, h1]
      simp only
      rw [dif_neg fun h => hc ⟨hact.1 h.1, hfW ▸ h.2.1, h.2.2⟩]
      push_cast
      refine (Finset.sum_eq_zero fun f _ => ?_).symm
      unfold chW
      split
      · rw [if_neg]
        rintro ⟨c', hc', ha, hw, hr, -⟩
        simp only at hc'
        rw [← hbv, hk, Option.some.injEq] at hc'
        subst hc'
        exact hc ⟨ha, hw, hr⟩
      · rfl

/-! ## Weights on the supports and their ratios -/

variable (τ U) in
/-- The charge carried by the coordinates at the sites of `Λ`. -/
def Fsum (Λ : Finset Coord) (c : Coord → PV) : ℝ :=
  ∑ q ∈ sitesOf Λ ×ˢ Finset.univ, chW τ U q (c q)

variable (τ U) in
/-- The charge carried by the private coordinates of the edges whose factors meet `K`. -/
def Gsum (β : ℝ) (K : Finset (Gibbs.ECoord Plane Ed (Q τ U))) (c : Coord → PV) : ℝ :=
  ∑ e ∈ ((elimData τ U β).gamma.meets K).toLeft, ∑ q : Q τ U e, chW τ U q.1 (c q.1)

omit hτ in
/-- On the support, the frozen weight is `e^{-β}` to the charge at the sites of `Λ`. -/
theorem frozenW_eq (β : ℝ) {c : Coord → PV} (hc : (frozenSystem β (bgMap U τ)).Pos c)
    (Λ : Finset Coord) : (frozenSystem β (bgMap U τ)).W Λ c = Real.exp (-β * Fsum U τ Λ c) := by
  obtain ⟨hk, hl, hcomp⟩ := (frozen_pos_iff β _ c).1 hc
  change frozenW β (bgMap U τ) Λ c = _
  unfold frozenW
  have hone : ∏ ξ ∈ sitesOf Λ, siteOK (bgMap U τ) c ξ = 1 := by
    refine Finset.prod_eq_one fun ξ _ => ?_
    unfold siteOK siteOK'
    rw [if_pos ⟨fun f => hk (ξ, f), hcomp ξ⟩]
  rw [hone, mul_one, energy_legal hl]
  have hne : ∑ ξ ∈ sitesOf Λ, ((assemble (bgMap U τ) (decodeC c) ξ).charge : ENNReal) ≠ ⊤ :=
    ENNReal.sum_ne_top.2 fun _ _ => ENNReal.natCast_ne_top _
  unfold boltzmann
  rw [if_neg hne, ENNReal.toReal_sum fun _ _ => ENNReal.natCast_ne_top _]
  simp only [ENNReal.toReal_natCast]
  have hch : ∀ ξ, ((assemble (bgMap U τ) (decodeC c) ξ).charge : ℝ) =
      ∑ f : PFld, chW τ U (ξ, f) (c (ξ, f)) := by
    intro ξ
    rw [charge_assemble]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [show encode (decodeC c ξ) f = c (ξ, f) from
      congrFun (encode_decode (c := fun f => c (ξ, f)) fun f => hk (ξ, f)) f]
  simp only [hch]
  unfold Fsum
  rw [Finset.sum_product]
  ring_nf

omit hτ in
/-- On the support, the factor weight is `e^{-β}` to the charge of the private coordinates of
the edges whose factors meet `K`. -/
theorem gammaW_eq (β : ℝ) {c : Coord → PV}
    (hc : (elimData τ U β).gamma.toHard.Pos (fun i => c ((relabel τ U).symm i)))
    (K : Finset (Gibbs.ECoord Plane Ed (Q τ U))) :
    (elimData τ U β).gamma.toHard.W K (fun i => c ((relabel τ U).symm i)) =
      Real.exp (-β * Gsum U τ β K c) := by
  obtain ⟨hg, hs⟩ := (gamma_pos_iff β c).1 hc
  rw [Gibbs.FactorSystem.toHard_W, Finset.prod_sum_eq_prod_toLeft_mul_prod_toRight]
  have h2 : ∏ v ∈ ((elimData τ U β).gamma.meets K).toRight,
      (elimData τ U β).gamma.φ (Sum.inr v) (fun i => c ((relabel τ U).symm i)) = 1 := by
    refine Finset.prod_eq_one fun v _ => ?_
    change (if PFld.spin.ok (c (v, .spin)) = true then (1 : ℝ) else 0) = 1
    rw [if_pos (hs v)]
  have h1 : ∀ e : Ed, (elimData τ U β).gamma.φ (Sum.inl e) (fun i => c ((relabel τ U).symm i)) =
      Real.exp (-β * ∑ q : Q τ U e, chW τ U q.1 (c q.1)) := by
    intro e
    change Wf τ U β e (fun q => c q.1) (c (etail τ e, .spin)) (c (ehead τ e, .spin)) = _
    unfold Wf
    rw [if_pos (hg e), one_mul]
  rw [h2, mul_one, Finset.prod_congr rfl fun e _ => h1 e, ← Real.exp_sum, Gsum, Finset.mul_sum]

omit hτ in
theorem Fsum_sub {Λ : Finset Coord} {x y : Coord → PV} (hy : ∀ q, q ∉ Λ → y q = x q) :
    Fsum U τ Λ y - Fsum U τ Λ x = ∑ q ∈ Λ, (chW τ U q (y q) - chW τ U q (x q)) := by
  unfold Fsum
  rw [← Finset.sum_sub_distrib]
  refine (Finset.sum_subset (fun q hq => ?_) fun q _ hq => ?_).symm
  · exact Finset.mem_product.2 ⟨Finset.mem_image.2 ⟨q, hq, rfl⟩, Finset.mem_univ _⟩
  · rw [hy q hq, sub_self]

omit hτ in
theorem chW_spin (ξ : Plane) (w : PV) : chW τ U (ξ, .spin) w = 0 := rfl

omit hτ in
theorem Gsum_sub (β : ℝ) {Λ : Finset Coord} {x y : Coord → PV} (hy : ∀ q, q ∉ Λ → y q = x q) :
    Gsum U τ β (Λ.map (relabel τ U).toEmbedding) y - Gsum U τ β (Λ.map (relabel τ U).toEmbedding) x =
      ∑ q ∈ Λ, (chW τ U q (y q) - chW τ U q (x q)) := by
  classical
  unfold Gsum
  rw [← Finset.sum_sub_distrib]
  simp only [← Finset.sum_sub_distrib]
  rw [Finset.sum_sigma']
  refine Finset.sum_bij_ne_zero (fun s _ _ => s.2.1) (fun s _ hs => ?_) (fun s _ _ t _ _ h => ?_)
    (fun q hq hne => ?_) (fun _ _ _ => rfl)
  · by_contra hn
    exact hs (by rw [hy _ hn, sub_self])
  · obtain ⟨e, ⟨q, hq, ho⟩⟩ := s
    obtain ⟨e', ⟨q', hq', ho'⟩⟩ := t
    simp only at h
    subst h
    have : e = e' := ho.symm.trans ho'
    subst this
    rfl
  · have hsp : q.2 ≠ .spin := by
      intro h
      obtain ⟨ξ, f⟩ := q
      simp only at h
      subst h
      exact hne (by rw [chW_spin, chW_spin, sub_self])
    refine ⟨⟨owner τ U q, ⟨q, hsp, rfl⟩⟩, ?_, hne, rfl⟩
    rw [Finset.mem_sigma]
    refine ⟨?_, Finset.mem_univ _⟩
    rw [Finset.mem_toLeft, Gibbs.FactorSystem.mem_meets]
    refine ⟨relabel τ U q, Finset.mem_map_of_mem _ hq, ?_⟩
    rw [relabel_of hsp]
    show _ ∈ ({Sum.inl _, Sum.inl _} ∪ Gibbs.ElimData.privSet _ : Finset _)
    exact Finset.mem_union_right _ (Gibbs.ElimData.mem_privSet.2 ⟨_, rfl⟩)

/-- **`pay:factor`(b)**, ratios: between two configurations of the support that differ inside `Λ`,
the frozen weight of `Λ` and the factor weight of `relabel(Λ)` change by the same factor. -/
theorem ratio (β : ℝ) {x : Coord → PV} (hx : (frozenSystem β (bgMap U τ)).Pos x)
    (Λ : Finset Coord) {y : Coord → PV} (hy : (frozenSystem β (bgMap U τ)).Pos y)
    (hyx : ∀ q, q ∉ Λ → y q = x q) :
    (frozenSystem β (bgMap U τ)).W Λ y *
        (elimData τ U β).gamma.toHard.W (Λ.map (relabel τ U).toEmbedding)
          (fun i => x ((relabel τ U).symm i)) =
      (elimData τ U β).gamma.toHard.W (Λ.map (relabel τ U).toEmbedding)
          (fun i => y ((relabel τ U).symm i)) * (frozenSystem β (bgMap U τ)).W Λ x := by
  rw [frozenW_eq β hx, frozenW_eq β hy, gammaW_eq β ((pos_iff hτ β x).1 hx),
    gammaW_eq β ((pos_iff hτ β y).1 hy), ← Real.exp_add, ← Real.exp_add]
  congr 1
  have h1 := Fsum_sub (τ := τ) (U := U) hyx
  have h2 := Gsum_sub (τ := τ) (U := U) β hyx
  linear_combination (-β) * (h1 - h2)

/-- **`pay:factor`**: for typical `τ`, the Gibbs measures of the frozen weight system of `𝔟_τ`
on the payload coordinates are exactly those of the factor system `γ` of the edges (`W_e`, `κ_v`),
transported along the relabelling `Coord ≃ Plane ⊕ Σ e, Q e`. -/
theorem pay_factor (β : ℝ) (μ : Measure (Coord → PV)) :
    (frozenSystem β (bgMap U τ)).IsGibbs μ ↔
      (elimData τ U β).gamma.toHard.IsGibbs (μ.map fun c i => c ((relabel τ U).symm i)) :=
  Gibbs.HardWeightSystem.isGibbs_iff_of_ratio _ _ (relabel τ U) (pos_iff hτ β)
    (fun _ hx Λ _ hy hyx => ratio hτ β hx Λ hy hyx) μ

end UPD.BG

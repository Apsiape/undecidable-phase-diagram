/-
# `pay:sum` for the edges of `𝔟_τ`: the edge sums `Z_e`

New in this project (session 10). The edge sums `Z_e(a, b) = ∑_{η_e} W_e(η_e, a, b)` of `pay:sum`
for the factors `W_e` of `pay:factor`(b) (`Wf`, `elimData`, `Payload/Edges.lean`), with the sensor
of a ready edge identified explicitly with the abstract sensor of `Payload/Sensor.lean`.

* `Zf_site`: the sum of a site edge does not depend on the end values (its private coordinates
  are the fixed coordinates of the site, with one admissible value each).
* **`Zf_nonready`** (`ρ_d = 0`): `Z_e = 1` (the private coordinates are the arm, whose only
  admissible value is `≡ σ_u`; no charge).
* The identification (`ρ_d = 1`, `N = N_d`, `n = n(d)`): the switch components of an edge are
  `swComp r 0` (`x⁻`) and `swComp r 1` (`x⁺`), and a component `ι` belongs to the switch
  `swSide ι = ι mod 2`. `toCfg` reads a configuration `ζ` of the private coordinates as an
  abstract sensor configuration in `Sensor.Cfg Empty N` (switches at the root `v = ξ(0, 0)`, no
  free copies, candidate free bits `y^±(j) = y_{ι}(0, j)`, `j < N`); `ofCfg` writes one back (arm
  `≡ σ_u`, every copy `x_ι` (cell records at `ξ(0, j)`, `ℓ^S`, `ℓ^N` on the first column) equal to
  its switch, `y_ι(0, j) = y^{ι mod 2}(j)`). `toCfg_ofCfg`, `ofCfg_toCfg`: inverse to each other on
  the configurations forced by the factor; `tgt_ofCfg_iff`: these are exactly the consistent
  sensor configurations for `L = sensL d = (20n - 5, 20n + 5)` (`gB_gsite`: the masks `g_ι` at
  `ξ(0, j)` are `[j < L_{ι mod 2}]`, `bg:ready`(a)); **`sensorEquiv`** packages this as a bijection.
  `good_ofCfg_iff`: `Good` (support of `W_e`) is consistency together with (P3).
  `charge_ofCfg`: the charge of the private coordinates is `20(x⁻ + x⁺)` (the charged coordinates
  are `(ξ(0, j), x_{⌊j/20⌋})`, `j < 80`, `⌊j/20⌋` a component of the edge: 20 copies per switch;
  `chW_gsite`). **`Wf_ofCfg`**: `W_e(ofCfg s) = Sensor.weight s`.
* **`Zf_eq_sensorSum`** (`ρ_d = 1`): `Z_e(σ_u, σ_v)` is the abstract sensor sum
  `∑_{s ∈ Sensor.Cfg Empty N} Sensor.weight s` (the reindexing `ofCfg`); **`Zf_ready`**:
  `Z_e(σ_u, σ_v) = H_n + G_n 1[σ_u = σ_v]` (`Sensor.pay_sum`), and **`Zf_ready_coupling`**:
  `Z_e(σ_u, σ_v) = sqrt(H_n (H_n + G_n)) e^{J_n σ_u σ_v}` (`Sensor.coupling`).
-/
import UndecidablePhaseDiagram.Payload.Factor
import UndecidablePhaseDiagram.Background.Ready

set_option autoImplicit false

noncomputable section

namespace UPD.BG

open UPD.Scaffold

variable {τ : ℕ → Bool × Bool} {U : Machine}

/-! ## Site edges -/

/-- The sum of a site edge does not depend on the end values. -/
theorem Zf_site (β : ℝ) (ξ : Plane) (a b a' b' : PV) :
    (elimData τ U β).Zf (Sum.inl ξ) a b = (elimData τ U β).Zf (Sum.inl ξ) a' b' := rfl

/-! ## Edges of non-ready depth -/

/-- For a non-ready depth, no private coordinate of the edge carries charge. -/
theorem chW_nonready {r : REdge} (hr : ¬ MachineM.ready U (r.1 + 1)) (q : Q τ U (Sum.inr r))
    (w : PV) : chW τ U q.1 w = 0 := by
  obtain ⟨⟨ξ, f⟩, hne, ho⟩ := q
  cases f with
  | kx ι => exact absurd (ready_of_sens (sens_head (privPred_of_owner ho) (Or.inl rfl))).1 hr
  | spin => rfl
  | wW => rfl
  | wE => rfl
  | wS => rfl
  | wN => rfl
  | ky ι => rfl
  | lSx ι => rfl
  | lNx ι => rfl

/-- For a non-ready depth, the only configuration on the support of `W_e` is the arm `≡ σ_u`. -/
theorem good_nonready {r : REdge} (hr : ¬ MachineM.ready U (r.1 + 1))
    {ζ : Q τ U (Sum.inr r) → PV} {a b : PV} (hg : Good τ U (Sum.inr r) ζ a b) :
    ζ = zeta0 (Sum.inr r) a := by
  funext q
  have hG := hg.1 q
  obtain ⟨⟨ξ, f⟩, hne, ho⟩ := q
  have hq := privPred_of_owner ho
  cases f with
  | spin => exact absurd rfl hne
  | wW => rw [hG]; rfl
  | wE => rw [hG]; rfl
  | wS => rw [hG]; rfl
  | wN => rw [hG]; rfl
  | kx ι => exact absurd (ready_of_sens (sens_head hq (Or.inl rfl))).1 hr
  | ky ι => exact absurd (ready_of_sens (sens_head hq (Or.inr (Or.inl rfl)))).1 hr
  | lSx ι => exact absurd (ready_of_sens (sens_head hq (Or.inr (Or.inr (Or.inl rfl))))).1 hr
  | lNx ι => exact absurd (ready_of_sens (sens_head hq (Or.inr (Or.inr (Or.inr rfl))))).1 hr

/-- **`pay:sum`, `ρ_d = 0`**: `Z_e = 1`. -/
theorem Zf_nonready (β : ℝ) {r : REdge} (hr : ¬ MachineM.ready U (r.1 + 1)) (a b : PV) :
    (elimData τ U β).Zf (Sum.inr r) a b = 1 := by
  have key : ∀ ζ : Q τ U (Sum.inr r) → PV, (elimData τ U β).Wf (Sum.inr r) ζ a b =
      if ζ = zeta0 (Sum.inr r) a then 1 else 0 := by
    intro ζ
    show Wf τ U β (Sum.inr r) ζ a b = _
    unfold Wf
    rw [Finset.sum_eq_zero (fun q _ => chW_nonready hr q (ζ q)), mul_zero, Real.exp_zero,
      mul_one]
    by_cases hz : ζ = zeta0 (Sum.inr r) a
    · rw [if_pos hz, if_pos (by rw [hz]; exact good_zeta0 (Sum.inr r) a b)]
    · rw [if_neg hz, if_neg fun hg => hz (good_nonready hr hg)]
  unfold Gibbs.ElimData.Zf
  rw [Finset.sum_congr rfl fun ζ _ => key ζ]
  simp

/-! ## The switch components of an edge -/

/-- The component of the switch `x⁻` (`k = 0`) or `x⁺` (`k = 1`) of an edge: `k` for a horizontal
edge, `2 + k` for a vertical one. -/
def swComp (r : REdge) (k : Fin 2) : Fin 4 :=
  ⟨(if r.2.2.2 then 2 else 0) + k.val, by have := k.isLt; split <;> omega⟩

/-- The switch of a component (`0` is `x⁻`, `1` is `x⁺`): its parity. -/
def swSide (ι : Fin 4) : Fin 2 := ⟨ι.val % 2, Nat.mod_lt _ (by norm_num)⟩

theorem swSide_swComp (r : REdge) (k : Fin 2) : swSide (swComp r k) = k := by
  apply Fin.ext
  show ((if r.2.2.2 then 2 else 0) + k.val) % 2 = k.val
  have := k.isLt
  split <;> omega

theorem swComp_swSide {r : REdge} {ι : Fin 4} (h : InPair r.2.2.2 ι) : swComp r (swSide ι) = ι := by
  obtain ⟨k, m1, m2, v⟩ := r
  apply Fin.ext
  cases v
  · have : ι.val < 2 := h
    show 0 + ι.val % 2 = ι.val
    omega
  · have : 2 ≤ ι.val := h
    show 2 + ι.val % 2 = ι.val
    omega

theorem inPair_swComp (r : REdge) (k : Fin 2) : InPair r.2.2.2 (swComp r k) := by
  obtain ⟨_, _, _, v⟩ := r
  have := k.isLt
  cases v
  · show 0 + k.val < 2
    omega
  · show 2 ≤ 2 + k.val
    omega

theorem swComp_zero (r : REdge) : swComp r 0 = iMinus r := by
  obtain ⟨_, _, _, v⟩ := r
  cases v <;> rfl

theorem swComp_one (r : REdge) : swComp r 1 = iPlus r := by
  obtain ⟨_, _, _, v⟩ := r
  cases v <;> rfl

theorem swSide_iMinus (r : REdge) : swSide (iMinus r) = 0 := by
  rw [← swComp_zero, swSide_swComp]

theorem swSide_iPlus (r : REdge) : swSide (iPlus r) = 1 := by
  rw [← swComp_one, swSide_swComp]

/-! ## The first column of a ready grid -/

/-- A ready depth has `N_d ≥ 80` (`d ≥ 8`, `bg:ready`(a)). -/
theorem Nd_ge_of_ready {d : ℕ} (hd : 1 ≤ d) (hr : MachineM.ready U d) : 80 ≤ MachineM.Nd d := by
  have h8 := MachineM.ready_ge_eight hd hr
  have h : 1024 ≤ 2 ^ (d + 2) :=
    le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) (show 10 ≤ d + 2 by omega))
  unfold MachineM.Nd
  omega

/-- The sites `ξ(0, j)` of the first column of a grid are distinct. -/
theorem gsite_col_inj {d : ℕ} (hd : 1 ≤ d) (m1 m2 : ℤ) {j j' : ℕ} (hj : j < MachineM.Nd d)
    (hj' : j' < MachineM.Nd d) (h : gsite τ d m1 m2 0 j = gsite τ d m1 m2 0 j') : j = j' := by
  have ha2 : FrameOffsets (a2 τ) := frameOffsets_phase _
  exact (zeta_inj ha2 hd m2 hj hj').1 (congrArg Prod.snd h)

variable (τ) in
open Classical in
/-- The row `j` of a site `ξ(0, j)`, `j < N`, of the first column of the grid at the head of `r`
(`0` at the other sites). -/
def jOf (r : REdge) (ξ : Plane) : ℕ :=
  if h : ∃ j, j < MachineM.Nd (r.1 + 1) ∧ ξ = gsite τ (r.1 + 1) r.2.1 r.2.2.1 0 j then h.choose
  else 0

theorem jOf_gsite {r : REdge} {j : ℕ} (hj : j < MachineM.Nd (r.1 + 1)) :
    jOf τ r (gsite τ (r.1 + 1) r.2.1 r.2.2.1 0 j) = j := by
  have hex : ∃ j', j' < MachineM.Nd (r.1 + 1) ∧
      gsite τ (r.1 + 1) r.2.1 r.2.2.1 0 j = gsite τ (r.1 + 1) r.2.1 r.2.2.1 0 j' := ⟨j, hj, rfl⟩
  rw [jOf, dif_pos hex]
  exact (gsite_col_inj (by omega) _ _ hj hex.choose_spec.1 hex.choose_spec.2).symm

/-- The thresholds `L = (20n - 5, 20n + 5)`, `n = n(d)`, of the sensor of a ready grid of
depth `d`. -/
def sensL (d : ℕ) : Fin 2 → ℕ := ![20 * MachineM.label d - 5, 20 * MachineM.label d + 5]

/-- **The masks on the first column of a ready grid** (`bg:ready`(a)): `g_ι` at `ξ(0, j)` is
`[j < L_{ι mod 2}]`. -/
theorem gB_gsite {d : ℕ} (hd : 1 ≤ d) (hr : MachineM.ready U d) (m1 m2 : ℤ) {j : ℕ}
    (hj : j < MachineM.Nd d) (ι : Fin 4) :
    gB U (bgMap U τ (gsite τ d m1 m2 0 j)) ι = decide (j < sensL d (swSide ι)) := by
  obtain ⟨-, -, hm, -⟩ := MachineM.ready_a hd hr
  have hmm : (cellFormula U d 0 j).gm = decide (j < 20 * MachineM.label d - 5) := by
    show (decide (MachineM.ready U d) && maskMinus U (runAt U d (MachineM.Nd d - 1) j)) = _
    rw [@decide_eq_true _ _ hr, Bool.true_and, runAt_eq hj]
    exact (hm ⟨j, hj⟩).1
  have hmp : (cellFormula U d 0 j).gp = decide (j < 20 * MachineM.label d + 5) := by
    show (decide (MachineM.ready U d) && maskPlus U (runAt U d (MachineM.Nd d - 1) j)) = _
    rw [@decide_eq_true _ _ hr, Bool.true_and, runAt_eq hj]
    exact (hm ⟨j, hj⟩).2
  have h0 : 0 < MachineM.Nd d := by have := MachineM.two_le_Nd d; omega
  unfold gB
  rw [bgMap_k_gsite hd m1 m2 h0 hj]
  show (if ι.val % 2 = 0 then (cellFormula U d 0 j).gm else (cellFormula U d 0 j).gp) = _
  rw [hmm, hmp]
  by_cases h : ι.val % 2 = 0
  · have e : swSide ι = 0 := Fin.ext h
    rw [if_pos h, e]
    rfl
  · have e : swSide ι = 1 := Fin.ext (by show ι.val % 2 = 1; omega)
    rw [if_neg h, e]
    rfl

theorem active_merge (ω : Config (SiteVal U)) (ξ : Plane) (p : PayVal) :
    (merge (bgOf ω ξ) p).IsActive ↔ (ω ξ).IsActive := Iff.rfl

theorem fW_merge (ω : Config (SiteVal U)) (ξ : Plane) (p : PayVal) :
    (merge (bgOf ω ξ) p).fW = (ω ξ).fW := rfl

/-- **The charge at `ξ(0, j)`** (`int:sub-charge`): the coordinate `x_ι` of the cell record at
`ξ(0, j)` carries charge iff `j < 80` and `ι = ⌊j/20⌋`. -/
theorem chW_gsite (hτ : Typical τ) {d : ℕ} (hd : 1 ≤ d) (m1 m2 : ℤ) {j : ℕ}
    (hj : j < MachineM.Nd d) (ι : Fin 4) (w : PV) :
    chW τ U (gsite τ d m1 m2 0 j, .kx ι) w =
      if j < 80 ∧ ι.val = j / 20 then Sensor.bitR w.bitOf else 0 := by
  have h0 : 0 < MachineM.Nd d := by have := MachineM.two_le_Nd d; omega
  have ha1 : FrameOffsets (a1 τ) := frameOffsets_phase _
  have ha2 : FrameOffsets (a2 τ) := frameOffsets_phase _
  have hk := bgMap_k_gsite (U := U) (τ := τ) hd m1 m2 h0 hj
  have hact : (merge (bgMap U τ (gsite τ d m1 m2 0 j)) p0).IsActive :=
    (active_merge _ _ _).2 ((cfg_active (U := U) hτ (fun _ => Spin.plus) _).2
      ⟨d, m1, m2, hd, zeta_free ha1 hd m1 h0, zeta_free ha2 hd m2 hj⟩)
  have hfW : (merge (bgMap U τ (gsite τ d m1 m2 0 j)) p0).fW = true := by
    rw [bgMap, fW_merge, (cfg_grids_c (U := U) hτ (fun _ => Spin.plus) hd m1 m2 h0 hj).1]
    exact decide_eq_true rfl
  unfold chW
  dsimp only
  by_cases hc : j < 80 ∧ ι.val = j / 20
  · rw [if_pos hc, if_pos ⟨cellFormula U d 0 j, hk, hact, hfW,
      (by show min j 80 ≤ 79; omega), (by show ι.val = min j 80 / 20; omega)⟩]
  · rw [if_neg hc, if_neg]
    rintro ⟨c, hc', -, -, h1, h2⟩
    rw [hk, Option.some.injEq] at hc'
    subst hc'
    change min j 80 ≤ 79 at h1
    change ι.val = min j 80 / 20 at h2
    exact hc ⟨by omega, by omega⟩

/-! ## The private coordinates of a ready edge -/

/-- A free bit `y(j)` of a family `y : Fin N → Bool`, at a natural number (`0` for `j ≥ N`). -/
def yAt {N : ℕ} (y : Fin N → Bool) (j : ℕ) : Bool := if h : j < N then y ⟨j, h⟩ else false

theorem yAt_of {N : ℕ} (y : Fin N → Bool) {j : ℕ} (h : j < N) : yAt y j = y ⟨j, h⟩ := dif_pos h

theorem yAt_val {N : ℕ} (y : Fin N → Bool) (j : Fin N) : yAt y j.val = y j := dif_pos j.2

variable (τ U) in
/-- The bit of `ζ` at a coordinate `q` private to `r` (`0` at the other coordinates). -/
def rdBit (r : REdge) (ζ : Q τ U (Sum.inr r) → PV) (q : Coord) : Bool :=
  if h : q.2 ≠ .spin ∧ owner τ U q = Sum.inr r then (ζ ⟨q, h⟩).bitOf else false

theorem rdBit_of {r : REdge} {ζ : Q τ U (Sum.inr r) → PV} {q : Coord}
    (h : q.2 ≠ .spin ∧ owner τ U q = Sum.inr r) : rdBit τ U r ζ q = (ζ ⟨q, h⟩).bitOf :=
  dif_pos h

theorem sens_mem {r : REdge} (hr : MachineM.ready U (r.1 + 1)) {ι : Fin 4}
    (hι : InPair r.2.2.2 ι) {j : ℕ} (hj : j < MachineM.Nd (r.1 + 1)) {f : PFld}
    (hf : f = .kx ι ∨ f = .ky ι) : privPred τ U r (gsite τ (r.1 + 1) r.2.1 r.2.2.1 0 j, f) :=
  Or.inr ⟨hr, ι, hι, Or.inl ⟨j, hj, rfl, hf⟩⟩

/-- A switch copy `x_ι` or a free bit `y_ι` private to `r` lies at a site `ξ(0, j)`, `j < N`, of
the first column, and `ι` is a component of the edge. -/
theorem sens_inv {r : REdge} {ξ : Plane} {f : PFld} {ι : Fin 4} (h : privPred τ U r (ξ, f))
    (hf : f = .kx ι ∨ f = .ky ι) :
    MachineM.ready U (r.1 + 1) ∧ InPair r.2.2.2 ι ∧
      ∃ j, j < MachineM.Nd (r.1 + 1) ∧ ξ = gsite τ (r.1 + 1) r.2.1 r.2.2.1 0 j := by
  rcases h with ha | ⟨hr, ι', hι', hs⟩
  · exfalso
    unfold armPred at ha
    split_ifs at ha <;> rcases ha.2 with ⟨h', -⟩ | ⟨h', -⟩ <;> rcases hf with rfl | rfl <;>
      simp at h'
  · rcases hs with ⟨j, hj, hq, h'⟩ | ⟨-, -, -, h'⟩ | ⟨-, -, -, h'⟩
    · have e : ι = ι' := by
        rcases hf with rfl | rfl <;> rcases h' with h' | h' <;> simp at h' <;> exact h'
      subst e
      exact ⟨hr, hι', j, hj, hq⟩
    · exfalso; rcases hf with rfl | rfl <;> simp at h'
    · exfalso; rcases hf with rfl | rfl <;> simp at h'

theorem sens_root' {r : REdge} (hr : MachineM.ready U (r.1 + 1)) {ι : Fin 4}
    (hι : InPair r.2.2.2 ι) : privPred τ U r (rhead τ r, .kx ι) :=
  sens_root hr hι

/-! ## The identification with the abstract sensor -/

variable (τ U) in
/-- **The abstract sensor configuration of `ζ`** (`pay:sum`): the switches `x⁻`, `x⁺` (the
values `x_ι` at the root `v = ξ(0, 0)`), no free copies, and the candidate free bits
`y^±(j) = y_ι(0, j)`, `j < N`, on the first column. -/
def toCfg (r : REdge) (ζ : Q τ U (Sum.inr r) → PV) : Sensor.Cfg Empty (MachineM.Nd (r.1 + 1)) :=
  (fun k => swv τ U r ζ (swComp r k), fun e => e.elim,
    fun k j => rdBit τ U r ζ (gsite τ (r.1 + 1) r.2.1 r.2.2.1 0 j, .ky (swComp r k)))

variable (τ U) in
/-- **The private coordinates of `r` from an abstract sensor configuration** (`pay:sum`): the arm
`≡ σ_u` (from the tail value `a`), every copy `x_ι` (cell records at `ξ(0, j)`, `ℓ^S`, `ℓ^N` on
the first column) equal to its switch `x^{ι mod 2}`, and `y_ι(0, j) = y^{ι mod 2}(j)`. -/
def ofCfg (r : REdge) (a : PV) (s : Sensor.Cfg Empty (MachineM.Nd (r.1 + 1)))
    (q : Q τ U (Sum.inr r)) : PV :=
  match q.1.2 with
  | .spin => .sp a.spinOf
  | .wW => .wire (some a.spinOf)
  | .wE => .wire (some a.spinOf)
  | .wS => .wire (some a.spinOf)
  | .wN => .wire (some a.spinOf)
  | .kx ι => .bit (s.1 (swSide ι))
  | .ky ι => .bit (yAt (s.2.2 (swSide ι)) (jOf τ r q.1.1))
  | .lSx ι => .bit (s.1 (swSide ι))
  | .lNx ι => .bit (s.1 (swSide ι))

theorem toCfg_switch (r : REdge) (ζ : Q τ U (Sum.inr r) → PV) :
    (toCfg τ U r ζ).1 0 = swv τ U r ζ (iMinus r) ∧ (toCfg τ U r ζ).1 1 = swv τ U r ζ (iPlus r) :=
  ⟨by show swv τ U r ζ (swComp r 0) = _; rw [swComp_zero],
    by show swv τ U r ζ (swComp r 1) = _; rw [swComp_one]⟩

theorem swv_ofCfg {r : REdge} (hr : MachineM.ready U (r.1 + 1)) (a : PV)
    (s : Sensor.Cfg Empty (MachineM.Nd (r.1 + 1))) {ι : Fin 4} (hι : InPair r.2.2.2 ι) :
    swv τ U r (ofCfg τ U r a s) ι = s.1 (swSide ι) := by
  rw [swv_of (sens_root' hr hι)]
  rfl

/-- `toCfg ∘ ofCfg = id`. -/
theorem toCfg_ofCfg {r : REdge} (hr : MachineM.ready U (r.1 + 1)) (a : PV)
    (s : Sensor.Cfg Empty (MachineM.Nd (r.1 + 1))) : toCfg τ U r (ofCfg τ U r a s) = s := by
  obtain ⟨x, c, y⟩ := s
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · funext k
    show swv τ U r (ofCfg τ U r a (x, c, y)) (swComp r k) = x k
    rw [swv_ofCfg hr a _ (inPair_swComp r k), swSide_swComp]
  · funext e
    exact e.elim
  · funext k j
    show rdBit τ U r (ofCfg τ U r a (x, c, y))
      (gsite τ (r.1 + 1) r.2.1 r.2.2.1 0 j, .ky (swComp r k)) = y k j
    rw [rdBit_of ⟨by simp, owner_of (sens_mem hr (inPair_swComp r k) j.2 (Or.inr rfl))⟩]
    show yAt (y (swSide (swComp r k))) (jOf τ r (gsite τ (r.1 + 1) r.2.1 r.2.2.1 0 j)) = y k j
    rw [swSide_swComp, jOf_gsite j.2, yAt_val]

/-- `ofCfg ∘ toCfg = id` on the configurations forced by the factor (`ζ = tgt`). -/
theorem ofCfg_toCfg {r : REdge} {a : PV}
    {ζ : Q τ U (Sum.inr r) → PV} (hg : ∀ q, ζ q = tgt τ U r a ζ q) :
    ofCfg τ U r a (toCfg τ U r ζ) = ζ := by
  funext q
  have hG := hg q
  obtain ⟨⟨ξ, f⟩, hne, ho⟩ := q
  have hq := privPred_of_owner ho
  cases f with
  | spin => exact absurd rfl hne
  | wW => rw [hG]; rfl
  | wE => rw [hG]; rfl
  | wS => rw [hG]; rfl
  | wN => rw [hG]; rfl
  | kx ι =>
    have hι := (ready_of_sens (sens_head hq (Or.inl rfl))).2
    rw [hG]
    show PV.bit (swv τ U r ζ (swComp r (swSide ι))) = PV.bit (swv τ U r ζ ι)
    rw [swComp_swSide hι]
  | lSx ι =>
    have hι := (ready_of_sens (sens_head hq (Or.inr (Or.inr (Or.inl rfl))))).2
    rw [hG]
    show PV.bit (swv τ U r ζ (swComp r (swSide ι))) = PV.bit (swv τ U r ζ ι)
    rw [swComp_swSide hι]
  | lNx ι =>
    have hι := (ready_of_sens (sens_head hq (Or.inr (Or.inr (Or.inr rfl))))).2
    rw [hG]
    show PV.bit (swv τ U r ζ (swComp r (swSide ι))) = PV.bit (swv τ U r ζ ι)
    rw [swComp_swSide hι]
  | ky ι =>
    obtain ⟨-, hι, j, hj, rfl⟩ := sens_inv hq (Or.inr rfl)
    show PV.bit (yAt ((toCfg τ U r ζ).2.2 (swSide ι))
      (jOf τ r (gsite τ (r.1 + 1) r.2.1 r.2.2.1 0 j))) = _
    rw [jOf_gsite hj, yAt_of _ hj]
    show PV.bit (rdBit τ U r ζ (gsite τ (r.1 + 1) r.2.1 r.2.2.1 0 j, .ky (swComp r (swSide ι)))) = _
    rw [swComp_swSide hι, rdBit_of (q := (gsite τ (r.1 + 1) r.2.1 r.2.2.1 0 j, .ky ι)) ⟨hne, ho⟩,
      hG]
    rfl

theorem bit_and_iff {y x g : Bool} :
    PV.bit y = PV.bit ((PV.bit y).bitOf && x && g) ↔ (y = true → x = true ∧ g = true) := by
  cases y <;> cases x <;> cases g <;> decide

/-- **The configurations forced by `W_e` are the consistent sensor configurations**: `ofCfg s`
satisfies `ζ = tgt` (arm `≡ σ_u`, copies equal to the switches, a free bit only where
`x_ι = g_ι = 1`) iff `s` is consistent for `L = (20n - 5, 20n + 5)`. -/
theorem tgt_ofCfg_iff {r : REdge} (hr : MachineM.ready U (r.1 + 1)) (a : PV)
    (s : Sensor.Cfg Empty (MachineM.Nd (r.1 + 1))) :
    (∀ q, ofCfg τ U r a s q = tgt τ U r a (ofCfg τ U r a s) q) ↔
      Sensor.Consistent Empty.elim (sensL (r.1 + 1)) s := by
  have hd : 1 ≤ r.1 + 1 := by omega
  constructor
  · intro h
    refine ⟨fun c => c.elim, fun k j hy => ?_⟩
    have hq := h ⟨(gsite τ (r.1 + 1) r.2.1 r.2.2.1 0 j, .ky (swComp r k)), by simp,
      owner_of (sens_mem hr (inPair_swComp r k) j.2 (Or.inr rfl))⟩
    change PV.bit (yAt (s.2.2 (swSide (swComp r k)))
        (jOf τ r (gsite τ (r.1 + 1) r.2.1 r.2.2.1 0 j))) =
      PV.bit ((PV.bit (yAt (s.2.2 (swSide (swComp r k)))
        (jOf τ r (gsite τ (r.1 + 1) r.2.1 r.2.2.1 0 j)))).bitOf &&
        swv τ U r (ofCfg τ U r a s) (swComp r k) &&
        gB U (bgMap U τ (gsite τ (r.1 + 1) r.2.1 r.2.2.1 0 j)) (swComp r k)) at hq
    rw [swSide_swComp, jOf_gsite j.2, yAt_val, swv_ofCfg hr a s (inPair_swComp r k),
      swSide_swComp, gB_gsite hd hr _ _ j.2, swSide_swComp] at hq
    obtain ⟨h1, h2⟩ := bit_and_iff.1 hq hy
    exact ⟨h1, of_decide_eq_true h2⟩
  · rintro ⟨-, hc⟩ q
    obtain ⟨⟨ξ, f⟩, hne, ho⟩ := q
    have hq := privPred_of_owner ho
    cases f with
    | spin => exact absurd rfl hne
    | wW => rfl
    | wE => rfl
    | wS => rfl
    | wN => rfl
    | kx ι =>
      show PV.bit (s.1 (swSide ι)) = PV.bit (swv τ U r (ofCfg τ U r a s) ι)
      rw [swv_ofCfg hr a s (ready_of_sens (sens_head hq (Or.inl rfl))).2]
    | lSx ι =>
      show PV.bit (s.1 (swSide ι)) = PV.bit (swv τ U r (ofCfg τ U r a s) ι)
      rw [swv_ofCfg hr a s (ready_of_sens (sens_head hq (Or.inr (Or.inr (Or.inl rfl))))).2]
    | lNx ι =>
      show PV.bit (s.1 (swSide ι)) = PV.bit (swv τ U r (ofCfg τ U r a s) ι)
      rw [swv_ofCfg hr a s (ready_of_sens (sens_head hq (Or.inr (Or.inr (Or.inr rfl))))).2]
    | ky ι =>
      obtain ⟨-, hι, j, hj, rfl⟩ := sens_inv hq (Or.inr rfl)
      show PV.bit (yAt (s.2.2 (swSide ι)) (jOf τ r (gsite τ (r.1 + 1) r.2.1 r.2.2.1 0 j))) =
        PV.bit ((PV.bit (yAt (s.2.2 (swSide ι))
          (jOf τ r (gsite τ (r.1 + 1) r.2.1 r.2.2.1 0 j)))).bitOf &&
          swv τ U r (ofCfg τ U r a s) ι &&
          gB U (bgMap U τ (gsite τ (r.1 + 1) r.2.1 r.2.2.1 0 j)) ι)
      rw [jOf_gsite hj, yAt_of _ hj, swv_ofCfg hr a s hι, gB_gsite hd hr _ _ hj]
      refine bit_and_iff.2 fun hy => ?_
      obtain ⟨h1, h2⟩ := hc (swSide ι) ⟨j, hj⟩ hy
      exact ⟨h1, decide_eq_true h2⟩

variable (τ U) in
/-- **The identification of the sensor of a ready edge with the abstract sensor** (`pay:sum`):
the configurations of the private coordinates of `r` forced by `W_e` given the tail value `a`
correspond bijectively (`toCfg`, `ofCfg`) to the consistent configurations of the abstract
sensor `Sensor.Cfg Empty N_d` with `L = (20n - 5, 20n + 5)` (no free copies). -/
def sensorEquiv {r : REdge} (hr : MachineM.ready U (r.1 + 1)) (a : PV) :
    {ζ : Q τ U (Sum.inr r) → PV // ∀ q, ζ q = tgt τ U r a ζ q} ≃
      {s : Sensor.Cfg Empty (MachineM.Nd (r.1 + 1)) //
        Sensor.Consistent Empty.elim (sensL (r.1 + 1)) s} where
  toFun ζ := ⟨toCfg τ U r ζ.1,
    (tgt_ofCfg_iff hr a _).1 (by rw [ofCfg_toCfg ζ.2]; exact ζ.2)⟩
  invFun s := ⟨ofCfg τ U r a s.1, (tgt_ofCfg_iff hr a s.1).2 s.2⟩
  left_inv ζ := Subtype.ext (ofCfg_toCfg ζ.2)
  right_inv s := Subtype.ext (toCfg_ofCfg hr a s.1)

/-- **The support of `W_e` at `ofCfg s`**: `Good` iff `s` is consistent and (P3) holds:
`(x⁻, x⁺) = (0, 1) ⇒ σ_u = σ_v`. -/
theorem good_ofCfg_iff {r : REdge} (hr : MachineM.ready U (r.1 + 1)) (σu σv : Spin)
    (s : Sensor.Cfg Empty (MachineM.Nd (r.1 + 1))) :
    Good τ U (Sum.inr r) (ofCfg τ U r (.sp σu) s) (.sp σu) (.sp σv) ↔
      Sensor.Consistent Empty.elim (sensL (r.1 + 1)) s ∧
        ((s.1 0 = false ∧ s.1 1 = true) → σu = σv) := by
  have e0 : swv τ U r (ofCfg τ U r (.sp σu) s) (iMinus r) = s.1 0 := by
    rw [swv_ofCfg hr _ s (inPair_iMinus r), swSide_iMinus]
  have e1 : swv τ U r (ofCfg τ U r (.sp σu) s) (iPlus r) = s.1 1 := by
    rw [swv_ofCfg hr _ s (inPair_iPlus r), swSide_iPlus]
  show (_ ∧ _) ↔ _
  rw [tgt_ofCfg_iff hr, e0, e1]
  constructor
  · rintro ⟨hc, hp⟩
    exact ⟨hc, fun h => PV.sp.inj (hp h.1 h.2)⟩
  · rintro ⟨hc, hp⟩
    exact ⟨hc, fun h0 h1 => by rw [hp ⟨h0, h1⟩]⟩

theorem inPair_of_ite_ne {v : Bool} {ι : Fin 4} {c : ℝ} (h : (if InPair v ι then c else 0) ≠ 0) :
    InPair v ι := by
  by_contra hn
  exact h (if_neg hn)

/-- **The charge of the private coordinates of a ready edge**: if every copy `x_ι` in the cell
records carries the value `x ι`, the charge is `20 (x⁻ + x⁺)`: the charged coordinates are
`(ξ(0, j), x_{⌊j/20⌋})` with `j < 80` and `⌊j/20⌋` a component of the edge. -/
theorem charge_eq (hτ : Typical τ) {r : REdge} (hr : MachineM.ready U (r.1 + 1))
    (x : Fin 4 → Bool) (ζ : Q τ U (Sum.inr r) → PV)
    (hζ : ∀ (q : Q τ U (Sum.inr r)) (ι : Fin 4), q.1.2 = .kx ι → (ζ q).bitOf = x ι) :
    ∑ q, chW τ U q.1 (ζ q) = 20 * (Sensor.bitR (x (iMinus r)) + Sensor.bitR (x (iPlus r))) := by
  have hd : 1 ≤ r.1 + 1 := by omega
  have hN := Nd_ge_of_ready hd hr
  have key : ∑ p : Fin 4 × Fin 20, (if InPair r.2.2.2 p.1 then Sensor.bitR (x p.1) else 0) =
      ∑ q, chW τ U q.1 (ζ q) := by
    refine Finset.sum_bij_ne_zero
      (fun (p : Fin 4 × Fin 20) (_ : p ∈ Finset.univ)
          (hp : (if InPair r.2.2.2 p.1 then Sensor.bitR (x p.1) else 0) ≠ 0) =>
        (⟨(gsite τ (r.1 + 1) r.2.1 r.2.2.1 0 (20 * p.1.val + p.2.val), .kx p.1), by simp,
          owner_of (sens_mem hr (inPair_of_ite_ne hp)
            (by have := p.1.isLt; have := p.2.isLt; omega) (Or.inl rfl))⟩ :
          Q τ U (Sum.inr r)))
      (fun _ _ _ => Finset.mem_univ _) ?_ ?_ ?_
    · rintro ⟨a, b⟩ _ _ ⟨a', b'⟩ _ _ h
      have h' := congrArg Subtype.val h
      change (gsite τ (r.1 + 1) r.2.1 r.2.2.1 0 (20 * a.val + b.val), PFld.kx a) =
        (gsite τ (r.1 + 1) r.2.1 r.2.2.1 0 (20 * a'.val + b'.val), PFld.kx a') at h'
      obtain ⟨hg, hk⟩ := Prod.mk.inj h'
      have ha : a = a' := PFld.kx.inj hk
      rw [← ha] at hg
      have hab := gsite_col_inj hd _ _ (j := 20 * a.val + b.val) (j' := 20 * a.val + b'.val)
        (by have := a.isLt; have := b.isLt; omega) (by have := a.isLt; have := b'.isLt; omega) hg
      have hb : b = b' := Fin.ext (by omega)
      rw [ha, hb]
    · intro q _ hq
      obtain ⟨⟨ξ, f⟩, hne, ho⟩ := q
      cases f with
      | kx ι =>
        obtain ⟨-, hι, j, hj, rfl⟩ := sens_inv (privPred_of_owner ho) (Or.inl rfl)
        change chW τ U (gsite τ (r.1 + 1) r.2.1 r.2.2.1 0 j, .kx ι) _ ≠ 0 at hq
        rw [chW_gsite hτ hd _ _ hj] at hq
        by_cases hc : j < 80 ∧ ι.val = j / 20
        · rw [if_pos hc] at hq
          have hb : x ι = true := by
            rw [← hζ ⟨(gsite τ (r.1 + 1) r.2.1 r.2.2.1 0 j, .kx ι), hne, ho⟩ ι rfl]
            by_contra hn
            rw [Bool.not_eq_true] at hn
            rw [hn] at hq
            exact hq rfl
          refine ⟨(ι, ⟨j % 20, Nat.mod_lt _ (by norm_num)⟩), Finset.mem_univ _, ?_, ?_⟩
          · show (if InPair r.2.2.2 ι then Sensor.bitR (x ι) else 0) ≠ 0
            rw [if_pos hι, hb]
            simp [Sensor.bitR]
          · apply Subtype.ext
            show (gsite τ (r.1 + 1) r.2.1 r.2.2.1 0 (20 * ι.val + j % 20), PFld.kx ι) =
              (gsite τ (r.1 + 1) r.2.1 r.2.2.1 0 j, PFld.kx ι)
            rw [show 20 * ι.val + j % 20 = j by omega]
        · rw [if_neg hc] at hq
          exact absurd rfl hq
      | spin => exact absurd rfl hq
      | wW => exact absurd rfl hq
      | wE => exact absurd rfl hq
      | wS => exact absurd rfl hq
      | wN => exact absurd rfl hq
      | ky ι => exact absurd rfl hq
      | lSx ι => exact absurd rfl hq
      | lNx ι => exact absurd rfl hq
    · intro p _ hp
      have hι := inPair_of_ite_ne hp
      have hj : 20 * p.1.val + p.2.val < MachineM.Nd (r.1 + 1) := by
        have := p.1.isLt; have := p.2.isLt; omega
      show _ = chW τ U (gsite τ (r.1 + 1) r.2.1 r.2.2.1 0 (20 * p.1.val + p.2.val), .kx p.1)
        (ζ ⟨(gsite τ (r.1 + 1) r.2.1 r.2.2.1 0 (20 * p.1.val + p.2.val), .kx p.1), _⟩)
      rw [chW_gsite hτ hd _ _ hj, if_pos hι,
        if_pos ⟨by have := p.1.isLt; have := p.2.isLt; omega,
          by have := p.2.isLt; omega⟩]
      congr 1
      exact (hζ _ _ (by rfl)).symm
  rw [← key, Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Fin.sum_univ_four]
  obtain ⟨k, m1, m2, v⟩ := r
  cases v <;> simp [InPair, iMinus, iPlus] <;> ring

/-- The charge at `ofCfg s` is `20 (x⁻ + x⁺)`. -/
theorem charge_ofCfg (hτ : Typical τ) {r : REdge} (hr : MachineM.ready U (r.1 + 1)) (a : PV)
    (s : Sensor.Cfg Empty (MachineM.Nd (r.1 + 1))) :
    ∑ q, chW τ U q.1 (ofCfg τ U r a s q) = 20 * (Sensor.bitR (s.1 0) + Sensor.bitR (s.1 1)) := by
  have hζ : ∀ (q : Q τ U (Sum.inr r)) (ι : Fin 4), q.1.2 = .kx ι →
      (ofCfg τ U r a s q).bitOf = s.1 (swSide ι) := by
    intro q ι h
    obtain ⟨⟨ξ, f⟩, hne, ho⟩ := q
    simp only at h
    subst h
    rfl
  rw [charge_eq hτ hr (fun ι => s.1 (swSide ι)) _ hζ, swSide_iMinus, swSide_iPlus]

/-- **`W_e` at `ofCfg s` is the abstract sensor weight** `Sensor.weight s`
(`1[consistent] 1[(x⁻,x⁺) = (0,1) ⇒ σ_u = σ_v] e^{-20β(x⁻+x⁺)}`). -/
theorem Wf_ofCfg (hτ : Typical τ) (β : ℝ) {r : REdge} (hr : MachineM.ready U (r.1 + 1))
    (σu σv : Spin) (s : Sensor.Cfg Empty (MachineM.Nd (r.1 + 1))) :
    Wf τ U β (Sum.inr r) (ofCfg τ U r (.sp σu) s) (.sp σu) (.sp σv) =
      Sensor.weight Empty.elim (sensL (r.1 + 1)) β σu σv s := by
  unfold Wf Sensor.weight
  rw [charge_ofCfg hτ hr]
  have hexp : Real.exp (-β * (20 * (Sensor.bitR (s.1 0) + Sensor.bitR (s.1 1)))) =
      Real.exp (-20 * β * (Sensor.bitR (s.1 0) + Sensor.bitR (s.1 1))) := by
    congr 1; ring
  rw [hexp]
  by_cases hg : Good τ U (Sum.inr r) (ofCfg τ U r (.sp σu) s) (.sp σu) (.sp σv)
  · obtain ⟨hc, hp⟩ := (good_ofCfg_iff hr σu σv s).1 hg
    rw [if_pos hg, if_pos hc, if_pos hp]
    ring
  · rw [if_neg hg]
    by_cases hc : Sensor.Consistent Empty.elim (sensL (r.1 + 1)) s
    · rw [if_pos hc, if_neg fun hp => hg ((good_ofCfg_iff hr σu σv s).2 ⟨hc, hp⟩)]
      ring
    · rw [if_neg hc]
      ring

/-! ## The edge sums of ready edges -/

/-- **The edge sum of a ready edge is the abstract sensor sum** (`pay:sum`, the identification):
`Z_e(σ_u, σ_v) = ∑_{s ∈ Sensor.Cfg Empty N} Sensor.weight s` with `L = (20n - 5, 20n + 5)`, by
the reindexing `ofCfg` (injective, `toCfg_ofCfg`; onto the support of `W_e`, `ofCfg_toCfg`;
`W_e ∘ ofCfg = Sensor.weight`, `Wf_ofCfg`). -/
theorem Zf_eq_sensorSum (hτ : Typical τ) (β : ℝ) {r : REdge} (hr : MachineM.ready U (r.1 + 1))
    (s t : Spin) :
    (elimData τ U β).Zf (Sum.inr r) (.sp s) (.sp t) =
      ∑ c : Sensor.Cfg Empty (MachineM.Nd (r.1 + 1)),
        Sensor.weight Empty.elim (sensL (r.1 + 1)) β s t c := by
  symm
  show _ = ∑ ζ : Q τ U (Sum.inr r) → PV, Wf τ U β (Sum.inr r) ζ (.sp s) (.sp t)
  refine Finset.sum_of_injOn (ofCfg τ U r (.sp s)) (fun x _ y _ h => ?_)
    (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)) (fun ζ _ hζ => ?_)
    (fun x _ => (Wf_ofCfg hτ β hr s t x).symm)
  · rw [← toCfg_ofCfg (τ := τ) (U := U) hr (.sp s) x, h, toCfg_ofCfg hr]
  · unfold Wf
    rw [if_neg, zero_mul]
    intro hg
    exact hζ ⟨toCfg τ U r ζ, Finset.mem_coe.2 (Finset.mem_univ _), ofCfg_toCfg hg.1⟩

/-- **`pay:sum`, `ρ_d = 1`**: `Z_e(σ_u, σ_v) = H_n + G_n 1[σ_u = σ_v]`, `n = n(d)`. -/
theorem Zf_ready (hτ : Typical τ) (β : ℝ) {r : REdge} (hr : MachineM.ready U (r.1 + 1))
    (s t : Spin) :
    (elimData τ U β).Zf (Sum.inr r) (.sp s) (.sp t) =
      Hc (MachineM.label (r.1 + 1)) β +
        Gc (MachineM.label (r.1 + 1)) β * (if s = t then 1 else 0) := by
  obtain ⟨-, -, -, hN⟩ := MachineM.ready_a (by omega) hr
  have hn : 1 ≤ MachineM.label (r.1 + 1) := by unfold MachineM.label; omega
  rw [Zf_eq_sensorSum hτ β hr s t]
  exact Sensor.pay_sum Empty.elim hn hN β s t

/-- **`pay:sum`, `ρ_d = 1`, as a coupling**:
`Z_e(σ_u, σ_v) = sqrt(H_n (H_n + G_n)) e^{J_n σ_u σ_v}`, `J_n = Jc (b_n)`. -/
theorem Zf_ready_coupling (hτ : Typical τ) (β : ℝ) {r : REdge}
    (hr : MachineM.ready U (r.1 + 1)) (s t : Spin) :
    (elimData τ U β).Zf (Sum.inr r) (.sp s) (.sp t) =
      Real.sqrt (Hc (MachineM.label (r.1 + 1)) β *
          (Hc (MachineM.label (r.1 + 1)) β + Gc (MachineM.label (r.1 + 1)) β)) *
        Real.exp (Jc (bc (MachineM.label (r.1 + 1)) β) * Ising.val s * Ising.val t) := by
  rw [Zf_ready hτ β hr s t, Sensor.coupling]

end UPD.BG

/-
# `pay:effective`: the effective Ising model

New in this project (session 10). For a typical phase `τ`, the Gibbs measures for `βΦ` concentrated
on the background `𝔟_τ` are exactly the measures `L(ν)` (the lift of `pay:elim`, read on the payload
coordinates through the relabelling and completed by the background, `liftCfg`), `ν` a Gibbs measure
of the Ising model on `Γ_τ` (`Payload/Graph.lean`). The chain (BLUEPRINT G.6, item 3):
`frozen_bridge` (measures on `Ω` concentrated on `𝔟_τ` and the frozen system on the payload
coordinates), `pay_factor` (frozen system and the factor system `γ` of the edges, along
`relabel : Coord ≃ Plane ⊕ Σ e, Q e`), `ElimData.elim` (`γ` and `γ̄`, the factors `Z_e` and `κ_v` on
the spins), and `Gibbs.isGibbs_iff_recode` (`γ̄` and the Ising model on `Γ_τ`: "constant factors do
not change a specification").

The edge sums `Z_e` (`pay:sum`) enter as explicit hypotheses (`ZfHyp`; proved separately):
`Z_e` is constant for a site edge, `1` for a real edge of a depth that is not ready, and
`H_n + G_n 1[σ_u = σ_v]` (`n = n(d)`) for a real edge of a ready depth `d`.

* `edgeC`, `edgeF`, `Zf_eq`: `Z_e(σ_u, σ_v) = C_e e^{f_e(σ)}` with `C_e > 0` independent of `σ`
  (`Sensor.coupling`: `C_e = sqrt(H_n (H_n + G_n))` and `f_e = J_n(β) σ_u σ_v` on a ready edge);
* `sum_edgeF` (the edges of `Γ_τ`): the ready real edges with an end in `Λ` correspond bijectively,
  by `e ↦ {u(e), v(e)}`, to the edges of `Γ_τ` meeting `Λ` (`redge_inj`, `rtail_mem_nbr`), with
  `f_e = J_e σ_u σ_v`; so `∑_e f_e = energySum Λ σ`;
* **`recode_W`**, **`recode_kind`**: the hypotheses of `isGibbs_iff_recode` for `γ̄`, `ι = PV.sp`;
* **`liftCfg`**, **`pay_effective`**, **`map_spin_liftCfg`** (the spin marginal of `liftCfg ν` is
  `ν`), and **`hEff_of`**, **`hS_of`**: the arguments `hEff`, `hS` of `Proof/Main2.lean` and
  `Proof/Steps.lean` with `L := fun τ => liftCfg U τ β`.
-/
import UndecidablePhaseDiagram.Payload.Factor
import UndecidablePhaseDiagram.Gibbs.Recode

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace UPD.BG

open UPD.Scaffold

/-! ## The edge sums, as hypotheses -/

/-- The edge sums `Z_e` of `pay:sum` as used by `pay:effective`: for a site edge `Z_e` does not
depend on the end values; for a real edge of a depth `d = r.1 + 1` that is not ready, `Z_e = 1`;
for a real edge of a ready depth `d`, `Z_e(σ_u, σ_v) = H_n + G_n 1[σ_u = σ_v]`, `n = n(d)`. -/
structure ZfHyp (U : Machine) (τ : ℕ → Bool × Bool) (β : ℝ) : Prop where
  site : ∀ (ξ : Plane) (a b a' b' : PV),
    (elimData τ U β).Zf (Sum.inl ξ) a b = (elimData τ U β).Zf (Sum.inl ξ) a' b'
  idle : ∀ r : REdge, ¬ MachineM.ready U (r.1 + 1) → ∀ a b : PV,
    (elimData τ U β).Zf (Sum.inr r) a b = 1
  ready : ∀ r : REdge, MachineM.ready U (r.1 + 1) → ∀ s t : Spin,
    (elimData τ U β).Zf (Sum.inr r) (.sp s) (.sp t) =
      Hc (MachineM.label (r.1 + 1)) β +
        Gc (MachineM.label (r.1 + 1)) β * (if s = t then 1 else 0)

variable {U : Machine} {τ : ℕ → Bool × Bool} {β : ℝ}

/-! ## The edges of `Γ_τ` -/

theorem Jc_bc_pos (n : ℕ) (β : ℝ) : 0 < Jc (bc n β) := by
  unfold Jc
  have hb := bc_pos n β
  have h1 : 1 < 1 + 1 / bc n β := by have := one_div_pos.2 hb; linarith
  exact div_pos (Real.log_pos h1) (by norm_num)

theorem Ising.val_ne_zero (s : Spin) : Ising.val s ≠ 0 := by
  cases s <;> norm_num [Ising.val]

/-- The tail of a real edge is a root of its depth. -/
theorem rtail_root (r : REdge) : ∃ m1 m2 : ℤ, rtail τ r = root τ (r.1 + 1) m1 m2 := by
  unfold rtail
  split_ifs
  · exact ⟨_, _, rfl⟩
  · exact ⟨_, _, rfl⟩

/-- The tail of a real edge of a ready depth is a neighbour of its head in `Γ_τ`. -/
theorem rtail_mem_nbr {r : REdge} (hr : MachineM.ready U (r.1 + 1)) :
    rtail τ r ∈ (Gamma U τ β).nbr (rhead τ r) := by
  rw [mem_Gamma_nbr]
  refine ⟨r.1 + 1, r.2.1, r.2.2.1, by omega, hr, rfl, ?_⟩
  unfold rtail
  split_ifs
  · exact Or.inr (Or.inr (Or.inr rfl))
  · exact Or.inr (Or.inl rfl)

/-- A real edge is determined by its unordered pair of ends. -/
theorem redge_inj {r r' : REdge} (h : s(rtail τ r, rhead τ r) = s(rtail τ r', rhead τ r')) :
    r = r' := by
  obtain ⟨k, m1, m2, v⟩ := r
  obtain ⟨k', m1', m2', v'⟩ := r'
  simp only [rtail, rhead] at h
  rcases Sym2.eq_iff.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · cases v <;> cases v' <;> simp only [Bool.false_eq_true, ↓reduceIte] at h1 h2 <;>
      obtain ⟨a1, a2, a3⟩ := root_inj' h1 <;> obtain ⟨b1, b2, b3⟩ := root_inj' h2 <;>
      first
        | omega
        | (simp only [Prod.mk.injEq, and_true]; omega)
  · cases v <;> cases v' <;> simp only [Bool.false_eq_true, ↓reduceIte] at h1 h2 <;>
      obtain ⟨a1, a2, a3⟩ := root_inj' h1 <;> obtain ⟨b1, b2, b3⟩ := root_inj' h2 <;> omega

/-! ## The edge sums as constants times Ising factors -/

variable (U τ β) in
/-- The constant factor `C_e` of the edge sum `Z_e`: `Z_e` itself for a site edge (it is constant),
`sqrt(H_n (H_n + G_n))` for a real edge of a ready depth, `1` for the other real edges. -/
def edgeC : Ed → ℝ
  | Sum.inl ξ => (elimData τ U β).Zf (Sum.inl ξ) (.sp .plus) (.sp .plus)
  | Sum.inr r => if MachineM.ready U (r.1 + 1) then
      Real.sqrt (Hc (MachineM.label (r.1 + 1)) β *
        (Hc (MachineM.label (r.1 + 1)) β + Gc (MachineM.label (r.1 + 1)) β))
    else 1

variable (U τ β) in
/-- The exponent `f_e(σ)` of the edge sum `Z_e`: `J_{n(d)}(β) σ_u σ_v` for a real edge of a ready
depth `d`, `0` for the other edges. -/
def edgeF (σ : Plane → Spin) : Ed → ℝ
  | Sum.inl _ => 0
  | Sum.inr r => if MachineM.ready U (r.1 + 1) then
      Jc (bc (MachineM.label (r.1 + 1)) β) * Ising.val (σ (rtail τ r)) * Ising.val (σ (rhead τ r))
    else 0

theorem edgeC_pos (e : Ed) : 0 < edgeC U τ β e := by
  rcases e with ξ | r
  · exact (elimData τ U β).Zf_pos' _ _ _
  · simp only [edgeC]
    split_ifs
    · exact Real.sqrt_pos.2 (mul_pos (Hc_pos _ _) (add_pos (Hc_pos _ _) (Gc_pos _ _)))
    · exact one_pos

theorem edgeF_ne_zero (σ : Plane → Spin) {r : REdge} (hr : MachineM.ready U (r.1 + 1)) :
    edgeF U τ β σ (Sum.inr r) ≠ 0 := by
  simp only [edgeF, if_pos hr]
  exact mul_ne_zero (mul_ne_zero (Jc_bc_pos _ _).ne' (Ising.val_ne_zero _))
    (Ising.val_ne_zero _)

theorem ready_of_edgeF_ne_zero {σ : Plane → Spin} {e : Ed} (h : edgeF U τ β σ e ≠ 0) :
    ∃ r : REdge, e = Sum.inr r ∧ MachineM.ready U (r.1 + 1) := by
  rcases e with ξ | r
  · exact absurd rfl h
  · by_cases hr : MachineM.ready U (r.1 + 1)
    · exact ⟨r, rfl, hr⟩
    · simp only [edgeF, if_neg hr] at h
      exact absurd rfl h

/-- **`pay:effective`** ("by `pay:sum`, the factor `Z_e` is constant for edges of non-ready depths
and proportional to `e^{J_{n(d)} σ_u σ_v}` for ready ones"): `Z_e(σ_u, σ_v) = C_e e^{f_e(σ)}`. -/
theorem Zf_eq
    (hZ1 : ∀ (ξ : Plane) (a b a' b' : PV),
      (elimData τ U β).Zf (Sum.inl ξ) a b = (elimData τ U β).Zf (Sum.inl ξ) a' b')
    (hZ2 : ∀ r : REdge, ¬ MachineM.ready U (r.1 + 1) → ∀ a b : PV,
      (elimData τ U β).Zf (Sum.inr r) a b = 1)
    (hZ3 : ∀ r : REdge, MachineM.ready U (r.1 + 1) → ∀ s t : Spin,
      (elimData τ U β).Zf (Sum.inr r) (.sp s) (.sp t) =
        Hc (MachineM.label (r.1 + 1)) β +
          Gc (MachineM.label (r.1 + 1)) β * (if s = t then 1 else 0))
    (σ : Plane → Spin) (e : Ed) :
    (elimData τ U β).Zf e (.sp (σ (etail τ e))) (.sp (σ (ehead τ e))) =
      edgeC U τ β e * Real.exp (edgeF U τ β σ e) := by
  rcases e with ξ | r
  · simp only [edgeC, edgeF, Real.exp_zero, mul_one]
    exact hZ1 ξ _ _ _ _
  · by_cases hr : MachineM.ready U (r.1 + 1)
    · simp only [edgeC, edgeF, if_pos hr]
      rw [← Sensor.coupling]
      exact hZ3 r hr _ _
    · simp only [edgeC, edgeF, if_neg hr, Real.exp_zero, one_mul]
      exact hZ2 r hr _ _

/-- **`pay:effective`** ("roots of different depths are different sites, and the roots of depth
`d` with these edges form a square lattice"): the exponents `f_e` of the edges with an end in `Λ`
add up to the Ising energy of `Γ_τ` on the edges meeting `Λ`; `e ↦ {u(e), v(e)}` is a bijection
from the ready real edges with an end in `Λ` onto the edges of `Γ_τ` meeting `Λ`. -/
theorem sum_edgeF (σ : Plane → Spin) (Λ : Finset Plane) :
    ∑ e ∈ (elimData τ U β).edgesOf Λ, edgeF U τ β σ e = (Gamma U τ β).energySum Λ σ := by
  unfold Gibbs.IsingGraph.energySum
  refine Finset.sum_bij_ne_zero (fun e _ _ => s(etail τ e, ehead τ e)) ?_ ?_ ?_ ?_
  · intro e he hne
    obtain ⟨r, rfl, hr⟩ := ready_of_edgeF_ne_zero hne
    rw [Gibbs.ElimData.mem_edgesOf] at he
    rw [Gibbs.IsingGraph.mem_edgesMeeting]
    rcases he with h | h
    · exact ⟨rtail τ r, h, rhead τ r, (Gamma U τ β).symm _ _ (rtail_mem_nbr hr), rfl⟩
    · exact ⟨rhead τ r, h, rtail τ r, rtail_mem_nbr hr, Sym2.eq_swap⟩
  · intro e₁ _ h₁ e₂ _ h₂ h
    obtain ⟨r₁, rfl, -⟩ := ready_of_edgeF_ne_zero h₁
    obtain ⟨r₂, rfl, -⟩ := ready_of_edgeF_ne_zero h₂
    rw [redge_inj h]
  · intro p hp _
    rw [Gibbs.IsingGraph.mem_edgesMeeting] at hp
    obtain ⟨u, hu, w, hw, rfl⟩ := hp
    obtain ⟨d, m1, m2, hd, hr, rfl, hw'⟩ := (mem_Gamma_nbr β).1 hw
    obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
    rcases hw' with rfl | rfl | rfl | rfl
    · refine ⟨Sum.inr (k, m1 + 1, m2, false), ?_,
        edgeF_ne_zero (r := (k, m1 + 1, m2, false)) σ hr, ?_⟩
      · rw [Gibbs.ElimData.mem_edgesOf]
        left
        show root τ (k + 1) (m1 + 1 - 1) m2 ∈ Λ
        rwa [add_sub_cancel_right]
      · show s(root τ (k + 1) (m1 + 1 - 1) m2, root τ (k + 1) (m1 + 1) m2) = _
        rw [add_sub_cancel_right]
    · refine ⟨Sum.inr (k, m1, m2, false), ?_, edgeF_ne_zero (r := (k, m1, m2, false)) σ hr, ?_⟩
      · rw [Gibbs.ElimData.mem_edgesOf]
        exact Or.inr hu
      · exact Sym2.eq_swap
    · refine ⟨Sum.inr (k, m1, m2 + 1, true), ?_,
        edgeF_ne_zero (r := (k, m1, m2 + 1, true)) σ hr, ?_⟩
      · rw [Gibbs.ElimData.mem_edgesOf]
        left
        show root τ (k + 1) m1 (m2 + 1 - 1) ∈ Λ
        rwa [add_sub_cancel_right]
      · show s(root τ (k + 1) m1 (m2 + 1 - 1), root τ (k + 1) m1 (m2 + 1)) = _
        rw [add_sub_cancel_right]
    · refine ⟨Sum.inr (k, m1, m2, true), ?_, edgeF_ne_zero (r := (k, m1, m2, true)) σ hr, ?_⟩
      · rw [Gibbs.ElimData.mem_edgesOf]
        exact Or.inr hu
      · exact Sym2.eq_swap
  · intro e _ hne
    obtain ⟨r, rfl, hr⟩ := ready_of_edgeF_ne_zero hne
    obtain ⟨a, b, hab⟩ := rtail_root (τ := τ) r
    show edgeF U τ β σ (Sum.inr r) = (Gamma U τ β).J s(rtail τ r, rhead τ r) *
      Gibbs.IsingGraph.pairVal σ s(rtail τ r, rhead τ r)
    simp only [edgeF, if_pos hr, Gibbs.IsingGraph.pairVal_mk]
    rw [hab, rhead, Gamma_J_root β (by omega) hr]
    ring

/-! ## The hypotheses of the recoding -/

/-- **`pay:effective`** (the recoding): on the recoded configurations `PV.sp ∘ σ`, the weights of
`γ̄` are a positive constant times the Ising weights of `Γ_τ`. -/
theorem recode_W
    (hZ1 : ∀ (ξ : Plane) (a b a' b' : PV),
      (elimData τ U β).Zf (Sum.inl ξ) a b = (elimData τ U β).Zf (Sum.inl ξ) a' b')
    (hZ2 : ∀ r : REdge, ¬ MachineM.ready U (r.1 + 1) → ∀ a b : PV,
      (elimData τ U β).Zf (Sum.inr r) a b = 1)
    (hZ3 : ∀ r : REdge, MachineM.ready U (r.1 + 1) → ∀ s t : Spin,
      (elimData τ U β).Zf (Sum.inr r) (.sp s) (.sp t) =
        Hc (MachineM.label (r.1 + 1)) β +
          Gc (MachineM.label (r.1 + 1)) β * (if s = t then 1 else 0))
    (Λ : Finset Plane) :
    ∃ c : ℝ, 0 < c ∧ ∀ σ : Plane → Spin,
      (elimData τ U β).gammaBar.toHard.W Λ (fun v => PV.sp (σ v)) =
        c * (Gamma U τ β).weight Λ σ := by
  refine ⟨∏ e ∈ (elimData τ U β).edgesOf Λ, edgeC U τ β e,
    Finset.prod_pos fun e _ => edgeC_pos e, fun σ => ?_⟩
  rw [Gibbs.ElimData.gammaBar_W]
  have hκ : ∏ v ∈ Λ, (elimData τ U β).κ v (PV.sp (σ v)) = 1 :=
    Finset.prod_eq_one fun v _ =>
      show (if PFld.spin.ok (PV.sp (σ v)) = true then (1 : ℝ) else 0) = 1 from if_pos rfl
  have hZ : ∏ e ∈ (elimData τ U β).edgesOf Λ, (elimData τ U β).Zf e
        (PV.sp (σ ((elimData τ U β).tail e))) (PV.sp (σ ((elimData τ U β).head e))) =
      ∏ e ∈ (elimData τ U β).edgesOf Λ, (edgeC U τ β e * Real.exp (edgeF U τ β σ e)) :=
    Finset.prod_congr rfl fun e _ => Zf_eq hZ1 hZ2 hZ3 σ e
  rw [hκ, mul_one, hZ, Finset.prod_mul_distrib, ← Real.exp_sum, sum_edgeF]
  rfl

/-- **`pay:effective`** (the recoding): where a weight of `γ̄` is positive, the spins of its sites
have the kind of a spin (the vertex factor `κ_v`). -/
theorem recode_kind (Λ : Finset Plane) (x : Plane → PV)
    (h : 0 < (elimData τ U β).gammaBar.toHard.W Λ x) : ∀ v ∈ Λ, x v ∈ Set.range PV.sp := by
  intro v hv
  rw [Gibbs.ElimData.gammaBar_W] at h
  by_contra hx
  have h0 : (elimData τ U β).κ v (x v) = 0 := by
    show (if PFld.spin.ok (x v) = true then (1 : ℝ) else 0) = 0
    rw [if_neg]
    intro hok
    exact hx ⟨_, PV.sp_spinOf hok⟩
  rw [Finset.prod_eq_zero hv h0, mul_zero] at h
  exact lt_irrefl _ h

/-! ## The lift on `Ω` -/

theorem measurable_unrelabel :
    Measurable fun (x : Gibbs.ECoord Plane Ed (Q τ U) → PV) (c : Coord) => x (relabel τ U c) :=
  Measurable.of_eval fun _ => measurable_pi_apply _

theorem measurable_relabelC :
    Measurable fun (c : Coord → PV) (i : Gibbs.ECoord Plane Ed (Q τ U)) =>
      c ((relabel τ U).symm i) :=
  Measurable.of_eval fun _ => measurable_pi_apply _

theorem map_unrelabel_map_relabelC (m : Measure (Coord → PV)) :
    (m.map fun c i => c ((relabel τ U).symm i)).map (fun x c => x (relabel τ U c)) = m := by
  rw [Measure.map_map measurable_unrelabel measurable_relabelC]
  have e : ((fun (x : Gibbs.ECoord Plane Ed (Q τ U) → PV) (c : Coord) => x (relabel τ U c)) ∘
      fun (c : Coord → PV) (i : Gibbs.ECoord Plane Ed (Q τ U)) => c ((relabel τ U).symm i)) =
      id := by
    funext c q
    simp
  rw [e, Measure.map_id]

theorem map_relabelC_map_unrelabel (M : Measure (Gibbs.ECoord Plane Ed (Q τ U) → PV)) :
    (M.map fun x c => x (relabel τ U c)).map (fun c i => c ((relabel τ U).symm i)) = M := by
  rw [Measure.map_map measurable_relabelC measurable_unrelabel]
  have e : ((fun (c : Coord → PV) (i : Gibbs.ECoord Plane Ed (Q τ U)) =>
      c ((relabel τ U).symm i)) ∘
      fun (x : Gibbs.ECoord Plane Ed (Q τ U) → PV) (c : Coord) => x (relabel τ U c)) = id := by
    funext x i
    simp
  rw [e, Measure.map_id]

variable (U τ β) in
/-- **The lift `L(ν)` on `Ω`** (`pay:effective`: "the measures `L(ν)`, completed by the fixed
values of `pay:factor`(a)"): the lift of `pay:elim` of the recoded Ising measure `ν.map (PV.sp ∘ ·)`,
read on the payload coordinates through the relabelling and completed by the background `𝔟_τ`. -/
def liftCfg (ν : Measure (Plane → Spin)) : Measure (Config (SiteVal U)) :=
  (((elimData τ U β).lift (ν.map fun σ v => PV.sp (σ v))).map
    fun x c => x (relabel τ U c)).map (ofCoords (bgMap U τ))

/-! ## `pay:effective` -/

/-- **`pay:effective`** (in the form of BLUEPRINT G.6, item 3), with the edge sums `Z_e` as
explicit hypotheses: for typical `τ`, a measure `μ'` on `Ω` is a Gibbs measure for `βΦ`
concentrated on the background `𝔟_τ` iff `μ' = L(ν)` (`liftCfg`) for a Gibbs measure `ν` of the
Ising model on `Γ_τ`. -/
theorem pay_effective (hτ : Typical τ)
    (hZ1 : ∀ (ξ : Plane) (a b a' b' : PV),
      (elimData τ U β).Zf (Sum.inl ξ) a b = (elimData τ U β).Zf (Sum.inl ξ) a' b')
    (hZ2 : ∀ r : REdge, ¬ MachineM.ready U (r.1 + 1) → ∀ a b : PV,
      (elimData τ U β).Zf (Sum.inr r) a b = 1)
    (hZ3 : ∀ r : REdge, MachineM.ready U (r.1 + 1) → ∀ s t : Spin,
      (elimData τ U β).Zf (Sum.inr r) (.sp s) (.sp t) =
        Hc (MachineM.label (r.1 + 1)) β +
          Gc (MachineM.label (r.1 + 1)) β * (if s = t then 1 else 0))
    (μ' : Measure (Config (SiteVal U))) :
    (IsGibbs β (Phi U) μ' ∧ ∀ᵐ ω ∂μ', bgOf ω = bgMap U τ) ↔
      ∃ ν : Measure (Plane → Spin), (Gamma U τ β).toWeightSystem.IsDLR ν ∧
        μ' = liftCfg U τ β ν := by
  haveI : Nonempty PV := ⟨.bit false⟩
  have hrec := fun ν' : Measure (Plane → PV) =>
    Gibbs.isGibbs_iff_recode PV.sp PV.spinOf (Gamma U τ β) (elimData τ U β).gammaBar
      (fun _ => rfl) recode_kind (recode_W hZ1 hZ2 hZ3) ν'
  constructor
  · intro h
    obtain ⟨hm, he⟩ := (frozen_bridge β hτ μ').1 h
    obtain ⟨ν', hν', hM⟩ := ((elimData τ U β).elim _).1 ((pay_factor hτ β _).1 hm)
    obtain ⟨ν, hν, rfl⟩ := (hrec ν').1 hν'
    refine ⟨ν, hν, ?_⟩
    calc μ' = (μ'.map toCoords).map (ofCoords (bgMap U τ)) := he
      _ = (((μ'.map toCoords).map fun c i => c ((relabel τ U).symm i)).map
            fun x c => x (relabel τ U c)).map (ofCoords (bgMap U τ)) := by
          rw [map_unrelabel_map_relabelC]
      _ = liftCfg U τ β ν := by rw [hM]; rfl
  · rintro ⟨ν, hν, rfl⟩
    have hν' := (hrec _).2 ⟨ν, hν, rfl⟩
    have hM := ((elimData τ U β).elim _).2 ⟨_, hν', rfl⟩
    have hm : (frozenSystem β (bgMap U τ)).IsGibbs
        (((elimData τ U β).lift (ν.map fun σ v => PV.sp (σ v))).map
          fun x c => x (relabel τ U c)) := by
      rw [pay_factor hτ β, map_relabelC_map_unrelabel]
      exact hM
    exact isGibbs_map_ofCoords β hτ hm

/-- **`pay:elim`, the inverse of the lift is the spin marginal**, on `Ω`: the spin marginal of
`L(ν)` is `ν` (the spin of `ofCoords 𝔟 c` at `ξ` is that of `c (ξ, spin)`, and
`relabel (ξ, spin)` is the vertex `ξ`). -/
theorem map_spin_liftCfg {ν : Measure (Plane → Spin)}
    (hν : (Gamma U τ β).toWeightSystem.IsDLR ν) :
    (liftCfg U τ β ν).map (fun ω ξ => (ω ξ).spin) = ν := by
  haveI : IsProbabilityMeasure ν := hν.1
  haveI : IsProbabilityMeasure (ν.map fun σ v => PV.sp (σ v)) :=
    (Measure.isProbabilityMeasure_map_iff (Gibbs.measurable_recode PV.sp).aemeasurable).2 inferInstance
  have hsp : Measurable (fun (ω : Config (SiteVal U)) (ξ : Plane) => (ω ξ).spin) :=
    Measurable.of_eval fun ξ =>
      (Measurable.of_discrete (f := fun s : SiteVal U => s.spin)).comp (measurable_pi_apply ξ)
  have hso : Measurable (fun (s : Plane → PV) (ξ : Plane) => (s ξ).spinOf) :=
    Gibbs.measurable_decode PV.spinOf
  unfold liftCfg
  rw [Measure.map_map hsp (measurable_ofCoords _),
    Measure.map_map (hsp.comp (measurable_ofCoords _)) measurable_unrelabel]
  have e : ((fun (ω : Config (SiteVal U)) (ξ : Plane) => (ω ξ).spin) ∘ ofCoords (bgMap U τ)) ∘
      (fun (x : Gibbs.ECoord Plane Ed (Q τ U) → PV) (c : Coord) => x (relabel τ U c)) =
      (fun (s : Plane → PV) (ξ : Plane) => (s ξ).spinOf) ∘ Gibbs.ElimData.spins := by
    funext x ξ
    show (x (relabel τ U (ξ, .spin))).spinOf = (x (Sum.inl ξ)).spinOf
    rw [relabel_spin]
  rw [e, ← Measure.map_map hso Gibbs.ElimData.measurable_spins, Gibbs.ElimData.map_spins_lift,
    Measure.map_map hso (Gibbs.measurable_recode PV.sp)]
  have e2 : ((fun (s : Plane → PV) (ξ : Plane) => (s ξ).spinOf) ∘
      fun (σ : Plane → Spin) (v : Plane) => PV.sp (σ v)) = id := rfl
  rw [e2, Measure.map_id]

/-! ## The arguments `hEff`, `hS` of `thm:main` -/

/-- **`pay:effective`** in the shape of the argument `hEff` of `thm_main_i_of`, `thm_main_ii_of`
(`Proof/Main2.lean`) and `thm_main_moreover_of` (`Proof/Steps.lean`), with
`L := fun τ => liftCfg U τ β`, from the edge sums for every typical `τ`. -/
theorem hEff_of (hZ : ∀ τ, Typical τ → ZfHyp U τ β) :
    ∀ τ, Typical τ → ∀ μ' : Measure (Config (SiteVal U)),
      (IsGibbs β (Phi U) μ' ∧ ∀ᵐ ω ∂μ', bgOf ω = bgMap U τ) ↔
        ∃ ν : Measure (Plane → Spin), (Gamma U τ β).toWeightSystem.IsDLR ν ∧
          μ' = liftCfg U τ β ν :=
  fun τ hτ μ' => pay_effective hτ (hZ τ hτ).site (hZ τ hτ).idle (hZ τ hτ).ready μ'

/-- The spin marginal of `liftCfg U τ β ν` is `ν`, in the shape of the argument `hS` of
`thm_main_ii_of` (`Proof/Main2.lean`) with `L := fun τ => liftCfg U τ β` (no hypothesis on the edge
sums or on `τ` is needed). -/
theorem hS_of :
    ∀ τ, Typical τ → ∀ ν : Measure (Plane → Spin), (Gamma U τ β).toWeightSystem.IsDLR ν →
      (liftCfg U τ β ν).map (fun ω ξ => (ω ξ).spin) = ν :=
  fun _ _ _ hν => map_spin_liftCfg hν

end UPD.BG

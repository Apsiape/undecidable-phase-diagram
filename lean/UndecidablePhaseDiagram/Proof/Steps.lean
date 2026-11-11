/-
# `thm:main`, Steps 1, 2 (uniqueness) and 4, with `pay:effective` as an explicit hypothesis

New in this project (session 10). The parts of the proof of `thm:main` (paper Section 7) that use
`pay:effective` only through its statement. That statement enters as the explicit argument `hEff`
(for a fixed machine `U`, a fixed `β` and ANY map `L`, the lift of `pay:elim` completed by the
fixed coordinates): for every typical `τ`, a measure `μ'` on `Ω` is a Gibbs measure for `βΦ` with
background `𝔟_τ` almost surely iff `μ' = L τ ν` for a Gibbs measure `ν` of the Ising model on
`Γ_τ`. No property of `L` (measurability, covariance) is used.

* **`step1`** (Step 1): a translation-invariant Gibbs measure `μ` is `∫ μ^τ Haar(dτ)`, and for
  Haar-almost every `τ`, `τ` is typical and `μ^τ = L τ ν` with `ν` Gibbs for `Γ_τ`
  (`freeze_c`, `map_phaseMap`, `ae_typical_phaseMap`, then `hEff`).
* **`tiGibbs_unique`** (Step 2, uniqueness half of `thm:main`(i)): if `U` does not halt on `n` and
  `β ∈ J_n`, two translation-invariant Gibbs measures are equal: every coupling of `Γ_τ` is at most
  `J̄ = J(2^14)` (`Gamma_J_le`: a ready depth `d` has `U` halting on `n(d)`, so `n(d) ≠ n`,
  `|β/log 2 - n(d)| ≥ 19/20` by `prf:windows`(d) and `b_{n(d)}(β) ≥ 2^14` by `prf:thermal`(b)),
  `4 tanh J̄ = 4/32769 < 1`, every vertex has at most four neighbours, so `Γ_τ` has one Gibbs
  measure (`set:dobrushin`, from `H1`), and the conditional laws agree Haar-almost everywhere.
* **`thm_main_moreover_of`** (Step 4, `thm:main` "Moreover"): for a Gibbs measure `ν` of `Γ_τ`
  (`exists_isDLR`), `L τ ν` is a Gibbs measure for `βΦ` with background `𝔟_τ`; it is not
  translation invariant (`T_{e₁}` would fix `𝔟_τ`, hence the quarters `Y_τ`, but the quarter phase
  of `T_{e₁} Y_τ` is `τ + e₁ ≠ τ`, `qphase_shift`); different typical phases give different
  measures (`bgMap_injOn`); and the typical phases are uncountable (Haar measure has no atoms,
  `haar_singleton`, and gives them measure `1`, `ae_typical`).
-/
import UndecidablePhaseDiagram.Background.Conditioning
import UndecidablePhaseDiagram.Background.Ready
import UndecidablePhaseDiagram.Payload.Graph
import UndecidablePhaseDiagram.Gibbs.Existence
import UndecidablePhaseDiagram.Proof.Windows

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace UPD.BG

open UPD.Scaffold

variable {U : Machine}

/-! ## Step 1: every translation-invariant Gibbs measure is an average over backgrounds -/

/-- **`thm:main`, Step 1** (`prf:eq-disint`), from `pay:effective` (`hEff`): a translation-invariant
Gibbs measure `μ` is `μ = ∫ μ^τ Haar(dτ)` (`condLaw μ`: the conditional laws given the quarter
phase), and for Haar-almost every `τ`, `τ` is typical and `μ^τ = L τ ν` for a Gibbs measure `ν` of
the Ising model on `Γ_τ`. -/
theorem step1 (L : (ℕ → Bool × Bool) → Measure (Plane → Spin) → Measure (Config (SiteVal U)))
    {β : ℝ}
    (hEff : ∀ τ, Typical τ → ∀ μ' : Measure (Config (SiteVal U)),
      (IsGibbs β (Phi U) μ' ∧ ∀ᵐ ω ∂μ', bgOf ω = bgMap U τ) ↔
        ∃ ν : Measure (Plane → Spin), (Gamma U τ β).toWeightSystem.IsDLR ν ∧ μ' = L τ ν)
    {μ : Measure (Config (SiteVal U))} [IsProbabilityMeasure μ] (hμ : IsTIGibbs U β μ) :
    μ = condLaw μ ∘ₘ haar ∧
      ∀ᵐ τ ∂haar, Typical τ ∧ ∃ ν : Measure (Plane → Spin),
        (Gamma U τ β).toWeightSystem.IsDLR ν ∧ condLaw μ τ = L τ ν := by
  have hleg := hμ.1.2.1
  have hti : ∀ a : Plane, μ.map (shift a) = μ := hμ.2
  obtain ⟨hdis, hae⟩ := freeze_c β hμ.1 (ae_typical_phaseMap hleg hti)
  rw [map_phaseMap hleg hti] at hdis hae
  refine ⟨hdis, hae.mono fun τ hτ => ⟨hτ.1, ?_⟩⟩
  obtain ⟨htyp, hG, -, hset⟩ := hτ
  exact (hEff τ htyp (condLaw μ τ)).1 ⟨hG, hset.mono fun ω hω => hω.2⟩

/-! ## Step 2: the couplings of `Γ_τ` when `U` does not halt on `n` -/

/-- `J_b = ½ log(1 + 1/b)` is antitone in `b > 0`. -/
theorem Jc_antitone {b b' : ℝ} (hb : 0 < b) (h : b ≤ b') : Jc b' ≤ Jc b := by
  unfold Jc
  have hb' : 0 < b' := hb.trans_le h
  have h1 : 1 / b' ≤ 1 / b := one_div_le_one_div_of_le hb h
  have h2 : 0 < 1 + 1 / b' := by positivity
  have h3 : Real.log (1 + 1 / b') ≤ Real.log (1 + 1 / b) := Real.log_le_log h2 (by linarith)
  linarith

/-- `prf:thermal`(b): `4 tanh J(2^14) = 4/32769 < 1`. -/
theorem four_tanh_Jc_lt_one : 4 * Real.tanh (Jc (2 ^ 14)) < 1 := by
  rw [tanh_Jc (by norm_num)]
  norm_num

/-- If `β ∈ J_n` and `m ≠ n`, then `|β / log 2 - m| ≥ 19/20` (`prf:windows`(d)). -/
theorem windows_sep {n m : ℕ} (hn : 1 ≤ n) {β : ℝ} (hβ : β ∈ J n) (hm : m ≠ n) :
    (19 / 20 : ℝ) ≤ |β / Real.log 2 - m| := by
  have hw := abs_lt.1 (windows_d hn hβ)
  rcases Nat.lt_or_gt_of_ne hm with h | h
  · have h' : (m : ℝ) + 1 ≤ n := by exact_mod_cast h
    exact le_abs.2 (Or.inl (by linarith [hw.1]))
  · have h' : (n : ℝ) + 1 ≤ m := by exact_mod_cast h
    exact le_abs.2 (Or.inr (by linarith [hw.2]))

/-- **`thm:main`, Step 2**: if `U` does not halt on `n` and `β ∈ J_n`, every coupling of `Γ_τ` is at
most `J(2^14)`: a coupling is `0` or `J_{n(d)}(β)` for a ready depth `d`; `U` halts on `n(d)`
(`bg:ready`(a)), so `n(d) ≠ n`, and `b_{n(d)}(β) ≥ 2^14` (`prf:thermal`(b)). -/
theorem Gamma_J_le {n : ℕ} (hn : 1 ≤ n) {β : ℝ} (hβ : β ∈ J n) (hh : ¬ U.HaltsOn n)
    (τ : ℕ → Bool × Bool) (e : Sym2 Plane) : (Gamma U τ β).J e ≤ Jc (2 ^ 14) := by
  rcases Gamma_J_cases β e with h | ⟨d, hd, hr, h⟩
  · rw [h]
    exact Jc_nonneg (by norm_num)
  · rw [h]
    have hl : MachineM.label d ≠ n := fun hl => hh (hl ▸ (MachineM.ready_a hd hr).2.1)
    exact Jc_antitone (by norm_num) (thermal_b _ β (windows_sep hn hβ hl)).1

/-- **`thm:main`, Step 2** (with `set:dobrushin`): if `U` does not halt on `n` and `β ∈ J_n`, the
Ising model on `Γ_τ` has at most one Gibbs measure. -/
theorem Gamma_isDLR_unique (h1 : H1) {n : ℕ} (hn : 1 ≤ n) {β : ℝ} (hβ : β ∈ J n)
    (hh : ¬ U.HaltsOn n) (τ : ℕ → Bool × Bool) {ν ν' : Measure (Plane → Spin)}
    (hν : (Gamma U τ β).toWeightSystem.IsDLR ν) (hν' : (Gamma U τ β).toWeightSystem.IsDLR ν') :
    ν = ν' :=
  (Gamma U τ β).dobrushin_unique h1 (Jc (2 ^ 14)) (Gamma_J_le hn hβ hh τ)
    (card_Gamma_nbr_le β) four_tanh_Jc_lt_one hν hν'

/-- **`thm:main`(i), uniqueness half** (Steps 1 and 2), from `H1` and `pay:effective` (`hEff`): if
`U` does not halt on `n` and `β ∈ J_n`, `βΦ` has at most one translation-invariant Gibbs
measure. -/
theorem tiGibbs_unique (h1 : H1)
    (L : (ℕ → Bool × Bool) → Measure (Plane → Spin) → Measure (Config (SiteVal U))) {β : ℝ}
    (hEff : ∀ τ, Typical τ → ∀ μ' : Measure (Config (SiteVal U)),
      (IsGibbs β (Phi U) μ' ∧ ∀ᵐ ω ∂μ', bgOf ω = bgMap U τ) ↔
        ∃ ν : Measure (Plane → Spin), (Gamma U τ β).toWeightSystem.IsDLR ν ∧ μ' = L τ ν)
    {n : ℕ} (hn : 1 ≤ n) (hβ : β ∈ J n) (hh : ¬ U.HaltsOn n)
    {μ μ' : Measure (Config (SiteVal U))} (hμ : IsTIGibbs U β μ) (hμ' : IsTIGibbs U β μ') :
    μ = μ' := by
  haveI := hμ.1.1
  haveI := hμ'.1.1
  obtain ⟨e, he⟩ := step1 L hEff hμ
  obtain ⟨e', he'⟩ := step1 L hEff hμ'
  have hk : ∀ᵐ τ ∂haar, condLaw μ τ = condLaw μ' τ := by
    filter_upwards [he, he'] with τ hτ hτ'
    obtain ⟨-, ν, hν, hL⟩ := hτ
    obtain ⟨-, ν', hν', hL'⟩ := hτ'
    rw [hL, hL', Gamma_isDLR_unique h1 hn hβ hh τ hν hν']
  calc μ = condLaw μ ∘ₘ haar := e
    _ = condLaw μ' ∘ₘ haar := Measure.bind_congr_right hk
    _ = μ' := e'.symm

/-! ## Step 4: Gibbs measures that are not translation invariant -/

/-- The quarter of `𝔟_τ` at `ξ` is `Y_τ(ξ)`. -/
theorem bgMap_q (τ : ℕ → Bool × Bool) (ξ : Plane) : (bgMap U τ ξ).q = qtilingOf τ ξ := rfl

/-- Different typical phases have different backgrounds (their quarters have different phases). -/
theorem bgMap_injOn : Set.InjOn (bgMap U) {τ | Typical τ} := by
  intro τ hτ τ' hτ' h
  have hq : qtilingOf τ = qtilingOf τ' := funext fun ξ => by
    rw [← bgMap_q (U := U), ← bgMap_q (U := U), h]
  have h2 := (qtilingOf_spec hτ'.1).2
  rw [← hq] at h2
  exact (qtilingOf_spec hτ.1).2.unique h2

/-- For typical `τ`, `T_{e₁} 𝔟_τ ≠ 𝔟_τ`: the quarter phase of `T_{e₁} Y_τ` is `τ + e₁ ≠ τ`
(`scf:quarter`). -/
theorem shift_bgMap_ne {τ : ℕ → Bool × Bool} (hτ : Typical τ) :
    shift e1 (bgMap U τ) ≠ bgMap U τ := by
  intro h
  have hY : shift e1 (qtilingOf τ) = qtilingOf τ := funext fun ξ => by
    have := congrArg BgVal.q (congrFun h ξ)
    exact this
  have hP := (qtilingOf_spec hτ.1).2
  have h' : IsQPhase (shift e1 (qtilingOf τ)) τ := by rw [hY]; exact hP
  have hd := (qphase_shift hP e1 h' 1).1
  norm_num [e1] at hd

/-- A probability measure whose background is almost surely `𝔟_τ`, `τ` typical, is not
translation invariant. -/
theorem not_ti_of_ae_bg {τ : ℕ → Bool × Bool} (hτ : Typical τ)
    {μ : Measure (Config (SiteVal U))} [IsProbabilityMeasure μ]
    (hbg : ∀ᵐ ω ∂μ, bgOf ω = bgMap U τ) : ¬ IsTranslationInvariantMeasure μ := by
  intro hti
  have h1 : ∀ᵐ ω ∂(μ.map (shift e1)), bgOf ω = bgMap U τ := by rw [hti e1]; exact hbg
  have h2 := ae_of_ae_map (measurable_shift e1).aemeasurable h1
  obtain ⟨ω, hω1, hω2⟩ := (hbg.and h2).exists
  rw [bgOf_shift, hω1] at hω2
  exact shift_bgMap_ne hτ hω2

/-- Haar measure has no atoms: `{τ}` lies in the prefix cylinders of mass `4^{-n}`. -/
theorem haar_singleton (τ : ℕ → Bool × Bool) : haar {τ} = 0 := by
  have hle : ∀ n : ℕ, haar {τ} ≤ ((Fintype.card (Bool × Bool) : ℝ≥0∞)⁻¹) ^ n := fun n => by
    rw [← unifSeq_cyl n τ, ← haar_def]
    exact measure_mono fun υ hυ => by
      rw [Set.mem_singleton_iff] at hυ
      subst hυ
      exact fun m _ => rfl
  have hlt : ((Fintype.card (Bool × Bool) : ℝ≥0∞))⁻¹ < 1 := by
    rw [ENNReal.inv_lt_one]
    simp
  exact le_antisymm (ge_of_tendsto' (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hlt) hle)
    zero_le

/-- Haar measure on phases has no atoms. -/
instance haar_noAtoms : NullSingletonClass haar := ⟨haar_singleton⟩

/-- The typical phases are uncountable (Haar measure has no atoms and gives them measure `1`). -/
theorem not_countable_typical : ¬ {τ : ℕ → Bool × Bool | Typical τ}.Countable := by
  intro hT
  obtain ⟨τ, h1, h2⟩ := (ae_typical.and (hT.ae_notMem haar)).exists
  exact h2 h1

/-- **`thm:main`, "Moreover"** (Step 4), from `pay:effective` (`hEff`): `βΦ` has uncountably many
Gibbs measures that are not translation invariant: for typical `τ` and a Gibbs measure `ν` of the
Ising model on `Γ_τ` (`exists_isDLR`), `L τ ν` is one, and different typical `τ` give different
measures. (`0 < β` is not used beyond `hEff`.) -/
theorem thm_main_moreover_of
    (L : (ℕ → Bool × Bool) → Measure (Plane → Spin) → Measure (Config (SiteVal U))) {β : ℝ}
    (hEff : ∀ τ, Typical τ → ∀ μ' : Measure (Config (SiteVal U)),
      (IsGibbs β (Phi U) μ' ∧ ∀ᵐ ω ∂μ', bgOf ω = bgMap U τ) ↔
        ∃ ν : Measure (Plane → Spin), (Gamma U τ β).toWeightSystem.IsDLR ν ∧ μ' = L τ ν)
    (_hβ : 0 < β) :
    ¬ {μ : Measure (Config (SiteVal U)) |
        IsGibbs β (Phi U) μ ∧ ¬ IsTranslationInvariantMeasure μ}.Countable := by
  intro hc
  have hex := fun τ => Gibbs.IsingGraph.exists_isDLR (Gamma U τ β)
  let ν : (ℕ → Bool × Bool) → Measure (Plane → Spin) := fun τ => Classical.choose (hex τ)
  have hν : ∀ τ, (Gamma U τ β).toWeightSystem.IsDLR (ν τ) := fun τ => Classical.choose_spec (hex τ)
  have hG : ∀ τ, Typical τ →
      IsGibbs β (Phi U) (L τ (ν τ)) ∧ ∀ᵐ ω ∂(L τ (ν τ)), bgOf ω = bgMap U τ :=
    fun τ hτ => (hEff τ hτ _).2 ⟨ν τ, hν τ, rfl⟩
  have hmaps : Set.MapsTo (fun τ => L τ (ν τ)) {τ | Typical τ}
      {μ | IsGibbs β (Phi U) μ ∧ ¬ IsTranslationInvariantMeasure μ} := by
    intro τ hτ
    obtain ⟨hg, hb⟩ := hG τ hτ
    haveI := hg.1
    exact ⟨hg, not_ti_of_ae_bg hτ hb⟩
  have hinj : Set.InjOn (fun τ => L τ (ν τ)) {τ | Typical τ} := by
    intro τ hτ τ' hτ' h
    obtain ⟨hg, hb⟩ := hG τ hτ
    obtain ⟨-, hb'⟩ := hG τ' hτ'
    haveI := hg.1
    have hb'' : ∀ᵐ ω ∂(L τ (ν τ)), bgOf ω = bgMap U τ' := by
      have e : L τ (ν τ) = L τ' (ν τ') := h
      rw [e]; exact hb'
    obtain ⟨ω, h1, h2⟩ := (hb.and hb'').exists
    exact bgMap_injOn hτ hτ' (h1.symm.trans h2)
  exact not_countable_typical (hmaps.countable_of_injOn hinj hc)

end UPD.BG

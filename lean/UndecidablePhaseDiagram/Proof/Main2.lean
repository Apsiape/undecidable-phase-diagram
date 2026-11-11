/-
# `thm:main`(i) and (ii) from the statement of `pay:effective`, by averaging

New in this project (session 10). The two cases of `thm:main` (paper Section 7, Steps 1 to 3)
from two properties of the lift `L` of `pay:elim` completed by the fixed coordinates, taken as
explicit arguments for a fixed machine `U`, a fixed `β` and an arbitrary map `L`:

* `hEff` (the statement of `pay:effective`, as in `Proof/Steps.lean`): for typical `τ`, a measure
  `μ'` on `Ω` is a Gibbs measure for `βΦ` with background `𝔟_τ` almost surely iff `μ' = L τ ν` for
  a Gibbs measure `ν` of the Ising model on `Γ_τ`;
* `hS` (in `thm_main_ii_of` only; `pay:elim`: the inverse of the lift is the spin marginal): for
  typical `τ` and `ν` Gibbs on `Γ_τ`, the spin marginal of `L τ ν` is `ν`.

No measurability of anything in the phase `τ` is used: where the paper integrates over phases
(`μ^± = ∫ δ_{𝔟_τ} ⊗ L(ν^{τ,±}) Haar(dτ)`), we fix one typical `τ` and average the translates of the
non-translation-invariant Gibbs measures `L τ ν` over growing boxes (`Gibbs/Average.lean`,
Krylov–Bogolyubov).

* **`thm_main_i_of`** (`thm:main`(i)): existence of a translation-invariant Gibbs measure
  (`exists_tiGibbs_of`: a typical `τ`, a Gibbs measure `ν` of `Γ_τ` by compactness, `L τ ν` Gibbs by
  `hEff`, then `exists_ti_gibbs`) and uniqueness (`tiGibbs_unique`, Steps 1 and 2, from `H1`).
* **`thm_main_ii_of`** (`thm:main`(ii), Step 3): fix a typical `τ` and one ready depth `d ≥ 1` with
  `n(d) = n` (`readyDepths_infinite`). `exists_pm_Gamma`: the Ising model on `Γ_τ` has two Gibbs
  measures `ν₁`, `ν₂`, products over the components (`isDLR_glue`, component map `depthOf`) of the
  images of the plus and minus states of `set:peierls` (coupling `J_n(β)`, `e^{J_n(β)} > 3` by
  `prf:thermal`(a), `prf:windows`(d)) under `m ↦ 𝐫_d(m)` (`squareIso`) on the component of depth
  `d`, and of the SAME Gibbs measure on every other component; so `ν₁(σ_ξ = +) ≥ ν₂(σ_ξ = +)` at
  every site, with a gap `≥ 2/3 - 1/3` at the roots of depth `d` (translation invariance of the
  plus and minus states). For `f` = the number of spins `+` in the block `[0, 4^{d+1})²`
  (`blockF`), every translate of the block contains a root of depth `d` (`exists_block_root`:
  spacing `4^{d+1}`, `rfree`), so `∫ f ∘ T_a dL(ν₁) - ∫ f ∘ T_a dL(ν₂) ≥ 1/3` for every `a` (by
  `hS`); the same holds for the box averages (`le_boxAvg_sub`), and `exists_ti_gibbs_avg₂` gives
  translation-invariant Gibbs measures `μ̄₁`, `μ̄₂` with `∫ f dμ̄₁ - ∫ f dμ̄₂ ≥ 1/3`, so
  `μ̄₁ ≠ μ̄₂`.
  This is the paper's Step 3 in substance (Peierls on the component of a depth in `𝒟_n`, the other
  components identical), with one depth of `𝒟_n` instead of all of them and an averaged local
  observable instead of the event "the origin is a root of depth `d`". `H1` is not used.
-/
import UndecidablePhaseDiagram.Proof.Steps
import UndecidablePhaseDiagram.Gibbs.Average
import UndecidablePhaseDiagram.Interaction.Basic

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace UPD.BG

open UPD.Scaffold

variable {U : Machine}

/-! ## `thm:main`(i) -/

/-- A typical phase exists (`ae_typical`). -/
theorem exists_typical_phase : ∃ τ : ℕ → Bool × Bool, Typical τ := ae_typical.exists

/-- **Existence of a translation-invariant Gibbs measure** for `βΦ`, from `pay:effective` (`hEff`):
for typical `τ` and a Gibbs measure `ν` of `Γ_τ`, `L τ ν` is a Gibbs measure for `βΦ`, and its
Cesàro averages have a translation-invariant Gibbs cluster point (`exists_ti_gibbs`). -/
theorem exists_tiGibbs_of
    (L : (ℕ → Bool × Bool) → Measure (Plane → Spin) → Measure (Config (SiteVal U))) {β : ℝ}
    (hEff : ∀ τ, Typical τ → ∀ μ' : Measure (Config (SiteVal U)),
      (IsGibbs β (Phi U) μ' ∧ ∀ᵐ ω ∂μ', bgOf ω = bgMap U τ) ↔
        ∃ ν : Measure (Plane → Spin), (Gamma U τ β).toWeightSystem.IsDLR ν ∧ μ' = L τ ν) :
    ∃ μ : Measure (Config (SiteVal U)), IsTIGibbs U β μ := by
  obtain ⟨τ, hτ⟩ := exists_typical_phase
  obtain ⟨ν, hν⟩ := Gibbs.IsingGraph.exists_isDLR (Gamma U τ β)
  have hG := ((hEff τ hτ (L τ ν)).2 ⟨ν, hν, rfl⟩).1
  obtain ⟨μ, h1, h2⟩ := Gibbs.exists_ti_gibbs phi_isInteraction phi_nearestNeighbour
    phi_translationInvariant hG
  exact ⟨μ, h1, h2⟩

/-- **`thm:main`(i)** (Steps 1 and 2), from `H1` and `pay:effective` (`hEff`): if `U` does not halt
on `n` and `β ∈ J_n`, `βΦ` has exactly one translation-invariant Gibbs measure. -/
theorem thm_main_i_of (h1 : H1)
    (L : (ℕ → Bool × Bool) → Measure (Plane → Spin) → Measure (Config (SiteVal U))) {β : ℝ}
    (hEff : ∀ τ, Typical τ → ∀ μ' : Measure (Config (SiteVal U)),
      (IsGibbs β (Phi U) μ' ∧ ∀ᵐ ω ∂μ', bgOf ω = bgMap U τ) ↔
        ∃ ν : Measure (Plane → Spin), (Gamma U τ β).toWeightSystem.IsDLR ν ∧ μ' = L τ ν)
    {n : ℕ} (hn : 1 ≤ n) (hβ : β ∈ J n) (hh : ¬ U.HaltsOn n) :
    ∃! μ : Measure (Config (SiteVal U)), IsTIGibbs U β μ := by
  obtain ⟨μ, hμ⟩ := exists_tiGibbs_of L hEff
  exact ⟨μ, hμ, fun μ' hμ' => tiGibbs_unique h1 L hEff hn hβ hh hμ' hμ⟩

/-! ## Products over the labels of measures on the label sets -/

section Glue

variable {V ι : Type} [DecidableEq ι] (c : V → ι)

/-- A configuration on the vertices with label `i`, extended by `+` elsewhere. -/
def extLabel (i : ι) (σ : {v // c v = i} → Spin) : V → Spin :=
  fun v => if h : c v = i then σ ⟨v, h⟩ else .plus

theorem measurable_extLabel (i : ι) : Measurable (extLabel c i) := by
  refine Measurable.of_eval fun v => ?_
  by_cases h : c v = i
  · simp only [extLabel, h, dif_pos]
    exact measurable_pi_apply _
  · simp only [extLabel, h, dif_neg, not_false_eq_true]
    exact measurable_const

/-- Restricting the extension to the label set gives back the configuration. -/
theorem restr_extLabel (i : ι) (σ : {v // c v = i} → Spin) :
    (fun (v : {v // c v = i}) => extLabel c i σ v.1) = σ := by
  funext v
  simp [extLabel, v.2]

/-- The measure on `V → Spin` whose part on the label set of `i` is `ρ i`, extended by `+`. -/
def compMeas (ρ : ∀ i, Measure ({v // c v = i} → Spin)) (i : ι) : Measure (V → Spin) :=
  (ρ i).map (extLabel c i)

/-- The product over the labels `i` of the measures `ρ i` on the label sets (`glue`). -/
def glueMeas (ρ : ∀ i, Measure ({v // c v = i} → Spin)) : Measure (V → Spin) :=
  (Measure.infinitePi (compMeas c ρ)).map (Gibbs.glue c)

theorem map_restr_compMeas (ρ : ∀ i, Measure ({v // c v = i} → Spin)) (i : ι) :
    (compMeas c ρ i).map (fun σ (v : {v // c v = i}) => σ v.1) = ρ i := by
  rw [compMeas, Measure.map_map (g := fun σ (v : {v // c v = i}) => σ v.1)
    (Measurable.of_eval fun v => measurable_pi_apply v.1) (measurable_extLabel c i)]
  have : ((fun σ (v : {v // c v = i}) => σ v.1) ∘ extLabel c i) = id :=
    funext fun σ => restr_extLabel c i σ
  rw [this, Measure.map_id]

theorem isProbabilityMeasure_compMeas (ρ : ∀ i, Measure ({v // c v = i} → Spin))
    [∀ i, IsProbabilityMeasure (ρ i)] (i : ι) : IsProbabilityMeasure (compMeas c ρ i) :=
  (Measure.isProbabilityMeasure_map_iff (measurable_extLabel c i).aemeasurable).2 inferInstance

/-- **Products of Gibbs measures of the components** (`isDLR_glue`): if `c` is a component map and
every `ρ i` is a Gibbs measure of the induced subgraph on the label set of `i`, the product is a
Gibbs measure of `G`. -/
theorem isDLR_glueMeas [DecidableEq V] (G : Gibbs.IsingGraph V) (hc : G.IsComponentMap c)
    (ρ : ∀ i, Measure ({v // c v = i} → Spin))
    (hρ : ∀ i, (G.restrict c i).toWeightSystem.IsDLR (ρ i)) :
    G.toWeightSystem.IsDLR (glueMeas c ρ) := by
  haveI : ∀ i, IsProbabilityMeasure (ρ i) := fun i => (hρ i).1
  haveI : ∀ i, IsProbabilityMeasure (compMeas c ρ i) := isProbabilityMeasure_compMeas c ρ
  refine G.isDLR_glue hc (compMeas c ρ) fun i => ?_
  rw [map_restr_compMeas]
  exact hρ i

theorem measurableSet_eval_eq {W : Type} (w : W) (s : Spin) :
    MeasurableSet {σ : W → Spin | σ w = s} :=
  (measurableSet_singleton s).preimage (measurable_pi_apply w)

/-- The law of the spin at `v` under the product is its law under the measure of the label of
`v`. -/
theorem glueMeas_real_eval (ρ : ∀ i, Measure ({v // c v = i} → Spin))
    [∀ i, IsProbabilityMeasure (ρ i)] (v : V) {i : ι} (h : c v = i) (s : Spin) :
    (glueMeas c ρ).real {σ | σ v = s} = (ρ i).real {σ | σ ⟨v, h⟩ = s} := by
  subst h
  haveI : ∀ i, IsProbabilityMeasure (compMeas c ρ i) := isProbabilityMeasure_compMeas c ρ
  rw [glueMeas, map_measureReal_apply (Gibbs.measurable_glue c) (measurableSet_eval_eq v s)]
  have e1 : Gibbs.glue c ⁻¹' {σ : V → Spin | σ v = s} =
      (fun x : ∀ i, V → Spin => x (c v)) ⁻¹' {σ | σ v = s} := rfl
  rw [e1, ← map_measureReal_apply (measurable_pi_apply (c v)) (measurableSet_eval_eq v s),
    Measure.infinitePi_map_eval, compMeas,
    map_measureReal_apply (measurable_extLabel c (c v)) (measurableSet_eval_eq v s)]
  congr 1
  ext σ
  simp [extLabel]

end Glue

/-! ## The local observable and its averages -/

/-- The indicator of the spin `+`. -/
def plusInd (s : Spin) : ℝ := if s = .plus then 1 else 0

theorem abs_plusInd_le (s : Spin) : ‖plusInd s‖ ≤ 1 := by
  unfold plusInd
  split_ifs <;> simp

/-- The number of spins `+` in a finite set of sites `B`. -/
def blockF (B : Finset Plane) (ω : Config (SiteVal U)) : ℝ := ∑ b ∈ B, plusInd (ω b).spin

/-- `blockF B` depends only on the sites in `B`. -/
theorem blockF_local (B : Finset Plane) (ω ω' : Config (SiteVal U))
    (h : ∀ ξ ∈ B, ω ξ = ω' ξ) : blockF B ω = blockF B ω' :=
  Finset.sum_congr rfl fun b hb => by rw [h b hb]

theorem integral_plusInd_eval (ν : Measure (Plane → Spin)) [IsProbabilityMeasure ν] (ξ : Plane) :
    ∫ σ, plusInd (σ ξ) ∂ν = ν.real {σ | σ ξ = .plus} := by
  have : (fun σ : Plane → Spin => plusInd (σ ξ)) = {σ | σ ξ = .plus}.indicator 1 := by
    funext σ
    simp [plusInd, Set.indicator_apply]
  rw [this, integral_indicator_one (measurableSet_eval_eq ξ .plus)]

/-- The spin field `ω ↦ (σ_ξ(ω))_ξ` is measurable. -/
theorem measurable_spinField :
    Measurable (fun (ω : Config (SiteVal U)) (ξ : Plane) => (ω ξ).spin) :=
  Measurable.of_eval fun ξ =>
    (Measurable.of_discrete (f := fun s : SiteVal U => s.spin)).comp (measurable_pi_apply ξ)

/-- `∫ (number of spins + in B) ∘ T_a dμ = ∑_{b ∈ B} ν(σ_{b - a} = +)` when the spin marginal of
`μ` is `ν`. -/
theorem integral_blockF_shift {μ : Measure (Config (SiteVal U))} [IsProbabilityMeasure μ]
    {ν : Measure (Plane → Spin)} (hS : μ.map (fun ω ξ => (ω ξ).spin) = ν) (B : Finset Plane)
    (a : Plane) :
    ∫ ω, blockF B (shift a ω) ∂μ = ∑ b ∈ B, ν.real {σ | σ (b - a) = .plus} := by
  subst hS
  haveI : IsProbabilityMeasure (μ.map (fun ω ξ => (ω ξ).spin)) :=
    (Measure.isProbabilityMeasure_map_iff measurable_spinField.aemeasurable).2 inferInstance
  have hm : ∀ ξ, Measurable (fun ω : Config (SiteVal U) => plusInd (ω ξ).spin) := fun ξ =>
    (Measurable.of_discrete (f := fun s : SiteVal U => plusInd s.spin)).comp (measurable_pi_apply ξ)
  have hint : ∀ b ∈ B, Integrable (fun ω : Config (SiteVal U) => plusInd (shift a ω b).spin) μ :=
    fun b _ => Integrable.of_bound (hm (b - a)).aestronglyMeasurable 1
      (ae_of_all _ fun ω => abs_plusInd_le _)
  simp only [blockF]
  rw [integral_finsetSum B hint]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hm' : Measurable (fun σ : Plane → Spin => plusInd (σ (b - a))) :=
    (Measurable.of_discrete (f := plusInd)).comp (measurable_pi_apply (b - a))
  rw [← integral_plusInd_eval, integral_map measurable_spinField.aemeasurable
    hm'.aestronglyMeasurable]
  rfl

/-- Box averages of a difference: if every translate has `∫ f ∘ T_a dμ₁ - ∫ f ∘ T_a dμ₂ ≥ c`,
so does every difference `A_n(μ₁, f) - A_n(μ₂, f)` of box averages. -/
theorem le_boxAvg_sub {S : Type} [MeasurableSpace S] (μ₁ μ₂ : Measure (Config S))
    (f : Config S → ℝ) {c : ℝ}
    (h : ∀ a, c ≤ ∫ ω, f (shift a ω) ∂μ₁ - ∫ ω, f (shift a ω) ∂μ₂) (n : ℕ) :
    c ≤ Gibbs.boxAvg μ₁ f n - Gibbs.boxAvg μ₂ f n := by
  have hpos : (0 : ℝ) < (Gibbs.avgBox n).card := by
    exact_mod_cast (Gibbs.avgBox_nonempty n).card_pos
  rw [Gibbs.boxAvg, Gibbs.boxAvg, ← mul_sub, ← Finset.sum_sub_distrib, le_inv_mul_iff₀ hpos]
  calc ((Gibbs.avgBox n).card : ℝ) * c = ∑ _a ∈ Gibbs.avgBox n, c := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := Finset.sum_le_sum fun a _ => h a

/-! ## Roots of one depth in every block -/

/-- Every window `[-y, -y + 4^{d+1})` contains a coordinate `r_d(m)` of the roots of depth `d`
(`scf:frames`(d): they are spaced `4^{d+1}` apart, `rfree_succ`). -/
theorem exists_rfree_near (A : ℕ → ℤ) (d : ℕ) (y : ℤ) :
    ∃ j : ℕ, j < 4 ^ (d + 1) ∧ ∃ m : ℤ, (j : ℤ) - y = rfree A d m := by
  have hPpos : (0 : ℤ) < 4 ^ (d + 1) := by positivity
  have h0 : 0 ≤ (A d + 4 ^ d + 2 + y) % 4 ^ (d + 1) := Int.emod_nonneg _ hPpos.ne'
  have h1 : (A d + 4 ^ d + 2 + y) % 4 ^ (d + 1) < 4 ^ (d + 1) := Int.emod_lt_of_pos _ hPpos
  refine ⟨((A d + 4 ^ d + 2 + y) % 4 ^ (d + 1)).toNat, ?_,
    -((A d + 4 ^ d + 2 + y) / 4 ^ (d + 1)), ?_⟩
  · have : (((A d + 4 ^ d + 2 + y) % 4 ^ (d + 1)).toNat : ℤ) < ((4 ^ (d + 1) : ℕ) : ℤ) := by
      rw [Int.toNat_of_nonneg h0]
      push_cast
      exact h1
    exact_mod_cast this
  · rw [Int.toNat_of_nonneg h0]
    simp only [rfree, frameLo]
    linear_combination Int.emod_add_mul_ediv (A d + 4 ^ d + 2 + y) (4 ^ (d + 1))

/-- Every translate `[0, 4^{d+1})² - a` of the block `[0, 4^{d+1})²` contains a root `𝐫_d(m₁, m₂)`
of depth `d`. -/
theorem exists_block_root (τ : ℕ → Bool × Bool) (d : ℕ) (a : Plane) :
    ∃ b ∈ Gibbs.avgBox (4 ^ (d + 1) - 1), ∃ m1 m2 : ℤ, b - a = root τ d m1 m2 := by
  obtain ⟨j1, hj1, m1, hm1⟩ := exists_rfree_near (a1 τ) d a.1
  obtain ⟨j2, hj2, m2, hm2⟩ := exists_rfree_near (a2 τ) d a.2
  refine ⟨Gibbs.natSite (j1, j2), ?_, m1, m2, Prod.ext hm1 hm2⟩
  have h4 : 1 ≤ 4 ^ (d + 1) := Nat.one_le_pow _ _ (by norm_num)
  refine Finset.mem_image_of_mem _ (Finset.mem_product.2 ⟨?_, ?_⟩) <;>
    rw [Finset.mem_range] <;> generalize 4 ^ (d + 1) = P at * <;> omega

/-! ## `thm:main`(ii) -/

/-- For a translation-invariant `ν`, `ν(σ_m = s) = ν(σ_0 = s)`. -/
theorem real_eval_of_ti {ν : Measure (Config Spin)} (hν : IsTranslationInvariantMeasure ν)
    (m : Plane) (s : Spin) : ν.real {σ | σ m = s} = ν.real {σ | σ 0 = s} := by
  conv_rhs => rw [← hν (-m)]
  rw [map_measureReal_apply (Gibbs.measurable_shiftConfig (-m)) (measurableSet_eval_eq 0 s)]
  congr 1
  ext σ
  simp [shift]

/-- **`thm:main`, Step 3, on `Γ_τ`**: if `β ∈ J_n` and `d ≥ 1` is a ready depth with `n(d) = n`,
the Ising model on `Γ_τ` has two Gibbs measures `ν₁`, `ν₂`: on the component of depth `d`, the
images of the plus and minus states of `set:peierls` under `m ↦ 𝐫_d(m)` (`squareIso`); on every
other component, the same Gibbs measure. At every site `ν₁(σ_ξ = +) ≥ ν₂(σ_ξ = +)`, and at the
sites of the component of depth `d`, `ν₁(σ_ξ = +) - ν₂(σ_ξ = +) ≥ 2/3 - 1/3` (`e^{J_n(β)} > 3` by
`prf:thermal`(a) and `prf:windows`(d); translation invariance of the plus and minus states). -/
theorem exists_pm_Gamma (h2 : H2) {n : ℕ} (hn : 1 ≤ n) {β : ℝ} (hβ : β ∈ J n)
    (τ : ℕ → Bool × Bool) {d : ℕ} (hd : 1 ≤ d) (hr : MachineM.ready U d)
    (hl : MachineM.label d = n) :
    ∃ ν₁ ν₂ : Measure (Plane → Spin), (Gamma U τ β).toWeightSystem.IsDLR ν₁ ∧
      (Gamma U τ β).toWeightSystem.IsDLR ν₂ ∧
      ∀ ξ, 0 ≤ ν₁.real {σ | σ ξ = .plus} - ν₂.real {σ | σ ξ = .plus} ∧
        (depthOf U τ ξ = some d →
          1 / 3 ≤ ν₁.real {σ | σ ξ = .plus} - ν₂.real {σ | σ ξ = .plus}) := by
  have hJ : 0 ≤ Jc (bc (MachineM.label d) β) := Jc_bc_nonneg _ _
  have h3 : 3 ≤ Real.exp (Jc (bc (MachineM.label d) β)) := by
    have hw := windows_d hn hβ
    refine (thermal_a (MachineM.label d) β ?_).2.2.le
    rw [hl]
    linarith
  obtain ⟨νp, νm, hp, hm, -, -, hTp, hTm, -, -, hpm⟩ := Peierls.peierls_squareLattice h2 hJ
  obtain ⟨hp3, hm3, -⟩ := hpm h3
  haveI := hp.1
  haveI := hm.1
  have hp2 : 2 / 3 ≤ νp.real {σ | σ 0 = .plus} := by
    have e : {σ : Config Spin | σ 0 = .plus} = {σ | σ 0 = .minus}ᶜ := by
      ext σ
      simp only [Set.mem_setOf_eq, Set.mem_compl_iff]
      generalize σ 0 = x
      cases x <;> simp
    rw [e, probReal_compl_eq_one_sub (measurableSet_eval_eq 0 .minus)]
    linarith
  let φ := squareIso U τ β hd hr hJ
  have hφm : Measurable (fun σ : Plane → Spin => σ ∘ φ.e.symm) :=
    Measurable.of_eval fun w => measurable_pi_apply _
  have hex := fun i => Gibbs.IsingGraph.exists_isDLR ((Gamma U τ β).restrict (depthOf U τ) i)
  let ρ : ∀ i, Measure ({v // depthOf U τ v = i} → Spin) := fun i => Classical.choose (hex i)
  have hρ : ∀ i, ((Gamma U τ β).restrict (depthOf U τ) i).toWeightSystem.IsDLR (ρ i) :=
    fun i => Classical.choose_spec (hex i)
  let ρ₁ := Function.update ρ (some d) (νp.map fun σ => σ ∘ φ.e.symm)
  let ρ₂ := Function.update ρ (some d) (νm.map fun σ => σ ∘ φ.e.symm)
  have hρ₁ : ∀ i, ((Gamma U τ β).restrict (depthOf U τ) i).toWeightSystem.IsDLR (ρ₁ i) := by
    intro i
    by_cases h : i = some d
    · subst h
      simp only [ρ₁, Function.update_self]
      exact φ.isDLR_map hp
    · simp only [ρ₁, Function.update_of_ne h]
      exact hρ i
  have hρ₂ : ∀ i, ((Gamma U τ β).restrict (depthOf U τ) i).toWeightSystem.IsDLR (ρ₂ i) := by
    intro i
    by_cases h : i = some d
    · subst h
      simp only [ρ₂, Function.update_self]
      exact φ.isDLR_map hm
    · simp only [ρ₂, Function.update_of_ne h]
      exact hρ i
  haveI : ∀ i, IsProbabilityMeasure (ρ₁ i) := fun i => (hρ₁ i).1
  haveI : ∀ i, IsProbabilityMeasure (ρ₂ i) := fun i => (hρ₂ i).1
  refine ⟨glueMeas (depthOf U τ) ρ₁, glueMeas (depthOf U τ) ρ₂,
    isDLR_glueMeas _ _ (isComponentMap_depthOf β) ρ₁ hρ₁,
    isDLR_glueMeas _ _ (isComponentMap_depthOf β) ρ₂ hρ₂, fun ξ => ?_⟩
  by_cases h : depthOf U τ ξ = some d
  · have key : ∀ ν : Measure (Config Spin), IsTranslationInvariantMeasure ν →
        (ν.map fun σ => σ ∘ φ.e.symm).real {σ' | σ' ⟨ξ, h⟩ = .plus} =
          ν.real {σ | σ 0 = .plus} := fun ν hν => by
      rw [map_measureReal_apply hφm (measurableSet_eval_eq _ _),
        ← real_eval_of_ti hν (φ.e.symm ⟨ξ, h⟩)]
      rfl
    rw [glueMeas_real_eval _ ρ₁ ξ h, glueMeas_real_eval _ ρ₂ ξ h]
    simp only [ρ₁, ρ₂, Function.update_self]
    rw [key νp hTp, key νm hTm]
    constructor
    · linarith
    · intro _
      linarith
  · rw [glueMeas_real_eval _ ρ₁ ξ rfl, glueMeas_real_eval _ ρ₂ ξ rfl]
    simp only [ρ₁, ρ₂, Function.update_of_ne h, sub_self]
    exact ⟨le_rfl, fun h' => absurd h' h⟩

/-- **`thm:main`(ii)** (Steps 1 and 3, by averaging), from `H2`, `pay:effective` (`hEff`) and
"the spin marginal of `L τ ν` is `ν`" (`hS`, `pay:elim`): if `U` halts on `n` and `β ∈ J_n`,
`βΦ` has at least two translation-invariant Gibbs measures. -/
theorem thm_main_ii_of (h2 : H2)
    (L : (ℕ → Bool × Bool) → Measure (Plane → Spin) → Measure (Config (SiteVal U))) {β : ℝ}
    (hEff : ∀ τ, Typical τ → ∀ μ' : Measure (Config (SiteVal U)),
      (IsGibbs β (Phi U) μ' ∧ ∀ᵐ ω ∂μ', bgOf ω = bgMap U τ) ↔
        ∃ ν : Measure (Plane → Spin), (Gamma U τ β).toWeightSystem.IsDLR ν ∧ μ' = L τ ν)
    (hS : ∀ τ, Typical τ → ∀ ν : Measure (Plane → Spin), (Gamma U τ β).toWeightSystem.IsDLR ν →
      (L τ ν).map (fun ω ξ => (ω ξ).spin) = ν)
    {n : ℕ} (hn : 1 ≤ n) (hβ : β ∈ J n) (hh : U.HaltsOn n) :
    ∃ μ₁ μ₂ : Measure (Config (SiteVal U)),
      μ₁ ≠ μ₂ ∧ IsTIGibbs U β μ₁ ∧ IsTIGibbs U β μ₂ := by
  obtain ⟨τ, hτ⟩ := exists_typical_phase
  obtain ⟨d, hd, hr, hl⟩ := (MachineM.readyDepths_infinite hn hh).nonempty
  obtain ⟨ν₁, ν₂, hν₁, hν₂, hD⟩ := exists_pm_Gamma h2 hn hβ τ hd hr hl
  have hG₁ := ((hEff τ hτ (L τ ν₁)).2 ⟨ν₁, hν₁, rfl⟩).1
  have hG₂ := ((hEff τ hτ (L τ ν₂)).2 ⟨ν₂, hν₂, rfl⟩).1
  haveI := hG₁.1
  haveI := hG₂.1
  have hdiff : ∀ a, 1 / 3 ≤
      ∫ ω, blockF (Gibbs.avgBox (4 ^ (d + 1) - 1)) (shift a ω) ∂(L τ ν₁) -
        ∫ ω, blockF (Gibbs.avgBox (4 ^ (d + 1) - 1)) (shift a ω) ∂(L τ ν₂) := by
    intro a
    rw [integral_blockF_shift (hS τ hτ ν₁ hν₁), integral_blockF_shift (hS τ hτ ν₂ hν₂),
      ← Finset.sum_sub_distrib]
    obtain ⟨b, hb, m1, m2, hbm⟩ := exists_block_root τ d a
    have hdb : depthOf U τ (b - a) = some d := by rw [hbm]; exact depthOf_root hd hr m1 m2
    exact ((hD (b - a)).2 hdb).trans (Finset.single_le_sum
      (f := fun b => ν₁.real {σ | σ (b - a) = .plus} - ν₂.real {σ | σ (b - a) = .plus})
      (fun b _ => (hD (b - a)).1) hb)
  obtain ⟨μb₁, μb₂, hG1, hT1, hG2, hT2, hC⟩ := Gibbs.exists_ti_gibbs_avg₂ phi_isInteraction
    phi_nearestNeighbour phi_translationInvariant hG₁ hG₂ (Gibbs.avgBox (4 ^ (d + 1) - 1))
    (blockF_local _) (blockF_local _)
  have hmem := hC {p : ℝ × ℝ | 1 / 3 ≤ p.1 - p.2}
    (isClosed_le continuous_const (continuous_fst.sub continuous_snd))
    (Eventually.of_forall fun n => le_boxAvg_sub _ _ _ hdiff n)
  refine ⟨μb₁, μb₂, fun h => ?_, ⟨hG1, hT1⟩, ⟨hG2, hT2⟩⟩
  subst h
  simp only [Set.mem_setOf_eq, sub_self] at hmem
  norm_num at hmem

end UPD.BG

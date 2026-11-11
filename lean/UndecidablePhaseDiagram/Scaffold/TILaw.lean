/-
# Sections 3.3–3.4: the translation-invariant laws of `𝔸` and `𝔸^q`
# (`prop:scaffold-ti`(b), `prop:quarter-ti`(a) second claim)

New in this project.

* The configuration spaces `𝔸^{ℤ²}` and `(𝔸^q)^{ℤ²}` carry the product σ-algebras of the discrete
  ones (letters and quarters are finite sets). A *translation-invariant law* of a Wang set with
  tilings `X` is a probability measure `μ` on the configurations with `μ(X) = 1` and
  `μ ∘ T_a⁻¹ = μ` for all `a` (`IsTILaw`; the same reading as `IsGibbs` and
  `IsTranslationInvariantMeasure` in `Statements.lean`).
* The printed proof of `prop:scaffold-ti`(b), written once for an abstract *phase system*
  (`PhaseSystem`): tilings `T` closed under translations, a measurable phase map `φ` with
  `φ(T_a f) = φ(f) + a`, and a measurable map `Ψ` with `Ψ(φ(f)) = f` and `φ(Ψ(υ)) = υ` for a
  Haar-almost sure set of good phases. Then (`PhaseSystem.law_phase`) under every
  translation-invariant law the phase is Haar distributed ("the law of `ϖ mod 2^l` is invariant
  under all translations of `(ℤ/2^lℤ)²`, hence uniform"); `f = Ψ(φ(f))` almost surely; so every
  translation-invariant law is the image of Haar measure under `Ψ` (`PhaseSystem.law_unique`).
  **[choice] (proof side)** Existence is proved directly: the image of Haar measure is
  translation invariant, since Haar measure is invariant under `ϖ ↦ ϖ + a` and
  `T_a(Ψ(υ)) = Ψ(υ + a)` (`PhaseSystem.isTILaw`), instead of by averaging translates of a point
  mass over growing boxes and taking a limit point. The printed statement is the same.
* `𝔸`: `phaseOf` (the phase `ϖ(f)` of a tiling, measurable by `scf:phase`(b)), `tilingOf`
  (`ϖ ↦ f_ϖ`: `f_ϖ(x)` is `𝔲` with the children `ς_{m-1}(x), …, ς_0(x)` taken in turn, `m` the
  first position of two consecutive digits `(1,1)` of `x - ϖ`; measurable, "since `f_ϖ(x)` is
  computed from finitely many digits of `x - ϖ`"); **`prop:scaffold-ti`(b)** `scaffold_ti_b`.
* `𝔸^q`: `qphaseOf`, `qtilingOf` (`τ ↦ Y_τ`); **`prop:quarter-ti`(a)**, second claim,
  `quarter_ti_law`; and the law of the quarter phase is Haar (`quarter_phase_haar`).
-/
import UndecidablePhaseDiagram.Scaffold.Haar

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter
open scoped ENNReal

namespace UPD.Scaffold

/-! ## Letters and quarters are discrete measurable spaces -/

instance : MeasurableSpace Letter := ⊤

instance : DiscreteMeasurableSpace Letter := ⟨fun _ => MeasurableSpace.measurableSet_top⟩

instance : MeasurableSpace Quarter := ⊤

instance : DiscreteMeasurableSpace Quarter := ⟨fun _ => MeasurableSpace.measurableSet_top⟩

section Abstract

variable {S : Type} [Fintype S] [MeasurableSpace S] [DiscreteMeasurableSpace S]

omit [Fintype S] [DiscreteMeasurableSpace S] in
theorem measurable_shift (a : Plane) : Measurable (shift a : (Plane → S) → (Plane → S)) :=
  Measurable.of_eval fun ξ => measurable_pi_apply (ξ - a)

/-- The set of tilings of a Wang set (legal on `ℤ²`) is measurable. -/
theorem measurableSet_legalOn_univ (H V : S → S → Prop) :
    MeasurableSet {f : Plane → S | LegalOn H V Set.univ f} := by
  classical
  have hH : ∀ u : Plane, MeasurableSet {f : Plane → S | H (f u) (f (u + (1, 0)))} := fun u =>
    Gibbs.measurableSet_of_dependsOn {u, u + (1, 0)} _ fun ω ω' h => by
      simp only [Set.mem_setOf_eq]
      rw [h u (by simp), h (u + (1, 0)) (by simp)]
  have hV : ∀ u : Plane, MeasurableSet {f : Plane → S | V (f u) (f (u + (0, 1)))} := fun u =>
    Gibbs.measurableSet_of_dependsOn {u, u + (0, 1)} _ fun ω ω' h => by
      simp only [Set.mem_setOf_eq]
      rw [h u (by simp), h (u + (0, 1)) (by simp)]
  have e : {f : Plane → S | LegalOn H V Set.univ f} =
      (⋂ u, {f : Plane → S | H (f u) (f (u + (1, 0)))}) ∩
        ⋂ u, {f : Plane → S | V (f u) (f (u + (0, 1)))} := by
    ext f; simp [LegalOn]
  rw [e]
  exact (MeasurableSet.iInter hH).inter (MeasurableSet.iInter hV)

/-- A *translation-invariant law* of a set `X` of configurations (the tilings of a Wang set): a
probability measure `μ` with `μ(X) = 1` and `T_a μ = μ` for every `a ∈ ℤ²`. -/
def IsTILaw (X : Set (Plane → S)) (μ : Measure (Plane → S)) : Prop :=
  IsProbabilityMeasure μ ∧ μ X = 1 ∧ ∀ a : Plane, μ.map (shift a) = μ

/-- A *phase system*: tilings `T` closed under translations, a phase map `φ` with
`φ(T_a f) = φ(f) + a` (in the form of P-7), a set `G` of good phases of full Haar measure, and a
map `Ψ` such that `Ψ(υ)` is the tiling with phase `υ` for good `υ` and `Ψ(φ(f)) = f` for a tiling
with good phase. -/
structure PhaseSystem (S : Type) [MeasurableSpace S] where
  /-- the tilings -/
  T : Set (Plane → S)
  /-- the phase of a tiling -/
  φ : (Plane → S) → ℕ → Bool × Bool
  /-- the tiling of a good phase -/
  Ψ : (ℕ → Bool × Bool) → Plane → S
  /-- the good phases -/
  G : Set (ℕ → Bool × Bool)
  measurableSet_T : MeasurableSet T
  shift_mem : ∀ (a : Plane), ∀ f ∈ T, shift a f ∈ T
  measurable_φ : Measurable φ
  measurable_Ψ : Measurable Ψ
  phase_shift : ∀ f ∈ T, ∀ (a : Plane) (l : ℕ),
    (2 : ℤ) ^ l ∣ wsum (col (φ (shift a f))) l - wsum (col (φ f)) l - a.1 ∧
      (2 : ℤ) ^ l ∣ wsum (row (φ (shift a f))) l - wsum (row (φ f)) l - a.2
  ae_good : ∀ᵐ υ ∂haar, υ ∈ G
  Ψ_mem : ∀ υ ∈ G, Ψ υ ∈ T ∧ φ (Ψ υ) = υ
  Ψ_φ : ∀ f ∈ T, φ f ∈ G → Ψ (φ f) = f

/-- Truncations in `[0, 2^n)` that are congruent modulo `2^n` are equal. -/
theorem wsum_eq_of_dvd {c c' : ℕ → Bool} {n : ℕ} (h : (2 : ℤ) ^ n ∣ wsum c n - wsum c' n) :
    wsum c n = wsum c' n := by
  have h0 := wsum_nonneg c n; have h1 := wsum_lt c n
  have h2 := wsum_nonneg c' n; have h3 := wsum_lt c' n
  have := Int.eq_zero_of_abs_lt_dvd h (by rw [abs_lt]; constructor <;> linarith)
  linarith

/-- Equal truncations at `n` give equal digits below `n`. -/
theorem prefix_eq_of_wsum_eq {c c' : ℕ → Bool} {n : ℕ} (h : wsum c n = wsum c' n) :
    ∀ m < n, c m = c' m := by
  intro m hm
  have e : ∀ k ≤ n, wsum c k = wsum c' k := fun k hk => by
    rw [← wsum_emod c hk, ← wsum_emod c' hk, h]
  have h1 := wsum_succ_top c m
  have h2 := wsum_succ_top c' m
  rw [e (m + 1) hm, e m hm.le] at h1
  have hp : (0 : ℤ) < 2 ^ m := by positivity
  have h3 : (2 : ℤ) ^ m * bitZ (c m) = 2 ^ m * bitZ (c' m) := by linarith
  exact bitZ_injective (mul_left_cancel₀ hp.ne' h3)

/-- `υ ∈ cyl n q` iff the truncations of `υ` and `q` at `n` agree, coordinatewise. -/
theorem mem_cyl_iff_wsum (υ q : ℕ → Bool × Bool) (n : ℕ) :
    υ ∈ cyl n q ↔ wsum (col υ) n = wsum (col q) n ∧ wsum (row υ) n = wsum (row q) n := by
  constructor
  · intro h
    exact ⟨wsum_congr fun m hm => by simp [col, h m hm],
      wsum_congr fun m hm => by simp [row, h m hm]⟩
  · rintro ⟨h1, h2⟩ m hm
    exact Prod.ext (prefix_eq_of_wsum_eq h1 m hm) (prefix_eq_of_wsum_eq h2 m hm)

/-- Two digit sequences congruent to `υ + a` modulo every `2^l` are equal. -/
theorem eq_of_shift_congr {υ υ' υ'' : ℕ → Bool × Bool} {a : Plane}
    (h' : ∀ l, (2 : ℤ) ^ l ∣ wsum (col υ') l - wsum (col υ) l - a.1 ∧
      (2 : ℤ) ^ l ∣ wsum (row υ') l - wsum (row υ) l - a.2)
    (h'' : ∀ l, (2 : ℤ) ^ l ∣ wsum (col υ'') l - wsum (col υ) l - a.1 ∧
      (2 : ℤ) ^ l ∣ wsum (row υ'') l - wsum (row υ) l - a.2) : υ' = υ'' := by
  have hc : col υ' = col υ'' := eq_of_wsum_eq fun l => wsum_eq_of_dvd (by
    have := dvd_sub (h' l).1 (h'' l).1
    convert this using 1; ring)
  have hr : row υ' = row υ'' := eq_of_wsum_eq fun l => wsum_eq_of_dvd (by
    have := dvd_sub (h' l).2 (h'' l).2
    convert this using 1; ring)
  funext m
  exact Prod.ext (congrFun hc m) (congrFun hr m)

namespace PhaseSystem

variable (P : PhaseSystem S)

omit [Fintype S] [DiscreteMeasurableSpace S] in
/-- `T_a(Ψ(υ)) = Ψ(υ + a)` for good `υ` and `υ + a`. -/
theorem shift_Ψ {υ : ℕ → Bool × Bool} (h1 : υ ∈ P.G) (a : Plane) (h2 : addDig a υ ∈ P.G) :
    shift a (P.Ψ υ) = P.Ψ (addDig a υ) := by
  have hT := P.shift_mem a _ (P.Ψ_mem υ h1).1
  have hφ : P.φ (shift a (P.Ψ υ)) = addDig a υ := by
    refine eq_of_shift_congr (υ := υ) (a := a) (fun l => ?_) (wsum_addDig a υ)
    have := P.phase_shift _ (P.Ψ_mem υ h1).1 a l
    rwa [(P.Ψ_mem υ h1).2] at this
  rw [← hφ, P.Ψ_φ _ hT (hφ ▸ h2)]

omit [Fintype S] [DiscreteMeasurableSpace S] in
/-- Existence: the image of Haar measure under `Ψ` is a translation-invariant law of `T`. -/
theorem isTILaw : IsTILaw P.T (haar.map P.Ψ) := by
  refine ⟨(Measure.isProbabilityMeasure_map_iff P.measurable_Ψ.aemeasurable).2 inferInstance, ?_, fun a => ?_⟩
  · rw [Measure.map_apply P.measurable_Ψ P.measurableSet_T,
      ← prob_compl_eq_zero_iff (P.measurable_Ψ P.measurableSet_T)]
    exact ae_iff.1 (P.ae_good.mono fun υ hυ => (P.Ψ_mem υ hυ).1)
  · rw [Measure.map_map (measurable_shift a) P.measurable_Ψ]
    have h2 : ∀ᵐ υ ∂haar, addDig a υ ∈ P.G := by
      have h := P.ae_good
      rw [← haar_map_addDig a] at h
      exact ae_of_ae_map (measurable_addDig a).aemeasurable h
    have hae : (shift a ∘ P.Ψ) =ᵐ[haar] (P.Ψ ∘ addDig a) := by
      filter_upwards [P.ae_good, h2] with υ h1 h2
      exact P.shift_Ψ h1 a h2
    rw [Measure.map_congr hae, ← Measure.map_map P.measurable_Ψ (measurable_addDig a),
      haar_map_addDig]

omit [Fintype S] [DiscreteMeasurableSpace S] in
/-- Proof of `prop:scaffold-ti`(b): under a translation-invariant law, all prefix cylinders of
the phase of the same length have the same mass (`scf:phase`(a)). -/
theorem cyl_const {μ : Measure (Plane → S)} (hμ : IsTILaw P.T μ) (n : ℕ)
    (p q : ℕ → Bool × Bool) : μ.map P.φ (cyl n p) = μ.map P.φ (cyl n q) := by
  obtain ⟨_, hT, hTI⟩ := hμ
  rw [Measure.map_apply P.measurable_φ (measurableSet_cyl n p),
    Measure.map_apply P.measurable_φ (measurableSet_cyl n q)]
  let a : Plane := (wsum (col q) n - wsum (col p) n, wsum (row q) n - wsum (row p) n)
  have key : ∀ f ∈ P.T, P.φ f ∈ cyl n p ↔ P.φ (shift a f) ∈ cyl n q := by
    intro f hf
    rw [mem_cyl_iff_wsum, mem_cyl_iff_wsum]
    obtain ⟨d1, d2⟩ := P.phase_shift f hf a n
    constructor
    · rintro ⟨h1, h2⟩
      rw [h1] at d1; rw [h2] at d2
      exact ⟨wsum_eq_of_dvd (by convert d1 using 1; simp only [a]; ring),
        wsum_eq_of_dvd (by convert d2 using 1; simp only [a]; ring)⟩
    · rintro ⟨h1, h2⟩
      rw [h1] at d1; rw [h2] at d2
      exact ⟨wsum_eq_of_dvd (by
          have := dvd_neg.2 d1
          convert this using 1; simp only [a]; ring),
        wsum_eq_of_dvd (by
          have := dvd_neg.2 d2
          convert this using 1; simp only [a]; ring)⟩
  have hset : P.φ ⁻¹' cyl n p ∩ P.T = shift a ⁻¹' (P.φ ⁻¹' cyl n q) ∩ P.T := by
    ext f
    simp only [Set.mem_inter_iff, Set.mem_preimage]
    constructor
    · rintro ⟨hp, hf⟩; exact ⟨(key f hf).1 hp, hf⟩
    · rintro ⟨hq, hf⟩; exact ⟨(key f hf).2 hq, hf⟩
  have hTc : μ P.Tᶜ = 0 := by rw [prob_compl_eq_zero_iff P.measurableSet_T]; exact hT
  rw [← measure_inter_conull hTc (s := P.φ ⁻¹' cyl n p), hset, measure_inter_conull hTc,
    ← Measure.map_apply (measurable_shift a) (P.measurable_φ (measurableSet_cyl n q)), hTI a]

omit [Fintype S] [DiscreteMeasurableSpace S] in
/-- Proof of `prop:scaffold-ti`(b): under every translation-invariant law the phase is Haar
distributed. -/
theorem law_phase {μ : Measure (Plane → S)} (hμ : IsTILaw P.T μ) : μ.map P.φ = haar := by
  haveI := hμ.1
  haveI := (Measure.isProbabilityMeasure_map_iff (μ := μ) P.measurable_φ.aemeasurable).2 inferInstance
  rw [haar_def]
  exact eq_unifSeq fun n q => cyl_eq_of_const _ n _ fun p => P.cyl_const hμ n p q

omit [Fintype S] [DiscreteMeasurableSpace S] in
/-- Proof of `prop:scaffold-ti`(b): every translation-invariant law is the image of Haar measure
under `Ψ` (`f = Ψ(φ(f))` almost surely). -/
theorem law_unique {μ : Measure (Plane → S)} (hμ : IsTILaw P.T μ) : μ = haar.map P.Ψ := by
  have hφ := P.law_phase hμ
  have hG : ∀ᵐ f ∂μ, P.φ f ∈ P.G := by
    have h := P.ae_good
    rw [← hφ] at h
    exact ae_of_ae_map P.measurable_φ.aemeasurable h
  have hTae : ∀ᵐ f ∂μ, f ∈ P.T := by
    haveI := hμ.1
    rw [ae_iff]
    exact (prob_compl_eq_zero_iff P.measurableSet_T).2 hμ.2.1
  have hae : (P.Ψ ∘ P.φ) =ᵐ[μ] id := by
    filter_upwards [hG, hTae] with f h1 h2
    exact P.Ψ_φ f h2 h1
  calc μ = μ.map id := Measure.map_id.symm
    _ = μ.map (P.Ψ ∘ P.φ) := Measure.map_congr hae.symm
    _ = (μ.map P.φ).map P.Ψ := (Measure.map_map P.measurable_Ψ P.measurable_φ).symm
    _ = haar.map P.Ψ := by rw [hφ]

omit [Fintype S] [DiscreteMeasurableSpace S] in
/-- There is exactly one translation-invariant law, the image of Haar measure under `Ψ`. -/
theorem existsUnique_isTILaw : ∃! μ : Measure (Plane → S), IsTILaw P.T μ :=
  ⟨haar.map P.Ψ, P.isTILaw, fun _ hμ => P.law_unique hμ⟩

end PhaseSystem

end Abstract

/-! ## The scaffold `𝔸`: `prop:scaffold-ti`(b) -/

/-- The box `[-r, r]²`. -/
def boxF (r : ℕ) : Finset Plane := Finset.Icc (-(r : ℤ)) r ×ˢ Finset.Icc (-(r : ℤ)) r

theorem mem_boxF {r : ℕ} {x : Plane} (h1 : |x.1| ≤ r) (h2 : |x.2| ≤ r) : x ∈ boxF r := by
  rw [abs_le] at h1 h2
  simp only [boxF, Finset.mem_product, Finset.mem_Icc]
  exact ⟨h1, h2⟩

theorem measurableSet_letterTilings : MeasurableSet {f : Plane → Letter | IsLetterTiling f} := by
  classical
  have hA : ∀ u : Plane, MeasurableSet {f : Plane → Letter | (f u).InA} := fun u =>
    Gibbs.measurableSet_of_dependsOn {u} _ fun ω ω' h => by
      simp only [Set.mem_setOf_eq]; rw [h u (by simp)]
  have e : {f : Plane → Letter | IsLetterTiling f} =
      (⋂ u, {f : Plane → Letter | (f u).InA}) ∩
        {f | LegalOn Letter.MatchE Letter.MatchN Set.univ f} := by
    ext f; simp [IsLetterTiling]
  rw [e]
  exact (MeasurableSet.iInter hA).inter (measurableSet_legalOn_univ _ _)

open Classical in
/-- The phase `ϖ(f)` of a tiling `f` of `𝔸` (the digits of its tower); `0` if `f` is not a
tiling. -/
def phaseOf (f : Plane → Letter) : ℕ → Bool × Bool :=
  if h : IsLetterTiling f then Classical.choose (exists_tower_of_tiling h) else fun _ => (false, false)

theorem phaseOf_spec {f : Plane → Letter} (hf : IsLetterTiling f) : IsPhase f (phaseOf f) := by
  rw [phaseOf, dif_pos hf]
  exact Classical.choose_spec (exists_tower_of_tiling hf)

/-- The phase map is measurable: each digit of `ϖ(f)` is read off a finite box (`scf:phase`(b)). -/
theorem measurable_phaseOf : Measurable phaseOf := by
  classical
  refine Measurable.of_eval fun m => ?_
  let D := boxF (rho (m + 1))
  let g : (Plane → Letter) → Bool × Bool := fun f =>
    if h : ∃ f', IsLetterTiling f' ∧ ∀ x ∈ D, f' x = f x then phaseOf (Classical.choose h) m
    else (false, false)
  have hg : ∀ f f', IsLetterTiling f' → (∀ x ∈ D, f' x = f x) → g f = phaseOf f' m := by
    intro f f' hf' hag
    have h : ∃ f', IsLetterTiling f' ∧ ∀ x ∈ D, f' x = f x := ⟨f', hf', hag⟩
    simp only [g, dif_pos h]
    obtain ⟨hc, hcag⟩ := Classical.choose_spec h
    exact phase_local (phaseOf_spec hc) (phaseOf_spec hf') (m + 1)
      (fun x hx1 hx2 => by rw [hcag x (mem_boxF hx1 hx2), hag x (mem_boxF hx1 hx2)]) m
      (by omega)
  have hgm : Measurable g := Gibbs.measurable_of_dependsOn D g fun f f'' hff => by
    by_cases h : ∃ f', IsLetterTiling f' ∧ ∀ x ∈ D, f' x = f x
    · obtain ⟨f', hf', hag⟩ := h
      rw [hg f f' hf' hag, hg f'' f' hf' fun x hx => (hag x hx).trans (hff x hx)]
    · have h'' : ¬ ∃ f', IsLetterTiling f' ∧ ∀ x ∈ D, f' x = f'' x :=
        fun ⟨f', hf', hag⟩ => h ⟨f', hf', fun x hx => (hag x hx).trans (hff x hx).symm⟩
      simp only [g, dif_neg h, dif_neg h'']
  have e : (fun f => phaseOf f m) = fun f => if IsLetterTiling f then g f else (false, false) := by
    funext f
    by_cases hf : IsLetterTiling f
    · rw [if_pos hf, hg f f hf fun _ _ => rfl]
    · simp only [phaseOf, dif_neg hf, if_neg hf]
  rw [e]
  exact Measurable.ite measurableSet_letterTilings hgm measurable_const

/-- `ς_m(x) = ς_{m+1}(x) = (1, 1)` (`scf:coincidence`). -/
def IsDouble (υ : ℕ → Bool × Bool) (x : Plane) (m : ℕ) : Prop :=
  digP υ x m = (true, true) ∧ digP υ x (m + 1) = (true, true)

instance (υ : ℕ → Bool × Bool) (x : Plane) : DecidablePred (IsDouble υ x) := fun m => by
  unfold IsDouble; infer_instance

open Classical in
/-- `ϖ ↦ f_ϖ` (`prop:scaffold-ti`(a), (b)): `f_ϖ(x)` is `𝔲` with the children
`ς_{m-1}(x), …, ς_0(x)` taken in turn, where `m` is the first position of two consecutive digits
`(1,1)` of `x - ϖ` (`scf:coincidence`); `𝔲` if there is none (never, for a resolving `ϖ`). -/
def tilingOf (υ : ℕ → Bool × Bool) (x : Plane) : Letter :=
  if h : ∃ m, IsDouble υ x m then descend (digP υ x) (Nat.find h) uLetter else uLetter

/-- For a resolving phase, `f_ϖ` is the tiling with phase `ϖ`. -/
theorem tilingOf_eq {υ : ℕ → Bool × Bool} (hυ : Resolving υ) {f : Plane → Letter}
    (hφ : IsPhase f υ) : tilingOf υ = f := by
  funext x
  obtain ⟨F, hF, rfl⟩ := hφ
  have h : ∃ m, IsDouble υ x m := hυ x
  rw [tilingOf, dif_pos h]
  exact ((coincidence hF x (Nat.find_spec h).1 (Nat.find_spec h).2).2).symm

theorem tilingOf_spec {υ : ℕ → Bool × Bool} (hυ : Resolving υ) :
    IsLetterTiling (tilingOf υ) ∧ IsPhase (tilingOf υ) υ := by
  obtain ⟨f, hf, hφ⟩ := exists_phase υ
  rw [tilingOf_eq hυ hφ]
  exact ⟨hf, hφ⟩

theorem descend_congr {s s' : ℕ → Bool × Bool} {n : ℕ} (h : ∀ i < n, s i = s' i) (P : Letter) :
    descend s n P = descend s' n P := by
  induction n generalizing P with
  | zero => rfl
  | succ n ih =>
    simp only [descend]
    rw [h n (by omega)]
    exact ih (fun i hi => h i (by omega)) _

/-- `ϖ ↦ f_ϖ` is measurable: "`f_ϖ(x)` is computed from finitely many digits of `x - ϖ`". -/
theorem measurable_tilingOf : Measurable tilingOf := by
  classical
  refine Measurable.of_eval fun x => ?_
  let p : ℕ → (ℕ → Bool × Bool) → Prop := fun n υ => IsDouble υ x n ∨ ¬ ∃ m, IsDouble υ x m
  have hp : ∀ υ, ∃ n, p n υ := fun υ => by
    by_cases h : ∃ m, IsDouble υ x m
    · obtain ⟨m, hm⟩ := h; exact ⟨m, Or.inl hm⟩
    · exact ⟨0, Or.inr h⟩
  let F : ℕ → (ℕ → Bool × Bool) → Letter := fun n υ =>
    if IsDouble υ x n then descend (digP υ x) n uLetter else uLetter
  have hD : ∀ n, MeasurableSet {υ : ℕ → Bool × Bool | IsDouble υ x n} := fun n =>
    measurableSet_setOf.2 (measurable_of_prefix (n + 2) _ fun υ υ' h => by
      simp only [IsDouble]
      rw [digP_congr (fun i hi => h i (by omega)) x,
        digP_congr (m := n + 1) (fun i hi => h i (by omega)) x])
  have hF : ∀ n, Measurable (F n) := fun n =>
    measurable_of_prefix (n + 2) _ fun υ υ' h => by
      have hd : ∀ i ≤ n + 1, digP υ x i = digP υ' x i :=
        fun i hi => digP_congr (fun j hj => h j (by omega)) x
      have e1 : IsDouble υ x n ↔ IsDouble υ' x n := by
        simp only [IsDouble, hd n (by omega), hd (n + 1) le_rfl]
      simp only [F]
      by_cases hc : IsDouble υ' x n
      · rw [if_pos hc, if_pos (e1.2 hc), descend_congr (fun i hi => hd i (by omega))]
      · rw [if_neg hc, if_neg (fun h => hc (e1.1 h))]
  have hpm : ∀ n, MeasurableSet {υ | p n υ} := fun n => by
    have e : {υ | p n υ} = {υ | IsDouble υ x n} ∪ (⋃ m, {υ | IsDouble υ x m})ᶜ := by
      ext υ; simp [p]
    rw [e]
    exact (hD n).union (MeasurableSet.iUnion hD).compl
  have e : (fun υ => tilingOf υ x) = fun υ => F (Nat.find (hp υ)) υ := by
    funext υ
    by_cases h : ∃ m, IsDouble υ x m
    · have hfind : Nat.find (hp υ) = Nat.find h :=
        Nat.find_congr' fun {n} => by simp only [p, h, not_true_eq_false, or_false]
      rw [tilingOf, dif_pos h, hfind]
      simp only [F, if_pos (Nat.find_spec h)]
    · rw [tilingOf, dif_neg h]
      simp only [F]
      rw [if_neg fun hd => h ⟨_, hd⟩]
  rw [e]
  exact Measurable.find hF hpm hp

/-- The phase system of `𝔸`: tilings, phases, `ϖ ↦ f_ϖ`, resolving phases. -/
def scaffoldSystem : PhaseSystem Letter where
  T := {f | IsLetterTiling f}
  φ := phaseOf
  Ψ := tilingOf
  G := {υ | Resolving υ}
  measurableSet_T := measurableSet_letterTilings
  shift_mem := fun a _ hf => IsLetterTiling.shift hf a
  measurable_φ := measurable_phaseOf
  measurable_Ψ := measurable_tilingOf
  phase_shift := fun _ hf a l =>
    phase_shift hf (phaseOf_spec hf) a (phaseOf_spec (IsLetterTiling.shift hf a)) l
  ae_good := ae_resolving
  Ψ_mem := fun _ hυ => ⟨(tilingOf_spec hυ).1,
    (phaseOf_spec (tilingOf_spec hυ).1).unique (tilingOf_spec hυ).2⟩
  Ψ_φ := fun _ hf hυ => tilingOf_eq hυ (phaseOf_spec hf)

/-- **`prop:scaffold-ti`(b)**: `X_𝔸` carries exactly one translation-invariant probability
measure, the image of Haar measure on `ℤ₂²` under `ϖ ↦ f_ϖ`. -/
theorem scaffold_ti_b :
    IsTILaw {f : Plane → Letter | IsLetterTiling f} (haar.map tilingOf) ∧
      ∀ μ : Measure (Plane → Letter), IsTILaw {f | IsLetterTiling f} μ → μ = haar.map tilingOf :=
  ⟨scaffoldSystem.isTILaw, fun _ hμ => scaffoldSystem.law_unique hμ⟩

/-- `prop:scaffold-ti`(b), as "exactly one". -/
theorem scaffold_ti_existsUnique :
    ∃! μ : Measure (Plane → Letter), IsTILaw {f | IsLetterTiling f} μ :=
  scaffoldSystem.existsUnique_isTILaw

/-- Section 3 (introduction, and the proof of `prop:scaffold-ti`(b)): under every
translation-invariant law of `𝔸` the phase is Haar distributed. -/
theorem scaffold_phase_haar {μ : Measure (Plane → Letter)}
    (hμ : IsTILaw {f | IsLetterTiling f} μ) : μ.map phaseOf = haar :=
  scaffoldSystem.law_phase hμ

/-! ## The quarters `𝔸^q`: `prop:quarter-ti`(a), second claim -/

theorem inA_descend (s : ℕ → Bool × Bool) (n : ℕ) {P : Letter} (hP : P.InA) :
    (descend s n P).InA := by
  induction n generalizing P with
  | zero => exact hP
  | succ n ih => exact ih (hP.child _ _)

theorem inA_uLetter : uLetter.InA := by decide

theorem inA_tilingOf (υ : ℕ → Bool × Bool) (x : Plane) : (tilingOf υ x).InA := by
  unfold tilingOf
  split
  · exact inA_descend _ _ inA_uLetter
  · exact inA_uLetter

/-- `f_ϖ` with values in `𝔸`. -/
def tilingOfA (υ : ℕ → Bool × Bool) (x : Plane) : LetterA := ⟨tilingOf υ x, inA_tilingOf υ x⟩

/-- `τ ↦ Y_τ` (`prop:quarter-ti`(a)): `Y_τ(ξ) = f_ϖ^q(ξ - ε)`, `ε ≡ τ (mod 2)`,
`ϖ = (τ - ε)/2` (the digits of `τ` after the first). -/
def qtilingOf (τ : ℕ → Bool × Bool) : Plane → Quarter :=
  qshift (τ 0) (tilingOfA fun m => τ (m + 1))

theorem measurableSet_qTilings : MeasurableSet {Y : Plane → Quarter | IsQTiling Y} :=
  measurableSet_legalOn_univ _ _

open Classical in
/-- The quarter phase `τ(Y)` of a tiling `Y` of `𝔸^q`; `0` if `Y` is not a tiling. -/
def qphaseOf (Y : Plane → Quarter) : ℕ → Bool × Bool :=
  if h : IsQTiling Y then Classical.choose (exists_qphase h) else fun _ => (false, false)

theorem qphaseOf_spec {Y : Plane → Quarter} (hY : IsQTiling Y) : IsQPhase Y (qphaseOf Y) := by
  rw [qphaseOf, dif_pos hY]
  exact Classical.choose_spec (exists_qphase hY)

/-- Tilings of `𝔸^q` are closed under translations. -/
theorem IsQTiling.shift {Y : Plane → Quarter} (hY : IsQTiling Y) (a : Plane) :
    IsQTiling (UPD.shift a Y) := by
  obtain ⟨ε, f, hf, rfl⟩ := quarter_exists hY
  rw [shift_qshift]
  exact isQTiling_qshift (hf.shift _) _

/-- The quarter phase map is measurable (`scf:quarter`, last claim). -/
theorem measurable_qphaseOf : Measurable qphaseOf := by
  classical
  refine Measurable.of_eval fun m => ?_
  let D := boxF (rho (m + 1))
  let g : (Plane → Quarter) → Bool × Bool := fun Y =>
    if h : ∃ Y', IsQTiling Y' ∧ ∀ x ∈ D, Y' x = Y x then qphaseOf (Classical.choose h) m
    else (false, false)
  have hg : ∀ Y Y', IsQTiling Y' → (∀ x ∈ D, Y' x = Y x) → g Y = qphaseOf Y' m := by
    intro Y Y' hY' hag
    have h : ∃ Y', IsQTiling Y' ∧ ∀ x ∈ D, Y' x = Y x := ⟨Y', hY', hag⟩
    simp only [g, dif_pos h]
    obtain ⟨hc, hcag⟩ := Classical.choose_spec h
    exact qphase_local (qphaseOf_spec hc) (qphaseOf_spec hY') (m + 1)
      (fun x hx1 hx2 => by rw [hcag x (mem_boxF hx1 hx2), hag x (mem_boxF hx1 hx2)]) m
      (by omega)
  have hgm : Measurable g := Gibbs.measurable_of_dependsOn D g fun Y Y'' hYY => by
    by_cases h : ∃ Y', IsQTiling Y' ∧ ∀ x ∈ D, Y' x = Y x
    · obtain ⟨Y', hY', hag⟩ := h
      rw [hg Y Y' hY' hag, hg Y'' Y' hY' fun x hx => (hag x hx).trans (hYY x hx)]
    · have h'' : ¬ ∃ Y', IsQTiling Y' ∧ ∀ x ∈ D, Y' x = Y'' x :=
        fun ⟨Y', hY', hag⟩ => h ⟨Y', hY', fun x hx => (hag x hx).trans (hYY x hx).symm⟩
      simp only [g, dif_neg h, dif_neg h'']
  have e : (fun Y => qphaseOf Y m) = fun Y => if IsQTiling Y then g Y else (false, false) := by
    funext Y
    by_cases hY : IsQTiling Y
    · rw [if_pos hY, hg Y Y hY fun _ _ => rfl]
    · simp only [qphaseOf, dif_neg hY, if_neg hY]
  rw [e]
  exact Measurable.ite measurableSet_qTilings hgm measurable_const

/-- `τ ↦ Y_τ` is measurable. -/
theorem measurable_qtilingOf : Measurable qtilingOf := by
  refine Measurable.of_eval fun ξ => ?_
  have hA : ∀ y : Plane, Measurable fun υ : ℕ → Bool × Bool => tilingOfA υ y := fun y =>
    ((measurable_pi_apply y).comp measurable_tilingOf).subtype_mk
  let G : (Bool × Bool) × (ℕ → Bool × Bool) → Quarter := fun p =>
    ⟨quad (ξ - bvec p.1), tilingOfA (fun m => p.2 (m + 1)) (half (ξ - bvec p.1))⟩
  have hG : Measurable G := measurable_from_prod_countable_right fun ε =>
    (measurable_of_countable (fun L : LetterA => (⟨quad (ξ - bvec ε), L⟩ : Quarter))).comp
      ((hA (half (ξ - bvec ε))).comp measurable_tail)
  have e : (fun τ => qtilingOf τ ξ) = G ∘ fun τ => (τ 0, τ) := by
    funext τ; rfl
  rw [e]
  exact hG.comp ((measurable_pi_apply 0).prodMk measurable_id)

theorem qtilingOf_spec {τ : ℕ → Bool × Bool} (hτ : QResolving τ) :
    IsQTiling (qtilingOf τ) ∧ IsQPhase (qtilingOf τ) τ := by
  have h := tilingOf_spec hτ
  exact ⟨isQTiling_qshift (f := tilingOfA fun m => τ (m + 1)) h.1 _,
    tilingOfA fun m => τ (m + 1), h.1, rfl, h.2⟩

/-- The phase system of `𝔸^q`: tilings, quarter phases, `τ ↦ Y_τ`, resolving quarter phases. -/
def quarterSystem : PhaseSystem Quarter where
  T := {Y | IsQTiling Y}
  φ := qphaseOf
  Ψ := qtilingOf
  G := {τ | QResolving τ}
  measurableSet_T := measurableSet_qTilings
  shift_mem := fun a _ hY => IsQTiling.shift hY a
  measurable_φ := measurable_qphaseOf
  measurable_Ψ := measurable_qtilingOf
  phase_shift := fun _ hY a l =>
    qphase_shift (qphaseOf_spec hY) a (qphaseOf_spec (IsQTiling.shift hY a)) l
  ae_good := ae_typical.mono fun _ h => h.1
  Ψ_mem := fun _ hτ => ⟨(qtilingOf_spec hτ).1,
    (qphaseOf_spec (qtilingOf_spec hτ).1).unique (qtilingOf_spec hτ).2⟩
  Ψ_φ := fun _ hY hτ =>
    (quarter_ti_a hτ).unique (qtilingOf_spec hτ) ⟨hY, qphaseOf_spec hY⟩

/-- **`prop:quarter-ti`(a)**, second claim: `X_{𝔸^q}` carries exactly one translation-invariant
probability measure, the image of Haar measure under `τ ↦ Y_τ`. -/
theorem quarter_ti_law :
    IsTILaw {Y : Plane → Quarter | IsQTiling Y} (haar.map qtilingOf) ∧
      ∀ μ : Measure (Plane → Quarter), IsTILaw {Y | IsQTiling Y} μ → μ = haar.map qtilingOf :=
  ⟨quarterSystem.isTILaw, fun _ hμ => quarterSystem.law_unique hμ⟩

/-- `prop:quarter-ti`(a), as "exactly one". -/
theorem quarter_ti_existsUnique :
    ∃! μ : Measure (Plane → Quarter), IsTILaw {Y | IsQTiling Y} μ :=
  quarterSystem.existsUnique_isTILaw

/-- Under every translation-invariant law of `𝔸^q` the quarter phase is Haar distributed (used in
`prop:background`(c) and Step 1 of the proof of `thm:main`); in particular it is typical almost
surely (`ae_typical`). -/
theorem quarter_phase_haar {μ : Measure (Plane → Quarter)}
    (hμ : IsTILaw {Y | IsQTiling Y} μ) : μ.map qphaseOf = haar :=
  quarterSystem.law_phase hμ

theorem quarter_phase_typical {μ : Measure (Plane → Quarter)}
    (hμ : IsTILaw {Y | IsQTiling Y} μ) : ∀ᵐ Y ∂μ, Typical (qphaseOf Y) := by
  have h := ae_typical
  rw [← quarter_phase_haar hμ] at h
  exact ae_of_ae_map measurable_qphaseOf.aemeasurable h

end UPD.Scaffold

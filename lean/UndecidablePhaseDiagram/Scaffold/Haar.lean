/-
# Section 3.3: Haar measure on phases, and Haar-almost every phase is typical

New in this project.

* Decision D9: Haar measure on `ℤ₂²` is the law `haar` of a sequence of i.i.d. uniform digit pairs
  (`Measure.infinitePi` of the uniform measure on `{0,1}²`). General facts for i.i.d. uniform
  sequences on a finite set `B` (`unifSeq B`): prefix cylinders (`cyl`) have mass `|B|^{-n}`,
  they form a π-system generating the product σ-algebra, so a probability measure with these
  masses is `unifSeq B` (`eq_unifSeq`); the shift `(υ_m) ↦ (υ_{m+1})` and the grouping of digits
  in consecutive pairs preserve the law; an event `∀ k ≥ 1, (e_{2k}, e_{2k+1}) ∈ T` with
  `T ≠ B²` is null.
* The digit map `ϖ ↦ x - ϖ` (`υ ↦ digP υ x`, the binary digits `ς_m(x)` of `x - ϖ`,
  `scf:eq-digits`) is an involution that preserves Haar measure ("for a fixed `x` and
  Haar-distributed `ϖ`, `x - ϖ` is Haar distributed"); so is `ϖ ↦ ϖ + a` (`addDig`).
* After `scf:def-resolving`: **Haar-almost every phase is resolving** (`ae_resolving`); after
  `scf:def-typical`: **Haar-almost every quarter phase is typical** (`ae_typical`), by the
  printed independence arguments.
-/
import UndecidablePhaseDiagram.Scaffold.Typical
import UndecidablePhaseDiagram.Gibbs.Weights
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace UPD.Scaffold

/-! ## I.i.d. uniform sequences on a finite set -/

section Seq

variable (B : Type) [Fintype B] [Nonempty B] [MeasurableSpace B] [MeasurableSingletonClass B]

/-- The uniform probability measure on a finite set. -/
def unif : Measure B := Measure.uniformOfFinset (Finset.univ : Finset B)

instance : IsProbabilityMeasure (unif B) := by
  constructor
  rw [unif, Measure.uniformOfFinset, Measure.finsetSum_apply]
  simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one, Finset.sum_const,
    nsmul_eq_mul, Finset.card_univ]
  exact ENNReal.mul_inv_cancel (by simp) (by simp)

/-- I.i.d. uniform sequences: the product of uniform measures on `B^ℕ`. -/
def unifSeq : Measure (ℕ → B) := Measure.infinitePi (fun _ : ℕ => unif B)

instance : IsProbabilityMeasure (unifSeq B) := by unfold unifSeq; infer_instance

variable {B}

theorem unif_singleton (b : B) : unif B {b} = (Fintype.card B : ℝ≥0∞)⁻¹ := by
  rw [unif, Measure.uniformOfFinset_apply_singleton_of_mem (Finset.mem_univ b), Finset.card_univ]

/-- The prefix cylinder `{υ : υ_m = p_m for m < n}`. -/
def cyl (n : ℕ) (p : ℕ → B) : Set (ℕ → B) := {υ | ∀ m < n, υ m = p m}

omit [Fintype B] [Nonempty B] [MeasurableSpace B] [MeasurableSingletonClass B] in
theorem cyl_eq_pi (n : ℕ) (p : ℕ → B) :
    cyl n p = Set.pi (↑(Finset.range n)) (fun m => {p m}) := by
  ext υ; simp [cyl, Set.mem_pi]

omit [Fintype B] [Nonempty B] in
theorem measurableSet_cyl (n : ℕ) (p : ℕ → B) : MeasurableSet (cyl n p) := by
  rw [cyl_eq_pi]
  exact MeasurableSet.pi (Finset.countable_toSet _) (fun _ _ => measurableSet_singleton _)

theorem unifSeq_cyl (n : ℕ) (p : ℕ → B) :
    unifSeq B (cyl n p) = (Fintype.card B : ℝ≥0∞)⁻¹ ^ n := by
  rw [cyl_eq_pi, unifSeq, Measure.infinitePi_pi _ (fun _ _ => measurableSet_singleton _)]
  simp [unif_singleton]

omit [Nonempty B] in
/-- The prefix cylinders generate the product σ-algebra. -/
theorem pi_eq_generateFrom_cyl :
    (MeasurableSpace.pi : MeasurableSpace (ℕ → B)) =
      MeasurableSpace.generateFrom {S | ∃ n p, S = cyl n p} := by
  apply le_antisymm
  · refine iSup_le fun i => Measurable.comap_le ?_
    refine @measurable_to_countable' B (ℕ → B) _ _
      (MeasurableSpace.generateFrom {S | ∃ n p, S = cyl n p}) _ (fun b => ?_)
    have e : (fun υ : ℕ → B => υ i) ⁻¹' {b} =
        ⋃ q : Fin i → B, cyl (i + 1) (fun m => if h : m < i then q ⟨m, h⟩ else b) := by
      ext υ
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion, cyl, Set.mem_setOf_eq]
      constructor
      · rintro rfl
        refine ⟨fun m => υ m, fun m hm => ?_⟩
        by_cases h : m < i
        · simp [h]
        · have : m = i := by omega
          subst this; simp
      · rintro ⟨q, hq⟩
        simpa using hq i (by omega)
    rw [e]
    exact MeasurableSet.iUnion fun q => MeasurableSpace.measurableSet_generateFrom ⟨_, _, rfl⟩
  · exact MeasurableSpace.generateFrom_le fun S ⟨n, p, hS⟩ => hS ▸ measurableSet_cyl n p

omit [Fintype B] [Nonempty B] [MeasurableSpace B] [MeasurableSingletonClass B] in
theorem isPiSystem_cyl : IsPiSystem {S : Set (ℕ → B) | ∃ n p, S = cyl n p} := by
  rintro _ ⟨n, p, rfl⟩ _ ⟨n', p', rfl⟩ ⟨υ, hυ, hυ'⟩
  refine ⟨max n n', υ, ?_⟩
  ext x
  simp only [cyl, Set.mem_inter_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2⟩ m hm
    rcases lt_max_iff.1 hm with h | h
    · exact (h1 m h).trans (hυ m h).symm
    · exact (h2 m h).trans (hυ' m h).symm
  · intro h
    exact ⟨fun m hm => (h m (lt_max_of_lt_left hm)).trans (hυ m hm),
      fun m hm => (h m (lt_max_of_lt_right hm)).trans (hυ' m hm)⟩

omit [Nonempty B] in
/-- Two probability measures on `B^ℕ` that agree on the prefix cylinders are equal. -/
theorem ext_cyl {μ ν : Measure (ℕ → B)} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : ∀ n p, μ (cyl n p) = ν (cyl n p)) : μ = ν :=
  ext_of_generate_finite _ pi_eq_generateFrom_cyl isPiSystem_cyl
    (by rintro _ ⟨n, p, rfl⟩; exact h n p) (by simp)

/-- A probability measure that gives every prefix cylinder of length `n` the mass `|B|^{-n}` is
the law of i.i.d. uniform sequences. -/
theorem eq_unifSeq {μ : Measure (ℕ → B)} [IsProbabilityMeasure μ]
    (h : ∀ n p, μ (cyl n p) = (Fintype.card B : ℝ≥0∞)⁻¹ ^ n) : μ = unifSeq B :=
  ext_cyl fun n p => by rw [h, unifSeq_cyl]

/-- The prefix `p` of length `n`, extended by a fixed value. -/
def extPre {n : ℕ} (p : Fin n → B) : ℕ → B :=
  fun m => if h : m < n then p ⟨m, h⟩ else Classical.arbitrary B

/-- The prefix cylinders of length `n` partition `B^ℕ`: their masses add up to `1`. -/
theorem sum_cyl (μ : Measure (ℕ → B)) [IsProbabilityMeasure μ] (n : ℕ) :
    ∑ p : Fin n → B, μ (cyl n (extPre p)) = 1 := by
  have hU : (⋃ p : Fin n → B, cyl n (extPre p)) = Set.univ := by
    refine Set.eq_univ_of_forall fun υ => Set.mem_iUnion.2 ⟨fun i => υ i, fun m hm => ?_⟩
    simp [extPre, hm]
  have hD : Pairwise (Function.onFun Disjoint fun p : Fin n → B => cyl n (extPre p)) := by
    intro p p' hne
    rw [Function.onFun, Set.disjoint_left]
    intro υ h h'
    apply hne
    funext i
    have e1 := h i.1 i.2
    have e2 := h' i.1 i.2
    simp only [extPre, i.2, dite_true] at e1 e2
    rw [← e1, ← e2]
  have := measure_iUnion (μ := μ) hD (fun p => measurableSet_cyl n (extPre p))
  rw [hU, measure_univ, tsum_fintype] at this
  exact this.symm

/-- If all prefix cylinders of length `n` have the same mass, it is `|B|^{-n}`. -/
theorem cyl_eq_of_const (μ : Measure (ℕ → B)) [IsProbabilityMeasure μ] (n : ℕ) (c : ℝ≥0∞)
    (h : ∀ p, μ (cyl n p) = c) : c = (Fintype.card B : ℝ≥0∞)⁻¹ ^ n := by
  have hs := sum_cyl μ n
  simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    nsmul_eq_mul] at hs
  rw [← ENNReal.inv_pow]
  refine ENNReal.eq_inv_of_mul_eq_one_left ?_
  rw [mul_comm]; exact_mod_cast hs

omit [Nonempty B] in
/-- A function of the first `n` terms of a sequence is measurable. -/
theorem measurable_of_prefix {β : Type} [MeasurableSpace β] (n : ℕ) (g : (ℕ → B) → β)
    (hg : ∀ x y : ℕ → B, (∀ m < n, x m = y m) → g x = g y) : Measurable g :=
  Gibbs.measurable_of_dependsOn (Finset.range n) g
    (fun x y h => hg x y fun m hm => h m (Finset.mem_range.2 hm))

/-- The shift `(υ_m) ↦ (υ_{m+1})` preserves the law of i.i.d. uniform sequences. -/
theorem unifSeq_map_tail :
    (unifSeq B).map (fun υ : ℕ → B => fun m => υ (m + 1)) = unifSeq B := by
  have hm : Measurable (fun υ : ℕ → B => fun m => υ (m + 1)) :=
    Measurable.of_eval fun m => measurable_pi_apply (m + 1)
  haveI := (Measure.isProbabilityMeasure_map_iff (μ := unifSeq B) hm.aemeasurable).2 inferInstance
  refine eq_unifSeq fun n p => ?_
  rw [Measure.map_apply hm (measurableSet_cyl n p)]
  have e : (fun υ : ℕ → B => fun m => υ (m + 1)) ⁻¹' cyl n p =
      Set.pi (↑((Finset.range n).map ⟨Nat.succ, Nat.succ_injective⟩)) (fun i => {p (i - 1)}) := by
    ext υ
    simp only [Set.mem_preimage, cyl, Set.mem_setOf_eq, Set.mem_pi, Finset.coe_map,
      Function.Embedding.coeFn_mk, Set.mem_image, Finset.mem_coe, Finset.mem_range,
      Set.mem_singleton_iff, forall_exists_index, and_imp]
    constructor
    · rintro h _ m hm rfl
      simpa using h m hm
    · intro h m hm
      simpa using h _ m hm rfl
  rw [e, unifSeq, Measure.infinitePi_pi _ (fun _ _ => measurableSet_singleton _)]
  simp [unif_singleton]

/-- Grouping the terms in consecutive pairs `(e_{2k}, e_{2k+1})`. -/
def pairs (e : ℕ → B) : ℕ → B × B := fun k => (e (2 * k), e (2 * k + 1))

omit [Fintype B] [Nonempty B] [MeasurableSingletonClass B] in
theorem measurable_pairs : Measurable (pairs (B := B)) :=
  Measurable.of_eval fun k =>
    (measurable_pi_apply (2 * k)).prodMk (measurable_pi_apply (2 * k + 1))

/-- Grouping in pairs maps i.i.d. uniform sequences on `B` to i.i.d. uniform sequences on `B²`. -/
theorem unifSeq_map_pairs : (unifSeq B).map pairs = unifSeq (B × B) := by
  haveI := (Measure.isProbabilityMeasure_map_iff (μ := unifSeq B) measurable_pairs.aemeasurable).2 inferInstance
  refine eq_unifSeq fun n Q => ?_
  rw [Measure.map_apply measurable_pairs (measurableSet_cyl n Q)]
  have e : pairs ⁻¹' cyl n Q =
      cyl (2 * n) (fun m => if m % 2 = 0 then (Q (m / 2)).1 else (Q (m / 2)).2) := by
    ext υ
    simp only [Set.mem_preimage, cyl, Set.mem_setOf_eq, pairs]
    constructor
    · intro h m hm
      have hk := h (m / 2) (by omega)
      rcases Nat.mod_two_eq_zero_or_one m with h0 | h1
      · rw [if_pos h0, ← hk]
        congr 1; omega
      · rw [if_neg (by omega), ← hk]
        congr 1; omega
    · intro h k hk
      have h1 := h (2 * k) (by omega)
      have h2 := h (2 * k + 1) (by omega)
      rw [if_pos (by omega)] at h1
      rw [if_neg (by omega)] at h2
      rw [show 2 * k / 2 = k by omega] at h1
      rw [show (2 * k + 1) / 2 = k by omega] at h2
      rw [h1, h2]
  rw [e, unifSeq_cyl, Fintype.card_prod, pow_mul]
  push_cast
  rw [ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _))]
  ring

/-- An event `∀ k ≥ 1, e_k ∈ T` of an i.i.d. uniform sequence with `T ≠ B` is null. -/
theorem unifSeq_forall_mem_null {T : Set B} (hT : T ≠ Set.univ) :
    unifSeq B {e | ∀ k, 1 ≤ k → e k ∈ T} = 0 := by
  obtain ⟨b0, hb0⟩ : ∃ b0, b0 ∉ T := by
    by_contra h
    push Not at h
    exact hT (Set.eq_univ_of_forall h)
  have hTm : MeasurableSet T := (Set.toFinite T).measurableSet
  have hlt : unif B T < 1 := by
    have h1 : unif B T + unif B {b0} ≤ 1 := by
      rw [← measure_union (Set.disjoint_singleton_right.2 hb0) (measurableSet_singleton _)]
      exact prob_le_one
    have h2 : unif B {b0} ≠ 0 := by rw [unif_singleton]; simp
    exact lt_of_lt_of_le (ENNReal.lt_add_right (measure_ne_top _ _) h2) h1
  refine le_antisymm (ge_of_tendsto' (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hlt)
    fun K => ?_) (by simp)
  calc unifSeq B {e | ∀ k, 1 ≤ k → e k ∈ T}
      ≤ unifSeq B (Set.pi (↑(Finset.Icc 1 K)) (fun _ => T)) :=
        measure_mono fun e he k hk => he k (Finset.mem_Icc.1 hk).1
    _ = unif B T ^ K := by
        rw [unifSeq, Measure.infinitePi_pi _ (fun _ _ => hTm)]
        simp

/-- Almost every i.i.d. uniform sequence has a pair `(e_{2k}, e_{2k+1})`, `k ≥ 1`, outside a
given proper subset `T` of `B²`. -/
theorem ae_exists_pair {T : Set (B × B)} (hT : T ≠ Set.univ) :
    ∀ᵐ e ∂(unifSeq B), ∃ k, 1 ≤ k ∧ (e (2 * k), e (2 * k + 1)) ∉ T := by
  have h0 : ∀ᵐ Q ∂(unifSeq (B × B)), ∃ k, 1 ≤ k ∧ Q k ∉ T := by
    rw [ae_iff]
    refine measure_mono_null ?_ (unifSeq_forall_mem_null hT)
    intro Q hQ k hk
    by_contra h
    exact hQ ⟨k, hk, h⟩
  rw [← unifSeq_map_pairs] at h0
  exact ae_of_ae_map measurable_pairs.aemeasurable h0

end Seq

/-! ## Haar measure on phases (decision D9) -/

/-- Haar measure on `ℤ₂²` (decision D9): the law of i.i.d. uniform digit pairs. -/
def haar : Measure (ℕ → Bool × Bool) := unifSeq (Bool × Bool)

theorem haar_def : haar = unifSeq (Bool × Bool) := rfl

instance : IsProbabilityMeasure haar := by unfold haar; infer_instance

theorem anc_congr {c c' : ℕ → Bool} {m : ℕ} (h : ∀ i < m, c i = c' i) (z : ℤ) :
    anc c m z = anc c' m z := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [anc]
    rw [ih (fun i hi => h i (by omega)), h m (by omega)]

/-- The digit `ς_m(z)` depends only on the digits `υ_0, …, υ_m` of the phase. -/
theorem dig_congr {c c' : ℕ → Bool} {m : ℕ} (h : ∀ i ≤ m, c i = c' i) (z : ℤ) :
    dig c m z = dig c' m z := by
  simp only [dig]
  rw [anc_congr (fun i hi => h i hi.le), h m le_rfl]

theorem digP_congr {υ υ' : ℕ → Bool × Bool} {m : ℕ} (h : ∀ i ≤ m, υ i = υ' i) (x : Plane) :
    digP υ x m = digP υ' x m := by
  simp only [digP]
  rw [dig_congr (c' := col υ') (fun i hi => by simp [col, h i hi]) x.1,
    dig_congr (c' := row υ') (fun i hi => by simp [row, h i hi]) x.2]

/-- `M ∣ X mod M - X`. -/
theorem dvd_emod_sub (X M : ℤ) : M ∣ X % M - X := ⟨-(X / M), by rw [Int.emod_def]; ring⟩

/-- `x - (x - ϖ) = ϖ`, digitwise: the digit map `c ↦ (ς_m)` of `z - ·` is an involution. -/
theorem dig_dig (c : ℕ → Bool) (z : ℤ) : (fun m => dig (fun k => dig c k z) m z) = c := by
  apply eq_of_wsum_eq
  intro l
  rw [← emod_eq_wsum_dig, ← emod_eq_wsum_dig]
  obtain ⟨k, hk⟩ := dvd_emod_sub (z - wsum c l) (2 ^ l)
  rw [show z - (z - wsum c l) % 2 ^ l = wsum c l + 2 ^ l * (-k) by linear_combination -hk,
    Int.add_mul_emod_self_left, Int.emod_eq_of_lt (wsum_nonneg _ _) (wsum_lt _ _)]

/-- The digit sequence of `x - (x - ϖ)` is that of `ϖ`. -/
theorem digP_digP (υ : ℕ → Bool × Bool) (x : Plane) :
    (fun m => digP (fun k => digP υ x k) x m) = υ := by
  funext m
  exact Prod.ext (congrFun (dig_dig (col υ) x.1) m) (congrFun (dig_dig (row υ) x.2) m)

theorem digP_mem_cyl_iff (υ q : ℕ → Bool × Bool) (x : Plane) (n : ℕ) :
    (fun m => digP υ x m) ∈ cyl n q ↔ υ ∈ cyl n (fun m => digP q x m) := by
  constructor
  · intro h m hm
    rw [← congrFun (digP_digP υ x) m]
    exact digP_congr (fun i hi => h i (by omega)) x
  · intro h m hm
    rw [← congrFun (digP_digP q x) m]
    exact digP_congr (fun i hi => h i (by omega)) x

theorem measurable_digP (x : Plane) :
    Measurable (fun υ : ℕ → Bool × Bool => fun m => digP υ x m) :=
  Measurable.of_eval fun m => measurable_of_prefix (m + 1) _
    fun υ υ' h => digP_congr (fun i hi => h i (by omega)) x

/-- After `scf:def-resolving`: "for a fixed `x` and Haar-distributed `ϖ`, `x - ϖ` is Haar
distributed". -/
theorem haar_map_digP (x : Plane) : haar.map (fun υ => fun m => digP υ x m) = haar := by
  rw [haar_def]
  haveI := (Measure.isProbabilityMeasure_map_iff (μ := unifSeq (Bool × Bool)) (measurable_digP x).aemeasurable).2 inferInstance
  refine eq_unifSeq fun n q => ?_
  rw [Measure.map_apply (measurable_digP x) (measurableSet_cyl n q)]
  have e : (fun υ : ℕ → Bool × Bool => fun m => digP υ x m) ⁻¹' cyl n q =
      cyl n (fun m => digP q x m) := by
    ext υ; exact digP_mem_cyl_iff υ q x n
  rw [e, unifSeq_cyl]

/-- The digits of `ϖ + a = 0 - ((-a) - ϖ)`. -/
def addDig (a : Plane) (υ : ℕ → Bool × Bool) : ℕ → Bool × Bool :=
  fun m => digP (fun k => digP υ (-a) k) 0 m

theorem measurable_addDig (a : Plane) : Measurable (addDig a) :=
  (measurable_digP 0).comp (measurable_digP (-a))

/-- Haar measure is invariant under `ϖ ↦ ϖ + a`. -/
theorem haar_map_addDig (a : Plane) : haar.map (addDig a) = haar := by
  rw [show addDig a = (fun υ => fun m => digP υ 0 m) ∘ (fun υ => fun m => digP υ (-a) m) from rfl,
    ← Measure.map_map (measurable_digP 0) (measurable_digP (-a)), haar_map_digP, haar_map_digP]

/-- `addDig a υ` is the digit sequence of `ϖ + a`: `(ϖ + a) mod 2^l ≡ (ϖ mod 2^l) + a`. -/
theorem wsum_addDig (a : Plane) (υ : ℕ → Bool × Bool) (l : ℕ) :
    (2 : ℤ) ^ l ∣ wsum (col (addDig a υ)) l - wsum (col υ) l - a.1 ∧
      (2 : ℤ) ^ l ∣ wsum (row (addDig a υ)) l - wsum (row υ) l - a.2 := by
  have key : ∀ (c : ℕ → Bool) (b : ℤ),
      (2 : ℤ) ^ l ∣ wsum (fun m => dig (fun k => dig c k (-b)) m 0) l - wsum c l - b := by
    intro c b
    rw [← emod_eq_wsum_dig, ← emod_eq_wsum_dig]
    have h1 := dvd_emod_sub (0 - (-b - wsum c l) % 2 ^ l) (2 ^ l)
    have h2 := dvd_emod_sub (-b - wsum c l) (2 ^ l)
    have := dvd_sub h1 h2
    convert this using 1; ring
  exact ⟨key (col υ) a.1, key (row υ) a.2⟩

/-! ## Haar-almost every phase is resolving and typical -/

theorem measurable_tail :
    Measurable (fun υ : ℕ → Bool × Bool => fun m => υ (m + 1)) :=
  Measurable.of_eval fun m => measurable_pi_apply (m + 1)

/-- After `scf:def-resolving`: **Haar-almost every phase is resolving** (the digit pairs of
`x - ϖ` at positions `(2k, 2k+1)` are independent and uniform on `16` values). -/
theorem ae_resolving : ∀ᵐ υ ∂haar, Resolving υ := by
  unfold Resolving
  rw [ae_all_iff]
  intro x
  have h := ae_exists_pair (B := Bool × Bool)
    (T := {q | q ≠ ((true, true), (true, true))})
    (by intro h; have := Set.eq_univ_iff_forall.1 h ((true, true), (true, true)); simp at this)
  rw [← haar_def, ← haar_map_digP x] at h
  filter_upwards [ae_of_ae_map (measurable_digP x).aemeasurable h] with υ hυ
  obtain ⟨k, -, hk⟩ := hυ
  simp only [not_not, Prod.mk.injEq] at hk
  exact ⟨2 * k, hk.1, hk.2⟩

/-- After `scf:def-typical`: **Haar-almost every quarter phase is typical** (`ℤ²` is countable;
for fixed `z` the binary and base-4 digits of `z - τ_i` are independent and uniform). -/
theorem ae_typical : ∀ᵐ τ ∂haar, Typical τ := by
  have hQ : ∀ᵐ τ ∂haar, QResolving τ := by
    have h := ae_resolving
    rw [haar_def, ← unifSeq_map_tail, ← haar_def] at h
    exact ae_of_ae_map measurable_tail.aemeasurable h
  have hpair : ∀ (x : Plane) (T : Set ((Bool × Bool) × (Bool × Bool))), T ≠ Set.univ →
      ∀ᵐ τ ∂haar, ∃ k, 1 ≤ k ∧ (digP τ x (2 * k), digP τ x (2 * k + 1)) ∉ T := by
    intro x T hT
    have h := ae_exists_pair hT
    rw [← haar_def, ← haar_map_digP x] at h
    exact ae_of_ae_map (measurable_digP x).aemeasurable h
  have hne : ∀ (P : (Bool × Bool) × (Bool × Bool) → Prop) (q : (Bool × Bool) × (Bool × Bool)),
      ¬ P q → {q | P q} ≠ Set.univ := by
    intro P q hq h
    exact hq (Set.eq_univ_iff_forall.1 h q)
  have hN1 : ∀ᵐ τ ∂haar, NotInt (col τ) := by
    unfold NotInt; rw [ae_all_iff]; intro z
    filter_upwards [hpair (z, 0) _ (hne (fun q => q.1.1 = false) ((true, true), (true, true))
      (by simp))] with τ hτ
    obtain ⟨k, -, hk⟩ := hτ
    simp only [Bool.not_eq_false] at hk
    exact ⟨2 * k, hk⟩
  have hN2 : ∀ᵐ τ ∂haar, NotInt (row τ) := by
    unfold NotInt; rw [ae_all_iff]; intro z
    filter_upwards [hpair (0, z) _ (hne (fun q => q.1.2 = false) ((true, true), (true, true))
      (by simp))] with τ hτ
    obtain ⟨k, -, hk⟩ := hτ
    simp only [Bool.not_eq_false] at hk
    exact ⟨2 * k, hk⟩
  have hD1 : ∀ᵐ τ ∂haar, ∀ z : ℤ, ∃ d, 1 ≤ d ∧ Digit2 (col τ) z d := by
    rw [ae_all_iff]; intro z
    filter_upwards [hpair (z, 0) _
      (hne (fun q => ¬ (q.1.1 = false ∧ q.2.1 = true)) ((false, false), (true, true))
      (by simp))] with τ hτ
    obtain ⟨k, hk1, hk⟩ := hτ
    simp only [not_not] at hk
    exact ⟨k, hk1, hk⟩
  have hD2 : ∀ᵐ τ ∂haar, ∀ z : ℤ, ∃ d, 1 ≤ d ∧ Digit2 (row τ) z d := by
    rw [ae_all_iff]; intro z
    filter_upwards [hpair (0, z) _
      (hne (fun q => ¬ (q.1.2 = false ∧ q.2.2 = true)) ((false, false), (true, true))
      (by simp))] with τ hτ
    obtain ⟨k, hk1, hk⟩ := hτ
    simp only [not_not] at hk
    exact ⟨k, hk1, hk⟩
  filter_upwards [hQ, hN1, hN2, hD1, hD2] with τ h1 h2 h3 h4 h5
  exact ⟨h1, h2, h3, h4, h5⟩

end UPD.Scaffold

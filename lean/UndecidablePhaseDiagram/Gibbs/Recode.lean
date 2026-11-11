/-
# Recoding a factor system as an Ising model (`pay:effective`)

New in this project (session 10). The proof of `pay:effective` ends with a factor specification on
the spins whose values lie in a larger set (the spin coordinates of the payload take values in a
finite set `E` containing a copy `ι(Spin)` of the two spin values), whose weights vanish off that
copy and are proportional there to the Ising weights of a graph ("constant factors do not change a
specification"). This file proves the abstract statement:

* `WeightSystem.toHard`: a positive weight system viewed as a hard-constraint weight system, and
  `WeightSystem.isDLR_iff_isGibbs_toHard` (the paper's DLR identity for positive weights is the
  Gibbs property of the hard system);
* `expect_recode`: the kernel of the factor system at a recoded configuration `ι ∘ σ` is the Ising
  kernel at `σ` (the fillings with a value outside `ι(Spin)` have weight `0`, and the constant `c`
  cancels);
* **`isGibbs_map_recode`**, **`isDLR_map_decode`**, **`isGibbs_iff_recode`**: the Gibbs measures
  of the factor system are exactly the images `ν.map (ι ∘ ·)` of the Gibbs measures `ν` of the
  Ising model, and `ν` is recovered as the image under `r ∘ ·`, `r` a left inverse of `ι`.
-/
import UndecidablePhaseDiagram.Gibbs.Factor
import UndecidablePhaseDiagram.Gibbs.Transport
import UndecidablePhaseDiagram.Gibbs.Dobrushin

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace UPD

namespace Gibbs

/-! ## Positive weight systems as hard-constraint systems -/

namespace WeightSystem

variable {I E : Type} [DecidableEq I] (ws : WeightSystem I E)

/-- A weight system with positive weights as a hard-constraint weight system (the support
property is vacuous). -/
def toHard : HardWeightSystem I E where
  W := ws.W
  nonneg Λ ω := (ws.pos Λ ω).le
  range := ws.range
  isLocal := ws.isLocal
  ratio := ws.ratio
  support Λ _ _ ω h := absurd h (ws.pos Λ ω).ne'

theorem toHard_W : ws.toHard.W = ws.W := rfl

/-- The two systems have the same kernels. -/
theorem toHard_expect [Fintype E] (Λ : Finset I) (ω : I → E) (F : (I → E) → ℝ) :
    ws.toHard.expect Λ ω F = ws.expect Λ ω F := rfl

/-- The paper's DLR identity for positive weights (`IsDLR`) is the Gibbs property of the
hard-constraint system (every weight is positive everywhere). -/
theorem isDLR_iff_isGibbs_toHard [Fintype E] [MeasurableSpace E] (μ : Measure (I → E)) :
    ws.IsDLR μ ↔ ws.toHard.IsGibbs μ :=
  ⟨fun h => ⟨h.1, ae_of_all _ fun ω Λ => ws.pos Λ ω, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩

end WeightSystem

/-! ## Recoding -/

section Recode

variable {V E K : Type} [DecidableEq V] [DecidableEq K] [Fintype E] [DecidableEq E]

omit [Fintype E] [DecidableEq E] in
/-- Filling commutes with recoding. -/
theorem fillOn_recode (ι : Spin → E) (σ : V → Spin) (Λ : Finset V) (ζ : Λ → Spin) :
    fillOn (fun v => ι (σ v)) Λ (fun x => ι (ζ x)) = fun v => ι (fillOn σ Λ ζ v) := by
  funext v
  by_cases h : v ∈ Λ <;> simp [fillOn, h]

/-- A sum over the fillings with values in `E` that vanishes on the fillings with a value outside
`ι(Spin)` is the sum over the spin fillings. -/
theorem sum_fillOn_recode (ι : Spin → E) (r : E → Spin) (hr : ∀ s, r (ι s) = s)
    (Λ : Finset V) (σ : V → Spin) (g : (V → E) → ℝ)
    (hg : ∀ ζ : Λ → E, (∃ x : Λ, ζ x ∉ Set.range ι) → g (fillOn (fun v => ι (σ v)) Λ ζ) = 0) :
    ∑ ζ : Λ → E, g (fillOn (fun v => ι (σ v)) Λ ζ) =
      ∑ ζ : Λ → Spin, g (fun v => ι (fillOn σ Λ ζ v)) := by
  have hinj : Function.Injective (fun (ζ : Λ → Spin) (x : Λ) => ι (ζ x)) := by
    intro ζ ζ' h
    funext x
    have := congrArg (fun f : Λ → E => r (f x)) h
    simpa only [hr] using this
  have hsub : (Finset.univ.image fun (ζ : Λ → Spin) (x : Λ) => ι (ζ x)) ⊆ Finset.univ :=
    Finset.subset_univ _
  calc ∑ ζ : Λ → E, g (fillOn (fun v => ι (σ v)) Λ ζ)
      = ∑ ζ ∈ Finset.univ.image (fun (ζ : Λ → Spin) (x : Λ) => ι (ζ x)),
          g (fillOn (fun v => ι (σ v)) Λ ζ) := by
        refine (Finset.sum_subset hsub fun ζ _ hζ => hg ζ ?_).symm
        by_contra hall
        simp only [not_exists, not_not] at hall
        apply hζ
        refine Finset.mem_image.2 ⟨fun x => r (ζ x), Finset.mem_univ _, funext fun x => ?_⟩
        obtain ⟨s, hs⟩ := hall x
        simp only [← hs, hr]
    _ = ∑ ζ : Λ → Spin, g (fillOn (fun v => ι (σ v)) Λ (fun x => ι (ζ x))) :=
        Finset.sum_image hinj.injOn
    _ = ∑ ζ : Λ → Spin, g (fun v => ι (fillOn σ Λ ζ v)) := by
        simp only [fillOn_recode]

variable (ι : Spin → E) (r : E → Spin) (G : IsingGraph V) (fs : FactorSystem V E K)

/-- **The kernels agree** (proof of `pay:effective`): if the weights of the factor system vanish
at the configurations with a value outside `ι(Spin)` in `Λ` and are proportional to the Ising
weights on the recoded configurations, the kernel of the factor system at `ι ∘ σ` is the Ising
kernel at `σ`. -/
theorem expect_recode (hr : ∀ s, r (ι s) = s)
    (hkind : ∀ (Λ : Finset V) (x : V → E), 0 < fs.toHard.W Λ x → ∀ v ∈ Λ, x v ∈ Set.range ι)
    (hW : ∀ Λ : Finset V, ∃ c : ℝ, 0 < c ∧
      ∀ σ : V → Spin, fs.toHard.W Λ (fun v => ι (σ v)) = c * G.weight Λ σ)
    (Λ : Finset V) (σ : V → Spin) (F : (V → E) → ℝ) :
    fs.toHard.expect Λ (fun v => ι (σ v)) F =
      G.toWeightSystem.expect Λ σ (fun σ' => F (fun v => ι (σ' v))) := by
  obtain ⟨c, hc, hcW⟩ := hW Λ
  have hzero : ∀ x : V → E, (∃ v ∈ Λ, x v ∉ Set.range ι) → fs.toHard.W Λ x = 0 := by
    rintro x ⟨v, hv, hx⟩
    rcases (fs.toHard.nonneg Λ x).eq_or_lt with h | h
    · exact h.symm
    · exact absurd (hkind Λ x h v hv) hx
  have hfill : ∀ ζ : Λ → E, (∃ x : Λ, ζ x ∉ Set.range ι) →
      ∃ v ∈ Λ, fillOn (fun v => ι (σ v)) Λ ζ v ∉ Set.range ι := by
    rintro ζ ⟨x, hx⟩
    exact ⟨x.1, x.2, by rw [fillOn_of_mem _ _ x.2]; exact hx⟩
  have hZ : fs.toHard.Z Λ (fun v => ι (σ v)) = c * G.toWeightSystem.Z Λ σ := by
    calc fs.toHard.Z Λ (fun v => ι (σ v))
        = ∑ ζ : Λ → E, fs.toHard.W Λ (fillOn (fun v => ι (σ v)) Λ ζ) := rfl
      _ = ∑ ζ : Λ → Spin, fs.toHard.W Λ (fun v => ι (fillOn σ Λ ζ v)) :=
          sum_fillOn_recode ι r hr Λ σ (fs.toHard.W Λ) fun ζ h => hzero _ (hfill ζ h)
      _ = ∑ ζ : Λ → Spin, c * G.weight Λ (fillOn σ Λ ζ) :=
          Finset.sum_congr rfl fun ζ _ => hcW _
      _ = c * G.toWeightSystem.Z Λ σ := by
          rw [← Finset.mul_sum]; rfl
  calc fs.toHard.expect Λ (fun v => ι (σ v)) F
      = ∑ ζ : Λ → E, (fun x => fs.toHard.W Λ x / fs.toHard.Z Λ (fun v => ι (σ v)) * F x)
          (fillOn (fun v => ι (σ v)) Λ ζ) := rfl
    _ = ∑ ζ : Λ → Spin, (fun x => fs.toHard.W Λ x / fs.toHard.Z Λ (fun v => ι (σ v)) * F x)
          (fun v => ι (fillOn σ Λ ζ v)) :=
        sum_fillOn_recode ι r hr Λ σ
          (fun x => fs.toHard.W Λ x / fs.toHard.Z Λ (fun v => ι (σ v)) * F x) fun ζ h => by
          simp only [hzero _ (hfill ζ h), zero_div, zero_mul]
    _ = ∑ ζ : Λ → Spin, G.weight Λ (fillOn σ Λ ζ) / G.toWeightSystem.Z Λ σ *
          F (fun v => ι (fillOn σ Λ ζ v)) := by
        refine Finset.sum_congr rfl fun ζ _ => ?_
        simp only [hcW, hZ, mul_div_mul_left _ _ hc.ne']
    _ = G.toWeightSystem.expect Λ σ (fun σ' => F (fun v => ι (σ' v))) := rfl

variable [MeasurableSpace E] [DiscreteMeasurableSpace E] [Countable V]

omit [DecidableEq V] [DecidableEq K] [Fintype E] [DecidableEq E] [DiscreteMeasurableSpace E]
  [Countable V] in
theorem measurable_recode : Measurable (fun (σ : V → Spin) (v : V) => ι (σ v)) :=
  Measurable.of_eval fun v => Measurable.of_discrete.comp (measurable_pi_apply v)

omit [DecidableEq V] [DecidableEq K] [Fintype E] [DecidableEq E] [Countable V] in
theorem measurable_decode : Measurable (fun (x : V → E) (v : V) => r (x v)) :=
  Measurable.of_eval fun v => Measurable.of_discrete.comp (measurable_pi_apply v)

/-- **`pay:effective`, the recoding (Ising to factors)**: the image `ν.map (ι ∘ ·)` of a Gibbs
measure `ν` of the Ising model on `G` is Gibbs for the factor system. -/
theorem isGibbs_map_recode (hr : ∀ s, r (ι s) = s)
    (hkind : ∀ (Λ : Finset V) (x : V → E), 0 < fs.toHard.W Λ x → ∀ v ∈ Λ, x v ∈ Set.range ι)
    (hW : ∀ Λ : Finset V, ∃ c : ℝ, 0 < c ∧
      ∀ σ : V → Spin, fs.toHard.W Λ (fun v => ι (σ v)) = c * G.weight Λ σ)
    {ν : Measure (V → Spin)} (hν : G.toWeightSystem.IsDLR ν) :
    fs.toHard.IsGibbs (ν.map fun σ v => ι (σ v)) := by
  refine HardWeightSystem.isGibbs_map G.toWeightSystem.toHard fs.toHard (measurable_recode ι)
    (A := Set.univ) ?_ ?_ ((G.toWeightSystem.isDLR_iff_isGibbs_toHard ν).1 hν)
    (ae_of_all _ fun _ => trivial)
  · intro σ _ Λ
    obtain ⟨c, hc, hcW⟩ := hW Λ
    rw [hcW]
    exact mul_pos hc (Real.exp_pos _)
  · intro Λ
    exact ⟨Λ, subset_rfl, Λ, fun σ _ F => expect_recode ι r G fs hr hkind hW Λ σ F⟩

/-- **`pay:effective`, the decoding (factors to Ising)**: if `μ` is Gibbs for the factor system,
its image under `r ∘ ·` is a Gibbs measure of the Ising model on `G`, and `μ` is the recoding of
that image. -/
theorem isDLR_map_decode (hr : ∀ s, r (ι s) = s)
    (hkind : ∀ (Λ : Finset V) (x : V → E), 0 < fs.toHard.W Λ x → ∀ v ∈ Λ, x v ∈ Set.range ι)
    (hW : ∀ Λ : Finset V, ∃ c : ℝ, 0 < c ∧
      ∀ σ : V → Spin, fs.toHard.W Λ (fun v => ι (σ v)) = c * G.weight Λ σ)
    {μ : Measure (V → E)} (hμ : fs.toHard.IsGibbs μ) :
    G.toWeightSystem.IsDLR (μ.map fun x v => r (x v)) ∧
      μ = (μ.map fun x v => r (x v)).map fun σ v => ι (σ v) := by
  have hA : ∀ᵐ x ∂μ, x ∈ {x : V → E | ∀ Λ : Finset V, 0 < fs.toHard.W Λ x} := hμ.2.1
  have hrange : ∀ x ∈ {x : V → E | ∀ Λ : Finset V, 0 < fs.toHard.W Λ x},
      (fun v => ι (r (x v))) = x := by
    intro x hx
    funext v
    obtain ⟨s, hs⟩ := hkind {v} x (hx {v}) v (Finset.mem_singleton_self v)
    rw [← hs, hr]
  constructor
  · rw [WeightSystem.isDLR_iff_isGibbs_toHard]
    refine HardWeightSystem.isGibbs_map fs.toHard G.toWeightSystem.toHard (measurable_decode r)
      ?_ ?_ hμ hA
    · intro x _ Λ
      exact G.toWeightSystem.pos Λ _
    · intro Λ
      refine ⟨Λ, subset_rfl, Λ, fun x hx F => ?_⟩
      calc G.toWeightSystem.toHard.expect Λ (fun v => r (x v)) F
          = G.toWeightSystem.expect Λ (fun v => r (x v))
              (fun σ' => (fun y : V → E => F (fun v => r (y v))) (fun v => ι (σ' v))) := by
            rw [WeightSystem.toHard_expect]
            simp only [hr]
        _ = fs.toHard.expect Λ (fun v => ι (r (x v))) (fun y => F (fun v => r (y v))) :=
            (expect_recode ι r G fs hr hkind hW Λ (fun v => r (x v)) (fun y => F (fun v => r (y v)))).symm
        _ = fs.toHard.expect Λ x (fun y => F (fun v => r (y v))) := by
            rw [hrange x hx]
  · exact (map_map_eq_self (measurable_decode r) (measurable_recode ι)
      (by filter_upwards [hA] with x hx using hrange x hx)).symm

/-- **`pay:effective`, the identification**: the Gibbs measures of the factor system are exactly
the recodings `ν.map (ι ∘ ·)` of the Gibbs measures `ν` of the Ising model on `G`. -/
theorem isGibbs_iff_recode (hr : ∀ s, r (ι s) = s)
    (hkind : ∀ (Λ : Finset V) (x : V → E), 0 < fs.toHard.W Λ x → ∀ v ∈ Λ, x v ∈ Set.range ι)
    (hW : ∀ Λ : Finset V, ∃ c : ℝ, 0 < c ∧
      ∀ σ : V → Spin, fs.toHard.W Λ (fun v => ι (σ v)) = c * G.weight Λ σ)
    (μ : Measure (V → E)) :
    fs.toHard.IsGibbs μ ↔ ∃ ν : Measure (V → Spin), G.toWeightSystem.IsDLR ν ∧
      μ = ν.map fun σ v => ι (σ v) := by
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := isDLR_map_decode ι r G fs hr hkind hW h
    exact ⟨_, h1, h2⟩
  · rintro ⟨ν, hν, rfl⟩
    exact isGibbs_map_recode ι r G fs hr hkind hW hν

end Recode

end Gibbs

end UPD

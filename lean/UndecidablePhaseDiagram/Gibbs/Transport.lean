/-
# Transport of Gibbs measures between hard-constraint systems

New in this project (session 9). Several steps of Section 6 identify the Gibbs measures of one
hard-constraint weight system with those of another: the frozen system on the site values and on
the payload coordinates (the measure-level bridge), the frozen kernels and the factors `W_e` of
`pay:factor`, the factors `Z_e` of `pay:elim` and the Ising model of `pay:effective`. They are all
instances of one lemma:

* **`isGibbs_map`**: let `f` be a measurable map between the configuration spaces of two
  hard-constraint systems and `A` a set of configurations such that (i) on `A` every weight of the
  target system is positive at `f x`, and (ii) for a cofinal family of finite sets `Λ''` of target
  coordinates there is a finite set `Λ` of source coordinates whose kernel is carried by `f` to the
  kernel of `Λ''` at every point of `A`. Then the image under `f` of every Gibbs measure
  concentrated on `A` is Gibbs (by `set:consistency` in the paper's form, `dlr_of_superset`).
* `measurableSet_pos`: the set of configurations at which every weight is positive is measurable
  (countably many coordinates).
* `map_map_eq_self`: a left inverse on a set of full measure undoes the image.
-/
import UndecidablePhaseDiagram.Gibbs.Hard

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace UPD

namespace Gibbs

namespace HardWeightSystem

variable {I E : Type} [DecidableEq I] [Fintype E] [MeasurableSpace E] [DiscreteMeasurableSpace E]

/-- Each weight is a measurable function (it depends on finitely many coordinates). -/
theorem measurable_W (ws : HardWeightSystem I E) (Λ : Finset I) : Measurable (ws.W Λ) :=
  measurable_of_dependsOn (ws.range Λ) _ (ws.isLocal Λ)

/-- The configurations at which every weight is positive form a measurable set. -/
theorem measurableSet_pos [Countable I] (ws : HardWeightSystem I E) :
    MeasurableSet {x : I → E | ∀ Λ : Finset I, 0 < ws.W Λ x} := by
  have e : {x : I → E | ∀ Λ : Finset I, 0 < ws.W Λ x} = ⋂ Λ : Finset I, {x | 0 < ws.W Λ x} := by
    ext x; simp
  rw [e]
  exact MeasurableSet.iInter fun Λ => measurableSet_lt measurable_const (ws.measurable_W Λ)

variable {I' E' : Type} [DecidableEq I'] [Fintype E'] [DecidableEq E'] [MeasurableSpace E']
  [DiscreteMeasurableSpace E'] [Countable I']

omit [DiscreteMeasurableSpace E] in
/-- **Transport of Gibbs measures.** If `f` carries the kernels of a cofinal family of finite sets
of target coordinates to kernels of the source system at every point of `A`, and every target
weight is positive on `f(A)`, then `f` maps the Gibbs measures concentrated on `A` to Gibbs
measures. -/
theorem isGibbs_map (ws : HardWeightSystem I E) (ws' : HardWeightSystem I' E')
    {f : (I → E) → (I' → E')} (hf : Measurable f) {A : Set (I → E)}
    (hpos : ∀ x ∈ A, ∀ Λ' : Finset I', 0 < ws'.W Λ' (f x))
    (hker : ∀ Λ' : Finset I', ∃ Λ'' : Finset I', Λ' ⊆ Λ'' ∧ ∃ Λ : Finset I,
      ∀ x ∈ A, ∀ G : (I' → E') → ℝ, ws'.expect Λ'' (f x) G = ws.expect Λ x (fun y => G (f y)))
    {μ : Measure (I → E)} (hμ : ws.IsGibbs μ) (hA : ∀ᵐ x ∂μ, x ∈ A) : ws'.IsGibbs (μ.map f) := by
  haveI := hμ.1
  refine ⟨(Measure.isProbabilityMeasure_map_iff hf.aemeasurable).2 inferInstance, ?_, fun Λ' G hG hb => ?_⟩
  · rw [ae_map_iff hf.aemeasurable ws'.measurableSet_pos]
    filter_upwards [hA] with x hx using hpos x hx
  · obtain ⟨Λ'', hsub, Λ, hk⟩ := hker Λ'
    refine ws'.dlr_of_superset hsub (fun G hG hb => ?_) G hG hb
    obtain ⟨C, hC⟩ := hb
    rw [integral_map hf.aemeasurable hG.aestronglyMeasurable,
      integral_map hf.aemeasurable (ws'.measurable_expect Λ'' hG).aestronglyMeasurable]
    rw [hμ.2.2 Λ (fun x => G (f x)) (hG.comp hf) ⟨C, fun x => hC (f x)⟩]
    refine integral_congr_ae ?_
    filter_upwards [hA] with x hx
    exact (hk x hx G).symm

end HardWeightSystem

/-- A map that is left inverse to `f` on a set of full measure undoes the image of `f`. -/
theorem map_map_eq_self {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
    {f : α → β} {g : β → α} (hf : Measurable f) (hg : Measurable g) {μ : Measure α}
    (h : ∀ᵐ x ∂μ, g (f x) = x) : (μ.map f).map g = μ := by
  rw [Measure.map_map hg hf]
  have e : (g ∘ f) =ᵐ[μ] id := h
  rw [Measure.map_congr e, Measure.map_id]

end Gibbs

end UPD

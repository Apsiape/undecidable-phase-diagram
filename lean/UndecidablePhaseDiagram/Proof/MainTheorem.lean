/-
# `thm:main`

The three claims of `thm:main` and the existence of a universal machine (non-vacuity of
Corollary B). Session 10: the three claims of `thm:main` are proved. Session 11:
`exists_universal` is proved (`Compiler/Universal.lean`: Mathlib's halting problem through a
universal `TM0` machine folded onto a one-sided tape with unary input).

The proof (Section 7 of the paper, with the route of `Proof/Steps.lean` and `Proof/Main2.lean`):
* `pay:effective` (`Payload/Effective.lean`, `pay_effective`, with the edge sums of
  `Payload/EdgeSums.lean`): for typical `τ`, the Gibbs measures for `βΦ` concentrated on the
  background `𝔟_τ` are exactly the lifts `liftCfg U τ β ν` of the Gibbs measures `ν` of the Ising
  model on `Γ_τ` (`Payload/Graph.lean`), and the spin marginal of `liftCfg U τ β ν` is `ν`;
* Step 1 (`step1`), Step 2 (uniqueness `tiGibbs_unique` from `H1`; existence by averaging,
  `Gibbs/Average.lean`), Step 3 (`thm_main_ii_of`, from `H2`: plus and minus states on the component
  of one depth in `𝒟_n`, averaged), Step 4 (`thm_main_moreover_of`).

The named hypotheses `H1` (Dobrushin) and `H2` (the plus state) are explicit arguments.
-/
import UndecidablePhaseDiagram.Hypotheses
import UndecidablePhaseDiagram.Payload.EdgeSums
import UndecidablePhaseDiagram.Payload.Effective
import UndecidablePhaseDiagram.Proof.Steps
import UndecidablePhaseDiagram.Proof.Main2
import UndecidablePhaseDiagram.Compiler.Universal

set_option autoImplicit false

noncomputable section

namespace UPD

open MeasureTheory

/-- The edge sums of `pay:sum` for every typical phase (`Payload/EdgeSums.lean`), in the form
that `pay:effective` takes. -/
theorem zfHyp (U : Machine) (β : ℝ) : ∀ τ, Scaffold.Typical τ → BG.ZfHyp U τ β := fun _ hτ =>
  ⟨BG.Zf_site β, fun _ hr => BG.Zf_nonready β hr, fun _ hr => BG.Zf_ready hτ β hr⟩

/-- `thm:main`(i): if `U` does not halt on `n`, then for `β ∈ J_n`, `βΦ` has exactly one
translation-invariant Gibbs measure. -/
theorem thm_main_i (h1 : H1) (U : Machine) {n : ℕ} (hn : 1 ≤ n) {β : ℝ} (hβ : β ∈ J n)
    (hh : ¬ U.HaltsOn n) : ∃! μ : Measure (Config (SiteVal U)), IsTIGibbs U β μ :=
  BG.thm_main_i_of h1 (fun τ => BG.liftCfg U τ β) (BG.hEff_of (zfHyp U β)) hn hβ hh

/-- `thm:main`(ii): if `U` halts on `n`, then for `β ∈ J_n`, `βΦ` has at least two
translation-invariant Gibbs measures. (`H1` is not used.) -/
theorem thm_main_ii (_h1 : H1) (h2 : H2) (U : Machine) {n : ℕ} (hn : 1 ≤ n) {β : ℝ}
    (hβ : β ∈ J n) (hh : U.HaltsOn n) : ∃ μ₁ μ₂ : Measure (Config (SiteVal U)),
      μ₁ ≠ μ₂ ∧ IsTIGibbs U β μ₁ ∧ IsTIGibbs U β μ₂ :=
  BG.thm_main_ii_of h2 (fun τ => BG.liftCfg U τ β) (BG.hEff_of (zfHyp U β)) BG.hS_of hn hβ hh

/-- `thm:main`, "Moreover": for every `β > 0`, `βΦ` has uncountably many Gibbs measures that are
not translation invariant. -/
theorem thm_main_moreover (U : Machine) {β : ℝ} (hβ : 0 < β) :
    ¬ {μ : Measure (Config (SiteVal U)) |
        IsGibbs β (Phi U) μ ∧ ¬ IsTranslationInvariantMeasure μ}.Countable :=
  BG.thm_main_moreover_of (fun τ => BG.liftCfg U τ β) (BG.hEff_of (zfHyp U β)) hβ

/-- Section 2.2: a universal machine exists (`Compiler/Universal.lean`: `univMachine`, the fold of
a `TM0` machine compiled by Mathlib from a universal code onto a one-sided tape with unary input;
`univMachine_universal`, from Mathlib's halting problem). -/
theorem exists_universal : ExistsUniversal :=
  ⟨Compiler.univMachine, Compiler.univMachine_universal⟩

end UPD

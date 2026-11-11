/-
# `cor:undecidable` from `thm:main`

The proof of Corollary B printed after `thm:main`: "The numbers `β_n` are rational and computable
from `n` by their defining finite sum, and `β_n ∈ J_n`. By `thm:main`, `β_n ∈ 𝒰` exactly when
`n ∉ ℋ_U`. An algorithm deciding `𝒰` would decide `ℋ_U`."

* `lamTriple`: `λ_K = p/q` and `3^{2K+1}` by one primitive recursion (`lamTriple_spec`);
  `betaPair n = (n p, q)` presents `β_n` (`betaPair_spec`) and is primitive recursive
  (`primrec_betaPair`).
* `corollaryB_of_main`: the conclusion of `CorollaryB` for a universal `U`, from the dichotomy of
  `thm:main` (parts (i) and (ii)) for that `U`.
-/
import UndecidablePhaseDiagram.Proof.Windows
import Mathlib.Computability.Halting

set_option autoImplicit false

noncomputable section

namespace UPD

/-! ## A computable presentation of `β_n` -/

/-- One step of the recursion: from `(p, q, t)` with `λ_K = p/q`, `t = 3^{2K+1}`, to the same for
`K + 1` (`λ_{K+1} = λ_K + 2/((2K+1) t)`). -/
def lamStep (K : ℕ) (r : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  (r.1 * ((2 * K + 1) * r.2.2) + 2 * r.2.1, r.2.1 * ((2 * K + 1) * r.2.2), 9 * r.2.2)

/-- `lamTriple K = (p, q, 3^{2K+1})` with `λ_K = p / q`. -/
def lamTriple (K : ℕ) : ℕ × ℕ × ℕ := Nat.rec (0, 1, 3) lamStep K

theorem lamTriple_zero : lamTriple 0 = (0, 1, 3) := rfl

theorem lamTriple_succ (K : ℕ) : lamTriple (K + 1) = lamStep K (lamTriple K) := rfl

theorem lamTriple_spec (K : ℕ) :
    0 < (lamTriple K).2.1 ∧ (lamTriple K).2.2 = 3 ^ (2 * K + 1) ∧
      ((lamTriple K).1 : ℚ) / (lamTriple K).2.1 = lam K := by
  induction K with
  | zero => simp [lamTriple_zero, lam]
  | succ K ih =>
    obtain ⟨hq, ht, hl⟩ := ih
    rw [lamTriple_succ]
    simp only [lamStep]
    set p := (lamTriple K).1
    set q := (lamTriple K).2.1
    have hd : 0 < (2 * K + 1) * 3 ^ (2 * K + 1) := by positivity
    refine ⟨Nat.mul_pos hq (by rw [ht]; exact hd), ?_, ?_⟩
    · rw [ht, show 2 * (K + 1) + 1 = 2 * K + 1 + 2 by ring, pow_add]; ring
    · rw [lam_succ, ← hl, ht]
      unfold lamTerm
      have hq' : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
      push_cast
      field_simp

/-- `β_n = (n p) / q` with `λ_{n+3} = p / q`. -/
def betaPair (n : ℕ) : ℕ × ℕ := (n * (lamTriple (n + 3)).1, (lamTriple (n + 3)).2.1)

theorem betaPair_spec (n : ℕ) :
    0 < (betaPair n).2 ∧ ((betaPair n).1 : ℚ) / (betaPair n).2 = betaN n := by
  obtain ⟨hq, -, hl⟩ := lamTriple_spec (n + 3)
  refine ⟨hq, ?_⟩
  simp only [betaPair, betaN]
  push_cast
  rw [mul_div_assoc, hl]

theorem primrec_lamTriple : Primrec lamTriple := by
  have hK : Primrec fun p : ℕ × (ℕ × ℕ × ℕ) => p.1 := Primrec.fst
  have hp : Primrec fun p : ℕ × (ℕ × ℕ × ℕ) => p.2.1 := Primrec.fst.comp Primrec.snd
  have hq : Primrec fun p : ℕ × (ℕ × ℕ × ℕ) => p.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have ht : Primrec fun p : ℕ × (ℕ × ℕ × ℕ) => p.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hd : Primrec fun p : ℕ × (ℕ × ℕ × ℕ) => (2 * p.1 + 1) * p.2.2.2 :=
    Primrec.nat_mul.comp
      (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) hK) (Primrec.const 1)) ht
  have hstep : Primrec₂ lamStep :=
    Primrec.pair
      (Primrec.nat_add.comp (Primrec.nat_mul.comp hp hd) (Primrec.nat_mul.comp (Primrec.const 2) hq))
      (Primrec.pair (Primrec.nat_mul.comp hq hd) (Primrec.nat_mul.comp (Primrec.const 9) ht))
  exact Primrec.nat_rec₁ (0, 1, 3) hstep

theorem primrec_betaPair : Primrec betaPair := by
  have h3 : Primrec fun n : ℕ => lamTriple (n + 3) :=
    primrec_lamTriple.comp (Primrec.nat_add.comp Primrec.id (Primrec.const 3))
  exact Primrec.pair (Primrec.nat_mul.comp Primrec.id (Primrec.fst.comp h3))
    (Primrec.fst.comp (Primrec.snd.comp h3))

/-! ## The reduction -/

/-- `β_n ∈ 𝒰` iff `U` does not halt on `n`, from the dichotomy of `thm:main`. -/
theorem betaN_mem_unique_iff (U : Machine)
    (hmain : ∀ n : ℕ, 1 ≤ n → ∀ β ∈ J n,
      (¬ U.HaltsOn n → ∃! μ : MeasureTheory.Measure (Config (SiteVal U)), IsTIGibbs U β μ) ∧
      (U.HaltsOn n → ∃ μ₁ μ₂ : MeasureTheory.Measure (Config (SiteVal U)),
        μ₁ ≠ μ₂ ∧ IsTIGibbs U β μ₁ ∧ IsTIGibbs U β μ₂))
    {n : ℕ} (hn : 1 ≤ n) : betaN n ∈ UniqueSet U ↔ ¬ U.HaltsOn n := by
  have hmem := betaN_mem_J n
  constructor
  · rintro ⟨-, μ, hμ, huniq⟩ hh
    obtain ⟨μ₁, μ₂, hne, h1, h2⟩ := (hmain n hn _ hmem).2 hh
    exact hne ((huniq μ₁ h1).trans (huniq μ₂ h2).symm)
  · intro hh
    refine ⟨?_, (hmain n hn _ hmem).1 hh⟩
    have h := betaN_sub_pos hn
    have : (0 : ℝ) < betaN n := by linarith
    exact_mod_cast this

/-- **`cor:undecidable` from `thm:main`.** For a universal `U`, the dichotomy of `thm:main` gives
the three claims of Corollary B. -/
theorem corollaryB_of_main (U : Machine) (hU : Universal U)
    (hmain : ∀ n : ℕ, 1 ≤ n → ∀ β ∈ J n,
      (¬ U.HaltsOn n → ∃! μ : MeasureTheory.Measure (Config (SiteVal U)), IsTIGibbs U β μ) ∧
      (U.HaltsOn n → ∃ μ₁ μ₂ : MeasureTheory.Measure (Config (SiteVal U)),
        μ₁ ≠ μ₂ ∧ IsTIGibbs U β μ₁ ∧ IsTIGibbs U β μ₂)) :
    ¬ ComputablePred (fun p : ℕ × ℕ => 0 < p.2 ∧ ((p.1 : ℚ) / p.2) ∈ UniqueSet U) ∧
    (∃ f : ℕ → ℕ × ℕ, Computable f ∧ ∀ n, 0 < (f n).2 ∧ ((f n).1 : ℚ) / (f n).2 = betaN n) ∧
    ∀ n : ℕ, 1 ≤ n → (betaN n ∈ UniqueSet U ↔ ¬ U.HaltsOn n) := by
  refine ⟨?_, ⟨betaPair, primrec_betaPair.to_comp, betaPair_spec⟩,
    fun n hn => betaN_mem_unique_iff U hmain hn⟩
  intro hc
  obtain ⟨g, hg, hgeq⟩ := ComputablePred.computable_iff.1 hc
  apply hU
  have hle : Computable fun n : ℕ => decide (1 ≤ n) :=
    (Primrec.nat_le.decide.comp (Primrec.const 1) Primrec.id).to_comp
  have hng : Computable fun n : ℕ => !(g (betaPair n)) :=
    Primrec.not.to_comp.comp (hg.comp primrec_betaPair.to_comp)
  refine ComputablePred.computable_iff.2
    ⟨fun n => decide (1 ≤ n) && !(g (betaPair n)), Primrec.and.to_comp.comp hle hng, ?_⟩
  funext n
  apply propext
  have hP : (0 < (betaPair n).2 ∧ (((betaPair n).1 : ℚ) / (betaPair n).2) ∈ UniqueSet U) ↔
      g (betaPair n) = true := by
    have := congrFun hgeq (betaPair n)
    rw [this]
  obtain ⟨hpos, heq⟩ := betaPair_spec n
  rw [heq] at hP
  by_cases hn : 1 ≤ n
  · have hiff := betaN_mem_unique_iff U hmain hn
    simp only [hn, decide_true, Bool.true_and, Bool.not_eq_true', true_and]
    constructor
    · intro hh
      by_contra hg'
      have hg'' : g (betaPair n) = true := by simpa using hg'
      exact (hiff.1 (hP.2 hg'').2) hh
    · intro hg'
      by_contra hh
      have := (hP.1 ⟨hpos, hiff.2 hh⟩)
      rw [hg'] at this
      exact Bool.false_ne_true this
  · simp [hn]

end UPD

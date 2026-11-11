/-
# Section 3.1: legal patterns of a Wang set

Ported from the forgetting core (`C:/Infanox/fixed-noise-ergodicity-lean`,
`FixedNoiseErgodicity/Section2/Compact.lean`, legal-pattern part; same authors), namespace
`FNE` → `UPD.Scaffold`.

* `LegalOn H V U p`: a pattern `p` is legal on `U` for matching relations `H` (direction `e₁`) and
  `V` (direction `e₂`) (Section 3, "Wang sets"). The relations are parameters, so the same notion
  serves the letters of `𝔸` and the quarters of `𝔸^q`, whose matching is defined by colours.
  **[choice] (proof side)** Patterns are total maps `ℤ² → α`; a pattern on `U` is such a map read
  on `U` only (`LegalOn.congr`).
* Restrictions, translates and images of legal patterns are legal; the square `a + [0, m)²`.
-/
import UndecidablePhaseDiagram.Statements

set_option autoImplicit false

namespace UPD.Scaffold

section Legal

variable {α β : Type*}

/-- Section 3 ("Wang sets"). A pattern `p` is *legal on `U`* (for the matching relations `H` in
direction `e₁` and `V` in direction `e₂`) if `H (p u) (p (u + e₁))` whenever `u, u + e₁ ∈ U`, and
`V (p u) (p (u + e₂))` whenever `u, u + e₂ ∈ U`. -/
def LegalOn (H V : α → α → Prop) (U : Set Plane) (p : Plane → α) : Prop :=
  (∀ u, u ∈ U → u + (1, 0) ∈ U → H (p u) (p (u + (1, 0)))) ∧
  (∀ u, u ∈ U → u + (0, 1) ∈ U → V (p u) (p (u + (0, 1))))

variable {H V : α → α → Prop} {U U' : Set Plane} {p q : Plane → α}

/-- Restrictions of legal patterns are legal. -/
theorem LegalOn.mono (h : LegalOn H V U p) (hU : U' ⊆ U) : LegalOn H V U' p :=
  ⟨fun u hu hu' => h.1 u (hU hu) (hU hu'), fun u hu hu' => h.2 u (hU hu) (hU hu')⟩

/-- Legality on `U` depends only on the values on `U`. -/
theorem LegalOn.congr (h : LegalOn H V U p) (hpq : ∀ u ∈ U, p u = q u) : LegalOn H V U q := by
  refine ⟨fun u hu hu' => ?_, fun u hu hu' => ?_⟩
  · rw [← hpq u hu, ← hpq _ hu']; exact h.1 u hu hu'
  · rw [← hpq u hu, ← hpq _ hu']; exact h.2 u hu hu'

/-- Translates of legal patterns are legal: `u ↦ p (u + a)` is legal on `U - a`. -/
theorem LegalOn.translate (h : LegalOn H V U p) (a : Plane) :
    LegalOn H V {u | u + a ∈ U} (fun u => p (u + a)) := by
  refine ⟨fun u hu hu' => ?_, fun u hu hu' => ?_⟩
  · have e : u + (1, 0) + a = u + a + (1, 0) := add_right_comm _ _ _
    simp only [Set.mem_setOf_eq, e] at hu' ⊢
    exact h.1 _ hu hu'
  · have e : u + (0, 1) + a = u + a + (0, 1) := add_right_comm _ _ _
    simp only [Set.mem_setOf_eq, e] at hu' ⊢
    exact h.2 _ hu hu'

/-- A map that respects the matching relations sends legal patterns to legal patterns. -/
theorem LegalOn.map {H' V' : β → β → Prop} (f : α → β) (hH : ∀ a b, H a b → H' (f a) (f b))
    (hV : ∀ a b, V a b → V' (f a) (f b)) (h : LegalOn H V U p) : LegalOn H' V' U (f ∘ p) :=
  ⟨fun u hu hu' => hH _ _ (h.1 u hu hu'), fun u hu hu' => hV _ _ (h.2 u hu hu')⟩

/-- On all of `ℤ²`: every edge matches. -/
theorem legalOn_univ_iff : LegalOn H V Set.univ p ↔
    (∀ u, H (p u) (p (u + (1, 0)))) ∧ ∀ u, V (p u) (p (u + (0, 1))) := by
  simp [LegalOn]

end Legal

/-- The square `a + [0, m)²` of side `m`. -/
def square (a : Plane) (m : ℕ) : Set Plane :=
  {u | a.1 ≤ u.1 ∧ u.1 < a.1 + m ∧ a.2 ≤ u.2 ∧ u.2 < a.2 + m}

theorem square_mono {a : Plane} {m m' : ℕ} (h : m ≤ m') : square a m ⊆ square a m' := by
  intro u hu
  simp only [square, Set.mem_setOf_eq] at hu ⊢
  omega

end UPD.Scaffold

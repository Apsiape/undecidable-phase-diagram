/-
# Elementary facts about the interaction `Φ` (`int:def-phi` and the remarks after it)

`Φ` evaluated on single sites and on horizontal and vertical pairs (`Phi_singleton`,
`Phi_pairH`, `Phi_pairV`, `Phi_other`); then the four properties that Theorem A lists after the
proof of `thm:main`: `Φ_A(ω)` depends only on `ω_A` (`phi_isInteraction`), `Φ` is translation
invariant (`phi_translationInvariant`) and nearest-neighbour (`phi_nearestNeighbour`), and its
values lie in `{0, 1, +∞}` (`phi_values`).
-/
import UndecidablePhaseDiagram.Statements

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace UPD

variable {U : Machine}

/-! ## Finite sets of one or two sites -/

theorem e1_ne_zero : e1 ≠ 0 := by simp [e1, Prod.ext_iff]

theorem e2_ne_zero : e2 ≠ 0 := by simp [e2, Prod.ext_iff]

/-- A pair `{ξ, ξ + d}`, `d ≠ 0`, is not a singleton. -/
theorem pair_ne_singleton {ξ ζ d : Plane} (hd : d ≠ 0) :
    ({ξ, ξ + d} : Finset Plane) ≠ {ζ} := by
  intro h
  have h1 : ξ ∈ ({ζ} : Finset Plane) := h ▸ Finset.mem_insert_self _ _
  have h2 : ξ + d ∈ ({ζ} : Finset Plane) :=
    h ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  rw [Finset.mem_singleton] at h1 h2
  exact hd (by rw [← h1] at h2; simpa using h2)

/-- Membership in a pair, coordinatewise. -/
theorem mem_pair_iff {x ξ d : Plane} :
    x ∈ ({ξ, ξ + d} : Finset Plane) ↔ (x.1 = ξ.1 ∧ x.2 = ξ.2) ∨
      (x.1 = ξ.1 + d.1 ∧ x.2 = ξ.2 + d.2) := by
  simp [Prod.ext_iff]

/-- `{ξ, ξ + e_i} = {ζ, ζ + e_j}` forces `i = j` and `ξ = ζ`; here the three cases used. -/
theorem pairH_inj {ξ ζ : Plane} (h : ({ξ, ξ + e1} : Finset Plane) = {ζ, ζ + e1}) : ξ = ζ := by
  have h1 : ξ ∈ ({ζ, ζ + e1} : Finset Plane) := h ▸ Finset.mem_insert_self _ _
  have h2 : ζ ∈ ({ξ, ξ + e1} : Finset Plane) := h.symm ▸ Finset.mem_insert_self _ _
  rw [mem_pair_iff] at h1 h2
  simp only [e1] at h1 h2
  ext <;> omega

theorem pairV_inj {ξ ζ : Plane} (h : ({ξ, ξ + e2} : Finset Plane) = {ζ, ζ + e2}) : ξ = ζ := by
  have h1 : ξ ∈ ({ζ, ζ + e2} : Finset Plane) := h ▸ Finset.mem_insert_self _ _
  have h2 : ζ ∈ ({ξ, ξ + e2} : Finset Plane) := h.symm ▸ Finset.mem_insert_self _ _
  rw [mem_pair_iff] at h1 h2
  simp only [e2] at h1 h2
  ext <;> omega

theorem pairV_ne_pairH {ξ ζ : Plane} : ({ξ, ξ + e2} : Finset Plane) ≠ {ζ, ζ + e1} := by
  intro h
  have h1 : ξ ∈ ({ζ, ζ + e1} : Finset Plane) := h ▸ Finset.mem_insert_self _ _
  have h2 : ξ + e2 ∈ ({ζ, ζ + e1} : Finset Plane) :=
    h ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  rw [mem_pair_iff] at h1 h2
  simp only [e1, e2, Prod.fst_add, Prod.snd_add] at h1 h2
  omega

/-! ## `Φ` on single sites and pairs -/

theorem Phi_singleton (ξ : Plane) (ω : Config (SiteVal U)) :
    Phi U {ξ} ω = siteEnergy (ω ξ) := by
  have h : ∃ ζ : Plane, ({ξ} : Finset Plane) = {ζ} := ⟨ξ, rfl⟩
  have hc : h.choose = ξ := (Finset.singleton_inj.1 h.choose_spec).symm
  unfold Phi
  rw [dif_pos h, hc]

theorem Phi_pairH (ξ : Plane) (ω : Config (SiteVal U)) :
    Phi U {ξ, ξ + e1} ω = edgeEnergyH (ω ξ) (ω (ξ + e1)) := by
  have h0 : ¬ ∃ ζ : Plane, ({ξ, ξ + e1} : Finset Plane) = {ζ} :=
    fun ⟨_, h⟩ => pair_ne_singleton e1_ne_zero h
  have h : ∃ ζ : Plane, ({ξ, ξ + e1} : Finset Plane) = {ζ, ζ + e1} := ⟨ξ, rfl⟩
  have hc : h.choose = ξ := (pairH_inj h.choose_spec).symm
  unfold Phi
  rw [dif_neg h0, dif_pos h, hc]

theorem Phi_pairV (ξ : Plane) (ω : Config (SiteVal U)) :
    Phi U {ξ, ξ + e2} ω = edgeEnergyV (ω ξ) (ω (ξ + e2)) := by
  have h0 : ¬ ∃ ζ : Plane, ({ξ, ξ + e2} : Finset Plane) = {ζ} :=
    fun ⟨_, h⟩ => pair_ne_singleton e2_ne_zero h
  have h1 : ¬ ∃ ζ : Plane, ({ξ, ξ + e2} : Finset Plane) = {ζ, ζ + e1} :=
    fun ⟨_, h⟩ => pairV_ne_pairH h
  have h : ∃ ζ : Plane, ({ξ, ξ + e2} : Finset Plane) = {ζ, ζ + e2} := ⟨ξ, rfl⟩
  have hc : h.choose = ξ := (pairV_inj h.choose_spec).symm
  unfold Phi
  rw [dif_neg h0, dif_neg h1, dif_pos h, hc]

theorem Phi_other {A : Finset Plane} (h0 : ¬ ∃ ξ, A = {ξ}) (h1 : ¬ ∃ ξ, A = {ξ, ξ + e1})
    (h2 : ¬ ∃ ξ, A = {ξ, ξ + e2}) (ω : Config (SiteVal U)) : Phi U A ω = 0 := by
  unfold Phi
  rw [dif_neg h0, dif_neg h1, dif_neg h2]

/-! ## The four properties -/

/-- `Φ` is nearest-neighbour. -/
theorem phi_nearestNeighbour : IsNearestNeighbour (Phi U) :=
  fun _ h0 h1 h2 ω => Phi_other h0 h1 h2 ω

/-- `Φ_A(ω)` depends only on `ω_A`. -/
theorem phi_isInteraction : IsInteraction (Phi U) := by
  intro A ω ω' hA
  by_cases h0 : ∃ ξ, A = {ξ}
  · obtain ⟨ξ, rfl⟩ := h0
    rw [Phi_singleton, Phi_singleton, hA ξ (Finset.mem_singleton_self _)]
  by_cases h1 : ∃ ξ, A = {ξ, ξ + e1}
  · obtain ⟨ξ, rfl⟩ := h1
    rw [Phi_pairH, Phi_pairH, hA ξ (Finset.mem_insert_self _ _),
      hA (ξ + e1) (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))]
  by_cases h2 : ∃ ξ, A = {ξ, ξ + e2}
  · obtain ⟨ξ, rfl⟩ := h2
    rw [Phi_pairV, Phi_pairV, hA ξ (Finset.mem_insert_self _ _),
      hA (ξ + e2) (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))]
  rw [Phi_other h0 h1 h2, Phi_other h0 h1 h2]

theorem image_add_singleton (ξ a : Plane) :
    ({ξ} : Finset Plane).image (fun x => x + a) = {ξ + a} := Finset.image_singleton _ _

theorem image_add_pair (ξ d a : Plane) :
    ({ξ, ξ + d} : Finset Plane).image (fun x => x + a) = {ξ + a, ξ + a + d} := by
  rw [Finset.image_insert, Finset.image_singleton, add_right_comm]

/-- Translating back: `A.image (· + a)` has one of the three shapes iff `A` has it. -/
theorem image_add_injective (a : Plane) :
    Function.Injective (fun A : Finset Plane => A.image (fun x => x + a)) :=
  fun _ _ h => Finset.image_injective (add_left_injective a) h

theorem shape_of_image {A : Finset Plane} {a : Plane} {d : Option Plane}
    (h : ∃ ζ, A.image (fun x => x + a) = (match d with | none => {ζ} | some d => {ζ, ζ + d})) :
    ∃ ξ, A = (match d with | none => {ξ} | some d => {ξ, ξ + d}) := by
  obtain ⟨ζ, hζ⟩ := h
  refine ⟨ζ - a, image_add_injective a ?_⟩
  cases d with
  | none => simp only at hζ ⊢; rw [hζ, image_add_singleton, sub_add_cancel]
  | some d => simp only at hζ ⊢; rw [hζ, image_add_pair, sub_add_cancel]

/-- `Φ` is translation invariant: `Φ_{A+a}(T_a ω) = Φ_A(ω)`. -/
theorem phi_translationInvariant : IsTranslationInvariant (Phi U) := by
  intro A a ω
  have hs : ∀ ξ, shift a ω (ξ + a) = ω ξ := fun ξ => by simp [shift]
  by_cases h0 : ∃ ξ, A = {ξ}
  · obtain ⟨ξ, rfl⟩ := h0
    rw [image_add_singleton, Phi_singleton, Phi_singleton, hs]
  by_cases h1 : ∃ ξ, A = {ξ, ξ + e1}
  · obtain ⟨ξ, rfl⟩ := h1
    rw [image_add_pair, Phi_pairH, Phi_pairH, hs, add_right_comm, hs]
  by_cases h2 : ∃ ξ, A = {ξ, ξ + e2}
  · obtain ⟨ξ, rfl⟩ := h2
    rw [image_add_pair, Phi_pairV, Phi_pairV, hs, add_right_comm, hs]
  have h0' : ¬ ∃ ζ, A.image (fun x => x + a) = {ζ} :=
    fun h => h0 (shape_of_image (d := none) h)
  have h1' : ¬ ∃ ζ, A.image (fun x => x + a) = {ζ, ζ + e1} :=
    fun h => h1 (shape_of_image (d := some e1) h)
  have h2' : ¬ ∃ ζ, A.image (fun x => x + a) = {ζ, ζ + e2} :=
    fun h => h2 (shape_of_image (d := some e2) h)
  rw [Phi_other h0 h1 h2, Phi_other h0' h1' h2']

/-- `int:sub-charge`: the charge is `0` or `1`. -/
theorem charge_le_one (s : SiteVal U) : s.charge = 0 ∨ s.charge = 1 := by
  unfold SiteVal.charge
  split
  · split
    · split <;> simp
    · simp
  · simp

/-- The values of `Φ` lie in `{0, 1, +∞}`. -/
theorem phi_values (A : Finset Plane) (ω : Config (SiteVal U)) :
    Phi U A ω = 0 ∨ Phi U A ω = 1 ∨ Phi U A ω = ⊤ := by
  by_cases h0 : ∃ ξ, A = {ξ}
  · obtain ⟨ξ, rfl⟩ := h0
    rw [Phi_singleton]
    unfold siteEnergy
    split
    · rcases charge_le_one (ω ξ) with h | h <;> simp [h]
    · simp
  by_cases h1 : ∃ ξ, A = {ξ, ξ + e1}
  · obtain ⟨ξ, rfl⟩ := h1
    rw [Phi_pairH]
    unfold edgeEnergyH
    split <;> simp
  by_cases h2 : ∃ ξ, A = {ξ, ξ + e2}
  · obtain ⟨ξ, rfl⟩ := h2
    rw [Phi_pairV]
    unfold edgeEnergyV
    split <;> simp
  simp [Phi_other h0 h1 h2]

end UPD

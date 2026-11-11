/-
# Section 5.4: the kernel does not move the background (`lem:freeze`(a), first part)

New in this project. `lem:freeze`(a): "The kernel `γ_Λ(· | ω)` charges the legal configurations
that agree with `ω` off `Λ`. By `prop:background`(d) they have background `𝔟`, …"

* `legal_fill`: a configuration that agrees with a legal one off `Λ` and has finite energy on `Λ`
  is legal (ratio and support properties of the site system, `Gibbs/Hard.lean`).
* **`freeze_a`**: at `ω ∈ X_typ`, every configuration charged by `γ_Λ(· | ω)` has the background
  of `ω`. The product form `γ_Λ(· | ω) = δ_𝔟 ⊗ γ^𝔟_Λ(· | p)` needs the frozen kernel on payload
  configurations (BLUEPRINT G.5, for QB).
-/
import UndecidablePhaseDiagram.Background.Unique
import UndecidablePhaseDiagram.Gibbs.Hard

set_option autoImplicit false

namespace UPD.BG

variable {U : Machine}

/-- A configuration that agrees with a legal one off `Λ` and has finite energy on `Λ` is legal. -/
theorem legal_fill {ω : Config (SiteVal U)} (hω : IsLegal (Phi U) ω) {Λ : Finset Plane}
    {η : Config (SiteVal U)} (hagree : ∀ ξ, ξ ∉ Λ → η ξ = ω ξ)
    (hE : energy (Phi U) Λ η ≠ ⊤) : IsLegal (Phi U) η := by
  set ws := Gibbs.siteSystem 1 (Phi U) phi_isInteraction phi_nearestNeighbour
  rw [Gibbs.isLegal_iff 1 phi_isInteraction phi_nearestNeighbour]
  have hω' := (Gibbs.isLegal_iff 1 phi_isInteraction phi_nearestNeighbour ω).1 hω
  have hΛ : 0 < ws.W Λ η := Gibbs.boltzmann_pos (lt_top_iff_ne_top.2 hE)
  intro Δ
  have hr := ws.ratio Λ (Δ ∪ Λ) Finset.subset_union_right η ω hagree
  have h1 : 0 < ws.W (Δ ∪ Λ) η := by
    have h4 : 0 < ws.W (Δ ∪ Λ) η * ws.W Λ ω := by rw [hr]; exact mul_pos (hω' _) hΛ
    exact (mul_pos_iff_of_pos_right (hω' Λ)).1 h4
  rcases (ws.nonneg Δ η).lt_or_eq with h | h
  · exact h
  · exact absurd (ws.support Δ (Δ ∪ Λ) Finset.subset_union_left η h.symm) h1.ne'

/-- **`lem:freeze`(a)**, first part: for `ω ∈ X_typ` and finite `Λ`, the kernel `γ_Λ(· | ω)`
charges only configurations with the background of `ω` (they are legal and agree with `ω` off
`Λ`, so `prop:background`(d) applies). -/
theorem freeze_a {ω : Config (SiteVal U)} {τ : ℕ → Bool × Bool} (hs : Setting ω τ) (β : ℝ)
    (Λ : Finset Plane) (ζ : Λ → SiteVal U)
    (hpos : boltzmann β (energy (Phi U) Λ (fill ω Λ ζ)) ≠ 0) :
    bgOf (fill ω Λ ζ) = bgOf ω := by
  have hagree : ∀ ξ, ξ ∉ Λ → fill ω Λ ζ ξ = ω ξ := fun ξ h => by simp [fill, h]
  have hE : energy (Phi U) Λ (fill ω Λ ζ) ≠ ⊤ := fun h => hpos (by simp [boltzmann, h])
  exact background_rigid hs (legal_fill hs.legal hagree hE) Λ hagree

end UPD.BG

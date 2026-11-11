/-
# Section 6: the measure-level bridge to the payload coordinates

New in this project (session 9). QB's G.5 ruling reads "`μ^𝔟` is Gibbs for `γ^𝔟`" as "`μ^𝔟`, a
measure on `Config (SiteVal U)` concentrated on the background `𝔟`, is Gibbs for `βΦ`"; Section 6
works with the frozen weight system `frozenSystem β 𝔟` on the payload coordinates
`Coord = Plane × PFld` (`Payload/Coords.lean`). This file identifies the two notions.

* `toCoords ω` (the payload coordinates of `ω`) and `ofCoords 𝔟 c` (the configuration with
  background `𝔟` and payload coordinates `c`), both measurable; `ofCoords_toCoords`,
  `toCoords_ofCoords` (on the configurations where every frozen weight is positive).
* `frozen_pos`: every frozen weight is positive at the coordinates of a legal configuration with
  background `𝔟`; `legal_ofCoords`, `siteOK_of_pos`: conversely.
* `setting_of_bgOf`: a legal configuration with background `𝔟_τ`, `τ` typical, has quarter phase `τ`.
* **`frozen_isGibbs_map`**, **`isGibbs_map_ofCoords`** and **`frozen_bridge`**: for typical `τ`, a
  probability measure `μ` on `Config (SiteVal U)` is Gibbs for `βΦ` and concentrated on `𝔟_τ` iff
  its payload image `μ.map toCoords` is Gibbs for `frozenSystem β 𝔟_τ` and `μ` is recovered from it
  by `ofCoords 𝔟_τ`; every Gibbs measure `ν` of the frozen system arises so
  (`map_toCoords_map_ofCoords`). The proof is the transport lemma `isGibbs_map` with the kernels
  matched on blocks: `freeze_a_product` (`lem:freeze`(a)) on one side, `frozen_expect_block` on the
  other.
-/
import UndecidablePhaseDiagram.Payload.Coords
import UndecidablePhaseDiagram.Gibbs.Transport

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace UPD.BG

open UPD.Scaffold

variable {U : Machine}

instance : MeasurableSpace PV := ⊤

instance : DiscreteMeasurableSpace PV := ⟨fun _ => trivial⟩

/-! ## Coordinates of a configuration and back -/

/-- The payload coordinates of a configuration. -/
def toCoords (ω : Config (SiteVal U)) : Coord → PV := encodeC (payOf ω)

/-- The configuration with background `𝔟` and payload coordinates `c`. -/
def ofCoords (b : Plane → BgVal U) (c : Coord → PV) : Config (SiteVal U) := assemble b (decodeC c)

theorem measurable_toCoords : Measurable (toCoords (U := U)) := by
  refine Measurable.of_eval fun x => ?_
  exact (measurable_of_countable (fun s : SiteVal U => encode (payPart s) x.2)).comp
    (measurable_pi_apply x.1)

theorem measurable_ofCoords (b : Plane → BgVal U) : Measurable (ofCoords b) := by
  refine Measurable.of_eval fun ξ => ?_
  refine Gibbs.measurable_of_dependsOn (Finset.univ.image fun f : PFld => (ξ, f)) _
    fun c c' h => ?_
  exact assemble_congr b fun f => h _ (Finset.mem_image.2 ⟨f, Finset.mem_univ _, rfl⟩)

theorem ofCoords_toCoords (ω : Config (SiteVal U)) : ofCoords (bgOf ω) (toCoords ω) = ω :=
  assemble_split ω

theorem bgOf_ofCoords (b : Plane → BgVal U) (c : Coord → PV) : bgOf (ofCoords b c) = b :=
  funext fun _ => bgPart_merge _ _

/-- The payload of `(𝔟, p)` is `p` when `p` is compatible with `𝔟` at every site. -/
theorem payOf_assemble {b : Plane → BgVal U} {p : Plane → PayVal}
    (h : ∀ ξ, Compatible (b ξ) (p ξ)) : payOf (assemble b p) = p :=
  funext fun ξ => payPart_merge (h ξ)

/-- `γ^𝔟_Λ F` only evaluates `F` at the fillings compatible with `𝔟`. -/
theorem frozenApply_congr (β : ℝ) (b : Plane → BgVal U) (Λ : Finset Plane)
    {F F' : (Plane → PayVal) → ℝ} (p : Plane → PayVal)
    (h : ∀ π ∈ compatFill b Λ, F (fill p Λ π) = F' (fill p Λ π)) :
    frozenApply β b Λ F p = frozenApply β b Λ F' p := by
  unfold frozenApply
  congr 1
  exact Finset.sum_congr rfl fun π hπ => by rw [h π hπ]

/-- A filling compatible with `𝔟` of a payload compatible with `𝔟` is compatible with `𝔟`. -/
theorem compatible_fill {b : Plane → BgVal U} {p : Plane → PayVal}
    (hp : ∀ ξ, Compatible (b ξ) (p ξ)) {Λ : Finset Plane} {π : Λ → PayVal}
    (hπ : π ∈ compatFill b Λ) (ξ : Plane) : Compatible (b ξ) (fill p Λ π ξ) := by
  classical
  simp only [compatFill, Finset.mem_filter, Finset.mem_univ, true_and] at hπ
  by_cases hξ : ξ ∈ Λ
  · simp only [fill, dif_pos hξ]
    exact hπ ⟨ξ, hξ⟩
  · simp only [fill, dif_neg hξ]
    exact hp ξ

/-! ## Positivity of the weights -/

variable (β : ℝ)

/-- Every frozen weight is positive at the coordinates of a legal configuration with background
`𝔟`. -/
theorem frozen_pos {b : Plane → BgVal U} {ω : Config (SiteVal U)} (h : IsLegal (Phi U) ω)
    (hb : bgOf ω = b) (Λ : Finset Coord) : 0 < (frozenSystem β b).W Λ (toCoords ω) := by
  subst hb
  change 0 < frozenW β (bgOf ω) Λ (toCoords ω)
  unfold frozenW
  have e : assemble (bgOf ω) (decodeC (toCoords ω)) = ω := assemble_split ω
  rw [e]
  refine mul_pos ((Gibbs.isLegal_iff β phi_isInteraction phi_nearestNeighbour ω).1 h _) ?_
  refine Finset.prod_pos fun ξ _ => ?_
  have hok : siteOK (bgOf ω) (toCoords ω) ξ = 1 := by
    unfold siteOK siteOK'
    rw [if_pos (show (∀ f : PFld, f.ok (toCoords ω (ξ, f)) = true) ∧
      Compatible (bgOf ω ξ) (decode fun f => toCoords ω (ξ, f)) from
        ⟨fun f => encode_ok _ f, compatible_split (ω ξ)⟩)]
  rw [hok]
  exact one_pos

/-- Where every frozen weight is positive, every site has fields of the right kinds and a payload
compatible with `𝔟`. -/
theorem siteOK_of_pos {b : Plane → BgVal U} {c : Coord → PV}
    (h : ∀ Λ, 0 < (frozenSystem β b).W Λ c) (ξ : Plane) :
    (∀ f : PFld, f.ok (c (ξ, f)) = true) ∧ Compatible (b ξ) (decode fun f => c (ξ, f)) := by
  have hp := h {(ξ, PFld.spin)}
  change 0 < frozenW β b {(ξ, PFld.spin)} c at hp
  unfold frozenW at hp
  have hs : sitesOf ({(ξ, PFld.spin)} : Finset Coord) = {ξ} := by simp [sitesOf]
  rw [hs, Finset.prod_singleton] at hp
  unfold siteOK siteOK' at hp
  by_contra hc
  rw [if_neg hc, mul_zero] at hp
  exact lt_irrefl _ hp

theorem payOf_ofCoords {b : Plane → BgVal U} {c : Coord → PV}
    (h : ∀ Λ, 0 < (frozenSystem β b).W Λ c) : payOf (ofCoords b c) = decodeC c :=
  payOf_assemble fun ξ => (siteOK_of_pos β h ξ).2

theorem toCoords_ofCoords {b : Plane → BgVal U} {c : Coord → PV}
    (h : ∀ Λ, 0 < (frozenSystem β b).W Λ c) : toCoords (ofCoords b c) = c := by
  funext x
  obtain ⟨ξ, f⟩ := x
  show encode (payOf (ofCoords b c) ξ) f = c (ξ, f)
  rw [payOf_ofCoords β h]
  exact congrFun (encode_decode (siteOK_of_pos β h ξ).1) f

/-- Where every frozen weight is positive, `(𝔟, c)` is legal. -/
theorem legal_ofCoords {b : Plane → BgVal U} {c : Coord → PV}
    (h : ∀ Λ, 0 < (frozenSystem β b).W Λ c) : IsLegal (Phi U) (ofCoords b c) := by
  refine (Gibbs.isLegal_iff β phi_isInteraction phi_nearestNeighbour _).2 fun Λ => ?_
  have hp := h (block Λ)
  change 0 < frozenW β b (block Λ) c at hp
  unfold frozenW at hp
  rw [sitesOf_block] at hp
  show 0 < boltzmann β (energy (Phi U) Λ (ofCoords b c))
  rcases (Gibbs.boltzmann_nonneg β (energy (Phi U) Λ (assemble b (decodeC c)))).eq_or_lt
    with h0 | h0
  · rw [← h0, zero_mul] at hp
    exact absurd hp (lt_irrefl _)
  · exact h0

/-- A legal configuration with background `𝔟_τ`, `τ` typical, has quarter phase `τ`. -/
theorem setting_of_bgOf {τ : ℕ → Bool × Bool} (hτ : Typical τ) {ω : Config (SiteVal U)}
    (h : IsLegal (Phi U) ω) (hb : bgOf ω = bgMap U τ) : Setting ω τ := by
  have hq : (fun ξ => (ω ξ).q) = fun ξ => (cfg U τ (fun _ => Spin.plus) ξ).q :=
    funext fun ξ => congrArg BgVal.q (congrFun hb ξ)
  refine ⟨h, ?_, hτ⟩
  rw [hq]
  exact (cfg_setting (U := U) hτ fun _ => Spin.plus).phase

/-! ## The bridge -/

variable {τ : ℕ → Bool × Bool} (hτ : Typical τ)
include hτ

/-- **Measure-level bridge, forward.** The payload image of a Gibbs measure for `βΦ` concentrated
on the background `𝔟_τ` is a Gibbs measure of the frozen system `frozenSystem β 𝔟_τ`. -/
theorem frozen_isGibbs_map {μ : Measure (Config (SiteVal U))} (hμ : IsGibbs β (Phi U) μ)
    (hb : ∀ᵐ ω ∂μ, bgOf ω = bgMap U τ) :
    (frozenSystem β (bgMap U τ)).IsGibbs (μ.map toCoords) := by
  have hμ' := (Gibbs.isGibbs_iff β phi_isInteraction phi_nearestNeighbour μ).1 hμ
  refine Gibbs.HardWeightSystem.isGibbs_map _ _ measurable_toCoords
    (A := {ω | IsLegal (Phi U) ω ∧ bgOf ω = bgMap U τ}) ?_ ?_ hμ' ?_
  · rintro ω ⟨h1, h2⟩ Λ'
    exact frozen_pos β h1 h2 Λ'
  · intro Λ'
    refine ⟨block (sitesOf Λ'), fun x hx => mem_block.2 (Finset.mem_image_of_mem _ hx),
      sitesOf Λ', ?_⟩
    rintro ω ⟨h1, h2⟩ G
    have hs := setting_of_bgOf hτ h1 h2
    have hp : ∀ ξ, Compatible (bgMap U τ ξ) (payOf ω ξ) := fun ξ => by
      rw [← h2]; exact compatible_split (ω ξ)
    rw [← Gibbs.kernelApply_eq β phi_isInteraction phi_nearestNeighbour, freeze_a_product hs,
      show toCoords ω = encodeC (payOf ω) from rfl, frozen_expect_block, h2]
    refine frozenApply_congr β _ _ _ fun π hπ => ?_
    show G (encodeC (fill (payOf ω) (sitesOf Λ') π)) =
      G (encodeC (payOf (assemble (bgMap U τ) (fill (payOf ω) (sitesOf Λ') π))))
    rw [payOf_assemble (compatible_fill hp hπ)]
  · have hleg : ∀ᵐ ω ∂μ, IsLegal (Phi U) ω := hμ'.2.1.mono fun ω hω =>
      (Gibbs.isLegal_iff β phi_isInteraction phi_nearestNeighbour ω).2 hω
    filter_upwards [hleg, hb] with ω h1 h2 using ⟨h1, h2⟩

/-- **Measure-level bridge, backward.** For a Gibbs measure `ν` of the frozen system
`frozenSystem β 𝔟_τ`, the measure `ν.map (ofCoords 𝔟_τ)` is a Gibbs measure for `βΦ` concentrated
on the background `𝔟_τ`. -/
theorem isGibbs_map_ofCoords {ν : Measure (Coord → PV)}
    (hν : (frozenSystem β (bgMap U τ)).IsGibbs ν) :
    IsGibbs β (Phi U) (ν.map (ofCoords (bgMap U τ))) ∧
      ∀ᵐ ω ∂(ν.map (ofCoords (bgMap U τ))), bgOf ω = bgMap U τ := by
  have hm := measurable_ofCoords (bgMap U τ)
  refine ⟨(Gibbs.isGibbs_iff β phi_isInteraction phi_nearestNeighbour _).2 ?_, ?_⟩
  · refine Gibbs.HardWeightSystem.isGibbs_map _ _ hm
      (A := {c | ∀ Λ, 0 < (frozenSystem β (bgMap U τ)).W Λ c}) ?_ ?_ hν hν.2.1
    · intro c hc Λ'
      exact (Gibbs.isLegal_iff β phi_isInteraction phi_nearestNeighbour _).1
        (legal_ofCoords β hc) Λ'
    · intro Λ'
      refine ⟨Λ', Finset.Subset.refl _, block Λ', fun c hc G => ?_⟩
      have hs := setting_of_bgOf hτ (legal_ofCoords β hc) (bgOf_ofCoords _ c)
      rw [← Gibbs.kernelApply_eq β phi_isInteraction phi_nearestNeighbour, freeze_a_product hs,
        bgOf_ofCoords, payOf_ofCoords β hc]
      have hc' : c = encodeC (decodeC c) := by
        have := toCoords_ofCoords β hc
        rw [toCoords, payOf_ofCoords β hc] at this
        exact this.symm
      conv_rhs => rw [hc']
      rw [frozen_expect_block]
      rfl
  · rw [ae_map_iff hm.aemeasurable (show MeasurableSet {ω : Config (SiteVal U) |
      bgOf ω = bgMap U τ} from measurable_bgOf (measurableSet_singleton _))]
    exact ae_of_all _ fun c => bgOf_ofCoords _ c

omit hτ in
/-- Every Gibbs measure of the frozen system is the payload image of its configuration measure. -/
theorem map_toCoords_map_ofCoords {ν : Measure (Coord → PV)}
    (hν : (frozenSystem β (bgMap U τ)).IsGibbs ν) :
    (ν.map (ofCoords (bgMap U τ))).map toCoords = ν :=
  Gibbs.map_map_eq_self (measurable_ofCoords _) measurable_toCoords
    (hν.2.1.mono fun _ hc => toCoords_ofCoords β hc)

/-- **The measure-level bridge** (BLUEPRINT G.6, item 3): for typical `τ`, a measure `μ` on
`Config (SiteVal U)` is a Gibbs measure for `βΦ` concentrated on the background `𝔟_τ` iff its
payload image is a Gibbs measure of the frozen system `frozenSystem β 𝔟_τ` from which `μ` is
recovered by `ofCoords 𝔟_τ`. -/
theorem frozen_bridge (μ : Measure (Config (SiteVal U))) :
    (IsGibbs β (Phi U) μ ∧ ∀ᵐ ω ∂μ, bgOf ω = bgMap U τ) ↔
      (frozenSystem β (bgMap U τ)).IsGibbs (μ.map toCoords) ∧
        μ = (μ.map toCoords).map (ofCoords (bgMap U τ)) := by
  constructor
  · rintro ⟨hμ, hb⟩
    refine ⟨frozen_isGibbs_map β hτ hμ hb, ?_⟩
    refine (Gibbs.map_map_eq_self measurable_toCoords (measurable_ofCoords _) ?_).symm
    filter_upwards [hb] with ω hω
    rw [← hω]
    exact ofCoords_toCoords ω
  · rintro ⟨hν, he⟩
    rw [he]
    exact isGibbs_map_ofCoords β hτ hν

end UPD.BG

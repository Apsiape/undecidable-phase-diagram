/-
# Section 6: payload coordinates and the field-level bridge

New in this project. QB's ruling on BLUEPRINT G.5 (2): for Section 6 the payload coordinates are
`Plane × PFld` with one value type `PV` (seven values: two spins, three wire values, two bits) and
single-site hard factors fixing the kind of each coordinate; the frozen kernels of
`lem:freeze` become the kernels of a hard-constraint weight system on `Plane × PFld → PV`
(`Gibbs/Hard.lean`), so that `pay:elim` can be proved for a general hard weight system.

* `PFld` (the 21 payload fields of a site, `int:sub-split`), `PV`, `PFld.ok` (the kind of a
  field), `encode`/`decode` between payload values and field assignments (`decode_encode`,
  `encode_decode`), and `encodeC`/`decodeC` for configurations.
* `frozenSystem β 𝔟`: the frozen weight system on the payload coordinates: for a finite set `Λ`
  of coordinates with sites `sitesOf Λ`, the weight is `e^{-βH_{sitesOf Λ}(𝔟, p)}` times the
  indicators that the coordinates at these sites have their kinds and are compatible with `𝔟`;
  it is a `HardWeightSystem` (ratio and support properties from the site system).
* **`frozen_expect_block`** (the field-level bridge): for the block `block Λ` of all payload
  coordinates at the sites of a finite `Λ ⊆ ℤ²`, the kernel of `frozenSystem β 𝔟` is the frozen
  kernel `γ^𝔟_Λ` of `lem:freeze` (`frozenApply`).
-/
import UndecidablePhaseDiagram.Background.Conditioning

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace UPD.BG

open UPD.Scaffold

variable {U : Machine}

/-! ## Fields, values and kinds -/

/-- The payload fields of a site (`int:sub-split`): the spin, the four wire values, and the
components `x_ι`, `y_ι` of the cell record and `x_ι` of `ℓ^S`, `ℓ^N`. -/
inductive PFld where
  | spin
  | wW
  | wE
  | wS
  | wN
  | kx (ι : Fin 4)
  | ky (ι : Fin 4)
  | lSx (ι : Fin 4)
  | lNx (ι : Fin 4)
  deriving DecidableEq, Fintype

/-- One value type for all payload coordinates: a spin, a wire value (`none` is `□`) or a bit. -/
inductive PV where
  | sp (s : Spin)
  | wire (w : Option Spin)
  | bit (b : Bool)
  deriving DecidableEq, Fintype

/-- The kind of a field: a spin, a wire value or a bit. -/
def PFld.ok : PFld → PV → Bool
  | .spin, .sp _ => true
  | .wW, .wire _ => true
  | .wE, .wire _ => true
  | .wS, .wire _ => true
  | .wN, .wire _ => true
  | .kx _, .bit _ => true
  | .ky _, .bit _ => true
  | .lSx _, .bit _ => true
  | .lNx _, .bit _ => true
  | _, _ => false

/-- The spin of a value (`+1` for a value of another kind). -/
def PV.spinOf : PV → Spin
  | .sp s => s
  | _ => .plus

/-- The wire value of a value (`□` for a value of another kind). -/
def PV.wireOf : PV → Option Spin
  | .wire w => w
  | _ => none

/-- The bit of a value (`0` for a value of another kind). -/
def PV.bitOf : PV → Bool
  | .bit b => b
  | _ => false

theorem PV.sp_spinOf {v : PV} (h : PFld.spin.ok v = true) : PV.sp v.spinOf = v := by
  cases v <;> simp_all [PFld.ok, PV.spinOf]

theorem PV.wire_wireOf {v : PV} {f : PFld} (hf : f = .wW ∨ f = .wE ∨ f = .wS ∨ f = .wN)
    (h : f.ok v = true) : PV.wire v.wireOf = v := by
  rcases hf with rfl | rfl | rfl | rfl <;> cases v <;> simp_all [PFld.ok, PV.wireOf]

theorem PV.bit_bitOf {v : PV} {f : PFld} (hf : ∃ ι, f = .kx ι ∨ f = .ky ι ∨ f = .lSx ι ∨ f = .lNx ι)
    (h : f.ok v = true) : PV.bit v.bitOf = v := by
  obtain ⟨ι, hf⟩ := hf
  rcases hf with rfl | rfl | rfl | rfl <;> cases v <;> simp_all [PFld.ok, PV.bitOf]

/-- The field assignment of a payload value. -/
def encode (p : PayVal) : PFld → PV
  | .spin => .sp p.spin
  | .wW => .wire p.wW
  | .wE => .wire p.wE
  | .wS => .wire p.wS
  | .wN => .wire p.wN
  | .kx ι => .bit (p.kx ι)
  | .ky ι => .bit (p.ky ι)
  | .lSx ι => .bit (p.lSx ι)
  | .lNx ι => .bit (p.lNx ι)

/-- The payload value of a field assignment (values of the wrong kind read as defaults). -/
def decode (c : PFld → PV) : PayVal :=
  ⟨(c .spin).spinOf, (c .wW).wireOf, (c .wE).wireOf, (c .wS).wireOf, (c .wN).wireOf,
    fun ι => (c (.kx ι)).bitOf, fun ι => (c (.ky ι)).bitOf, fun ι => (c (.lSx ι)).bitOf,
    fun ι => (c (.lNx ι)).bitOf⟩

theorem decode_encode (p : PayVal) : decode (encode p) = p := rfl

theorem encode_ok (p : PayVal) (f : PFld) : f.ok (encode p f) = true := by
  cases f <;> rfl

theorem encode_decode {c : PFld → PV} (h : ∀ f : PFld, f.ok (c f) = true) : encode (decode c) = c := by
  funext f
  cases f with
  | spin => exact PV.sp_spinOf (h _)
  | wW => exact PV.wire_wireOf (Or.inl rfl) (h _)
  | wE => exact PV.wire_wireOf (Or.inr (Or.inl rfl)) (h _)
  | wS => exact PV.wire_wireOf (Or.inr (Or.inr (Or.inl rfl))) (h _)
  | wN => exact PV.wire_wireOf (Or.inr (Or.inr (Or.inr rfl))) (h _)
  | kx ι => exact PV.bit_bitOf ⟨ι, Or.inl rfl⟩ (h _)
  | ky ι => exact PV.bit_bitOf ⟨ι, Or.inr (Or.inl rfl)⟩ (h _)
  | lSx ι => exact PV.bit_bitOf ⟨ι, Or.inr (Or.inr (Or.inl rfl))⟩ (h _)
  | lNx ι => exact PV.bit_bitOf ⟨ι, Or.inr (Or.inr (Or.inr rfl))⟩ (h _)

/-! ## Coordinates -/

/-- A payload coordinate: a site and a field. -/
abbrev Coord := Plane × PFld

/-- The payload configuration of a coordinate configuration. -/
def decodeC (c : Coord → PV) : Plane → PayVal := fun ξ => decode fun f => c (ξ, f)

/-- The coordinate configuration of a payload configuration. -/
def encodeC (p : Plane → PayVal) : Coord → PV := fun x => encode (p x.1) x.2

theorem decodeC_encodeC (p : Plane → PayVal) : decodeC (encodeC p) = p := rfl

/-- The sites of a set of coordinates. -/
def sitesOf (Λ : Finset Coord) : Finset Plane := Λ.image Prod.fst

/-- All payload coordinates at the sites of `Λ`. -/
def block (Λ : Finset Plane) : Finset Coord := Λ ×ˢ Finset.univ

theorem sitesOf_block (Λ : Finset Plane) : sitesOf (block Λ) = Λ :=
  Finset.product_image_fst ⟨PFld.spin, Finset.mem_univ _⟩

/-! ## The frozen weight system -/

open Classical in
/-- The single-site hard factor of a field assignment `a` at a site with background value `bv`:
every field has its kind and the payload is compatible with `bv`. -/
def siteOK' (bv : BgVal U) (a : PFld → PV) : ℝ :=
  if (∀ f : PFld, f.ok (a f) = true) ∧ Compatible bv (decode a) then 1 else 0

/-- The single-site hard factor at `ξ`: the coordinates at `ξ` have their kinds and the payload is
compatible with the background `𝔟 ξ`. -/
def siteOK (b : Plane → BgVal U) (c : Coord → PV) (ξ : Plane) : ℝ :=
  siteOK' (b ξ) fun f => c (ξ, f)

/-- The weight of the frozen system for a finite set `Λ` of payload coordinates. -/
def frozenW (β : ℝ) (b : Plane → BgVal U) (Λ : Finset Coord) (c : Coord → PV) : ℝ :=
  boltzmann β (energy (Phi U) (sitesOf Λ) (assemble b (decodeC c))) *
    ∏ ξ ∈ sitesOf Λ, siteOK b c ξ

theorem siteOK_nonneg (b : Plane → BgVal U) (c : Coord → PV) (ξ : Plane) : 0 ≤ siteOK b c ξ := by
  unfold siteOK siteOK'; split_ifs <;> norm_num

theorem siteOK_congr (b : Plane → BgVal U) {c c' : Coord → PV} {ξ : Plane}
    (h : ∀ f, c (ξ, f) = c' (ξ, f)) : siteOK b c ξ = siteOK b c' ξ := by
  have e : (fun f => c (ξ, f)) = fun f => c' (ξ, f) := funext h
  unfold siteOK
  rw [e]

theorem assemble_congr (b : Plane → BgVal U) {c c' : Coord → PV} {ξ : Plane}
    (h : ∀ f, c (ξ, f) = c' (ξ, f)) : assemble b (decodeC c) ξ = assemble b (decodeC c') ξ := by
  have e : (fun f => c (ξ, f)) = fun f => c' (ξ, f) := funext h
  simp only [assemble, decodeC, e]

/-- **The frozen weight system** on the payload coordinates (BLUEPRINT G.5 (2)). -/
def frozenSystem (β : ℝ) (b : Plane → BgVal U) : Gibbs.HardWeightSystem Coord PV where
  W := frozenW β b
  nonneg Λ c := mul_nonneg (Gibbs.boltzmann_nonneg _ _)
    (Finset.prod_nonneg fun ξ _ => siteOK_nonneg b c ξ)
  range Λ := ((Gibbs.nnSets (sitesOf Λ)).biUnion id) ×ˢ Finset.univ
  isLocal Λ c c' h := by
    have hsite : ∀ ξ ∈ (Gibbs.nnSets (sitesOf Λ)).biUnion id, ∀ f, c (ξ, f) = c' (ξ, f) :=
      fun ξ hξ f => h (ξ, f) (Finset.mem_product.2 ⟨hξ, Finset.mem_univ _⟩)
    have hself : ∀ ξ ∈ sitesOf Λ, ξ ∈ (Gibbs.nnSets (sitesOf Λ)).biUnion id := by
      intro ξ hξ
      refine Finset.mem_biUnion.2 ⟨{ξ}, ?_, Finset.mem_singleton_self ξ⟩
      simp only [Gibbs.nnSets, Finset.mem_biUnion, Finset.mem_union, Finset.mem_insert,
        Finset.mem_singleton]
      exact ⟨ξ, Or.inl (Or.inl hξ), Or.inl rfl⟩
    have hB := (Gibbs.siteSystem β (Phi U) phi_isInteraction phi_nearestNeighbour).isLocal
      (sitesOf Λ) (assemble b (decodeC c)) (assemble b (decodeC c'))
      fun ξ hξ => assemble_congr b (hsite ξ hξ)
    show boltzmann β _ * _ = boltzmann β _ * _
    rw [show boltzmann β (energy (Phi U) (sitesOf Λ) (assemble b (decodeC c))) =
      boltzmann β (energy (Phi U) (sitesOf Λ) (assemble b (decodeC c'))) from hB]
    congr 1
    exact Finset.prod_congr rfl fun ξ hξ => siteOK_congr b (hsite ξ (hself ξ hξ))
  ratio Λ Δ hΛΔ c c' h := by
    classical
    have hs : sitesOf Λ ⊆ sitesOf Δ := Finset.image_subset_image hΛΔ
    have hoff : ∀ ξ, ξ ∉ sitesOf Λ → ∀ f, c (ξ, f) = c' (ξ, f) := fun ξ hξ f =>
      h (ξ, f) fun hm => hξ (Finset.mem_image.2 ⟨(ξ, f), hm, rfl⟩)
    have hB := (Gibbs.siteSystem β (Phi U) phi_isInteraction phi_nearestNeighbour).ratio
      (sitesOf Λ) (sitesOf Δ) hs (assemble b (decodeC c)) (assemble b (decodeC c'))
      fun ξ hξ => assemble_congr b (hoff ξ hξ)
    change boltzmann β (energy (Phi U) (sitesOf Δ) (assemble b (decodeC c))) *
      boltzmann β (energy (Phi U) (sitesOf Λ) (assemble b (decodeC c'))) =
      boltzmann β (energy (Phi U) (sitesOf Δ) (assemble b (decodeC c'))) *
      boltzmann β (energy (Phi U) (sitesOf Λ) (assemble b (decodeC c))) at hB
    have hR : ∏ ξ ∈ sitesOf Δ \ sitesOf Λ, siteOK b c ξ =
        ∏ ξ ∈ sitesOf Δ \ sitesOf Λ, siteOK b c' ξ :=
      Finset.prod_congr rfl fun ξ hξ => siteOK_congr b (hoff ξ (Finset.mem_sdiff.1 hξ).2)
    show frozenW β b Δ c * frozenW β b Λ c' = frozenW β b Δ c' * frozenW β b Λ c
    unfold frozenW
    rw [← Finset.prod_sdiff hs, ← Finset.prod_sdiff (f := siteOK b c') hs, hR]
    linear_combination (∏ ξ ∈ sitesOf Δ \ sitesOf Λ, siteOK b c' ξ) *
      (∏ ξ ∈ sitesOf Λ, siteOK b c ξ) * (∏ ξ ∈ sitesOf Λ, siteOK b c' ξ) * hB
  support Λ Δ hΛΔ c h0 := by
    have hs : sitesOf Λ ⊆ sitesOf Δ := Finset.image_subset_image hΛΔ
    change frozenW β b Λ c = 0 at h0
    show frozenW β b Δ c = 0
    unfold frozenW at h0 ⊢
    rcases mul_eq_zero.1 h0 with h | h
    · have := (Gibbs.siteSystem β (Phi U) phi_isInteraction phi_nearestNeighbour).support
        (sitesOf Λ) (sitesOf Δ) hs (assemble b (decodeC c)) h
      change boltzmann β (energy (Phi U) (sitesOf Δ) (assemble b (decodeC c))) = 0 at this
      rw [this, zero_mul]
    · obtain ⟨ξ, hξ, hz⟩ := Finset.prod_eq_zero_iff.1 h
      rw [Finset.prod_eq_zero (hs hξ) hz, mul_zero]

/-! ## The field-level bridge -/

section Bridge

theorem mem_block {Λ : Finset Plane} {x : Coord} : x ∈ block Λ ↔ x.1 ∈ Λ := by
  simp [block, Finset.mem_product]

/-- The field assignment at the site `x` of a filling of a block. -/
def rowOf {Λ : Finset Plane} (ζ : block Λ → PV) (x : Λ) : PFld → PV :=
  fun f => ζ ⟨(x.1, f), mem_block.2 x.2⟩

theorem fillOn_block_site {Λ : Finset Plane} (c : Coord → PV) (ζ : block Λ → PV) (x : Λ) :
    (fun f => Gibbs.fillOn c (block Λ) ζ (x.1, f)) = rowOf ζ x := by
  funext f
  rw [Gibbs.fillOn_of_mem c ζ (mem_block.2 x.2)]
  rfl

variable (β : ℝ) (b : Plane → BgVal U) (Λ : Finset Plane) (p : Plane → PayVal)

/-- The fillings of a block are reindexed by the payload fillings compatible with `𝔟` (the other
fillings have weight `0`). -/
theorem sum_block_eq (g : (Coord → PV) → ℝ) :
    ∑ ζ : block Λ → PV, frozenW β b (block Λ) (Gibbs.fillOn (encodeC p) (block Λ) ζ) *
        g (Gibbs.fillOn (encodeC p) (block Λ) ζ) =
      ∑ π ∈ compatFill b Λ, boltzmann β (energy (Phi U) Λ (assemble b (fill p Λ π))) *
        g (encodeC (fill p Λ π)) := by
  classical
  set Good : (block Λ → PV) → Prop := fun ζ =>
    ∀ x : Λ, (∀ f : PFld, f.ok (rowOf ζ x f) = true) ∧ Compatible (b x) (decode (rowOf ζ x))
  have hsite : ∀ (ζ : block Λ → PV) (x : Λ),
      siteOK b (Gibbs.fillOn (encodeC p) (block Λ) ζ) x = siteOK' (b x) (rowOf ζ x) := by
    intro ζ x
    unfold siteOK
    rw [fillOn_block_site]
  have hprod : ∀ ζ : block Λ → PV,
      ∏ ξ ∈ Λ, siteOK b (Gibbs.fillOn (encodeC p) (block Λ) ζ) ξ = if Good ζ then 1 else 0 := by
    intro ζ
    rw [← Finset.prod_attach]
    simp only [hsite]
    by_cases hg : Good ζ
    · rw [if_pos hg]
      exact Finset.prod_eq_one fun x _ => by unfold siteOK'; rw [if_pos (hg x)]
    · rw [if_neg hg]
      have hex : ∃ x : Λ, ¬ ((∀ f : PFld, f.ok (rowOf ζ x f) = true) ∧
          Compatible (b x) (decode (rowOf ζ x))) := by
        by_contra hc
        exact hg fun x => by by_contra hx; exact hc ⟨x, hx⟩
      obtain ⟨x, hx⟩ := hex
      refine Finset.prod_eq_zero (Finset.mem_attach _ x) ?_
      unfold siteOK'
      rw [if_neg hx]
  have hfill : ∀ ζ : block Λ → PV, Good ζ →
      Gibbs.fillOn (encodeC p) (block Λ) ζ = encodeC (fill p Λ fun x => decode (rowOf ζ x)) := by
    intro ζ hg
    funext y
    obtain ⟨ξ, f⟩ := y
    by_cases hξ : ξ ∈ Λ
    · rw [Gibbs.fillOn_of_mem _ ζ (mem_block.2 hξ)]
      simp only [encodeC, fill, dif_pos hξ]
      rw [encode_decode (hg ⟨ξ, hξ⟩).1]
      rfl
    · have hy : (ξ, f) ∉ block Λ := fun h => hξ (mem_block.1 h)
      simp only [Gibbs.fillOn, dif_neg hy, encodeC, fill, dif_neg hξ]
  unfold frozenW
  rw [sitesOf_block]
  simp only [hprod]
  rw [← Finset.sum_filter_of_ne (p := Good)]
  · refine Finset.sum_nbij' (fun ζ x => decode (rowOf ζ x))
      (fun π y => encode (π ⟨y.1.1, mem_block.1 y.2⟩) y.1.2) ?_ ?_ ?_ ?_ ?_
    · intro ζ hζ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hζ
      simp only [compatFill, Finset.mem_filter, Finset.mem_univ, true_and]
      exact fun x => (hζ x).2
    · intro π hπ
      simp only [compatFill, Finset.mem_filter, Finset.mem_univ, true_and] at hπ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro x
      have e : rowOf (fun y : block Λ => encode (π ⟨y.1.1, mem_block.1 y.2⟩) y.1.2) x =
          encode (π x) := rfl
      rw [e, decode_encode]
      exact ⟨encode_ok _, hπ x⟩
    · intro ζ hζ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hζ
      funext y
      obtain ⟨⟨ξ, f⟩, hy⟩ := y
      have := encode_decode (hζ ⟨ξ, mem_block.1 hy⟩).1
      exact congrFun this f
    · intro π _
      funext x
      exact decode_encode (π x)
    · intro ζ hζ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hζ
      rw [hfill ζ hζ, if_pos hζ, mul_one, decodeC_encodeC]
  · intro ζ _ hne
    by_contra hg
    rw [if_neg hg, mul_zero, zero_mul] at hne
    exact hne rfl

/-- **The field-level bridge**: the kernel of the frozen weight system for the block of all
payload coordinates at the sites of `Λ` is the frozen kernel `γ^𝔟_Λ` of `lem:freeze`. -/
theorem frozen_expect_block (G : (Coord → PV) → ℝ) :
    (frozenSystem β b).expect (block Λ) (encodeC p) G =
      frozenApply β b Λ (fun p' => G (encodeC p')) p := by
  unfold Gibbs.HardWeightSystem.expect Gibbs.HardWeightSystem.prob Gibbs.HardWeightSystem.Z
    frozenApply
  simp only [div_mul_eq_mul_div, ← Finset.sum_div]
  have h1 := sum_block_eq β b Λ p G
  have h2 := sum_block_eq β b Λ p (fun _ => 1)
  simp only [mul_one] at h2
  change (∑ ζ : block Λ → PV, frozenW β b (block Λ) (Gibbs.fillOn (encodeC p) (block Λ) ζ) *
      G (Gibbs.fillOn (encodeC p) (block Λ) ζ)) /
      ∑ ζ : block Λ → PV, frozenW β b (block Λ) (Gibbs.fillOn (encodeC p) (block Λ) ζ) = _
  rw [h1, h2]

end Bridge

end UPD.BG

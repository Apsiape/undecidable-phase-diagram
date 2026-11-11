/-
# The graph `Γ_τ` of `pay:effective`

New in this project (session 10). `pay:effective`: "Let `Γ_𝔟` be the graph with vertex set `ℤ²`
whose edges are the pairs `{𝐫_d(m₁, m₂), 𝐫_d(m₁ + 1, m₂)}` and `{𝐫_d(m₁, m₂), 𝐫_d(m₁, m₂ + 1)}` for
the ready depths `d`, with coupling `J_{n(d)}(β)` on the edges of depth `d`. [...] The graph `Γ_𝔟`
is a disjoint union of one square lattice for each ready depth and of isolated vertices."

The graph depends on the background only through its phase `τ` (the roots `𝐫_d(m₁, m₂)`,
`Background/Grids.lean`) and on the machine through the readiness `ρ_d` (`MachineM.ready`).

* `root_inj`: roots of different depths are different sites, and `m ↦ 𝐫_d(m)` is injective
  (`scf:frames`(d), `rfree_depth_unique`, `rfree_inj`);
* `rootData`: the data `(d, m₁, m₂)` of a ready root, `none` at other sites; the neighbours
  `gNbr` (the four roots `𝐫_d(m₁ ± 1, m₂)`, `𝐫_d(m₁, m₂ ± 1)` at a ready root, none elsewhere), the
  couplings `gJ` and the graph `Gamma` (`IsingGraph Plane`); `mem_Gamma_nbr`, `Gamma_J_root`,
  `Gamma_J_cases`, `card_Gamma_nbr_le`;
* for Step 3 of `thm:main`: the component map `depthOf` (`isComponentMap_depthOf`) and, for a
  ready depth `d ≥ 1`, the isomorphism `squareIso` from the square lattice with coupling
  `J_{n(d)}(β)` onto the component of depth `d`, `m ↦ 𝐫_d(m)`.
-/
import UndecidablePhaseDiagram.Background.Markers
import UndecidablePhaseDiagram.Background.Label
import UndecidablePhaseDiagram.Proof.Thermal
import UndecidablePhaseDiagram.Gibbs.Product
import UndecidablePhaseDiagram.Peierls.Lattice

set_option autoImplicit false

noncomputable section

namespace UPD.BG

open UPD.Scaffold

/-! ## Roots -/

/-- `scf:frames`(d) and `bg:markers`(b): a root determines its depth and its index. -/
theorem root_inj' {τ : ℕ → Bool × Bool} {d d' : ℕ} {m1 m2 m1' m2' : ℤ}
    (h : root τ d m1 m2 = root τ d' m1' m2') : d = d' ∧ m1 = m1' ∧ m2 = m2' := by
  have h1 : rfree (a1 τ) d m1 = rfree (a1 τ) d' m1' := congrArg Prod.fst h
  have h2 : rfree (a2 τ) d m2 = rfree (a2 τ) d' m2' := congrArg Prod.snd h
  obtain rfl : d = d' := rfree_depth_unique (frameOffsets_phase _) h1
  exact ⟨rfl, rfree_inj h1, rfree_inj h2⟩

/-- **`pay:effective`** ("roots of different depths are different sites"): the roots
`𝐫_d(m₁, m₂)`, `d ≥ 1`, are pairwise different. (The depth hypotheses are not needed; see
`root_inj'`.) -/
theorem root_inj {τ : ℕ → Bool × Bool} {d d' : ℕ} {m1 m2 m1' m2' : ℤ} (_hd : 1 ≤ d)
    (_hd' : 1 ≤ d') (h : root τ d m1 m2 = root τ d' m1' m2') : d = d' ∧ m1 = m1' ∧ m2 = m2' :=
  root_inj' h

open Classical in
/-- The data `(d, m₁, m₂)` of a ready root `ξ = 𝐫_d(m₁, m₂)` (`d ≥ 1`, `ρ_d = 1`; unique by
`root_inj`), and `none` at the other sites. -/
def rootData (U : Machine) (τ : ℕ → Bool × Bool) (ξ : Plane) : Option (ℕ × ℤ × ℤ) :=
  if h : ∃ p : ℕ × ℤ × ℤ, 1 ≤ p.1 ∧ MachineM.ready U p.1 ∧ ξ = root τ p.1 p.2.1 p.2.2 then
    some h.choose
  else none

variable {U : Machine} {τ : ℕ → Bool × Bool}

theorem rootData_eq_some_iff {ξ : Plane} {p : ℕ × ℤ × ℤ} :
    rootData U τ ξ = some p ↔ 1 ≤ p.1 ∧ MachineM.ready U p.1 ∧ ξ = root τ p.1 p.2.1 p.2.2 := by
  unfold rootData
  split_ifs with h
  · rw [Option.some_inj]
    constructor
    · rintro rfl
      exact h.choose_spec
    · rintro ⟨-, -, e2⟩
      obtain ⟨-, -, e1⟩ := h.choose_spec
      obtain ⟨a, b, c⟩ := root_inj' (e1.symm.trans e2)
      exact Prod.ext a (Prod.ext b c)
  · constructor
    · intro h'
      cases h'
    · intro hp
      exact absurd ⟨p, hp⟩ h

theorem rootData_root {d : ℕ} (hd : 1 ≤ d) (hr : MachineM.ready U d) (m1 m2 : ℤ) :
    rootData U τ (root τ d m1 m2) = some (d, m1, m2) :=
  rootData_eq_some_iff.2 ⟨hd, hr, rfl⟩

theorem rootData_cases (ξ : Plane) :
    rootData U τ ξ = none ∨ ∃ d m1 m2, 1 ≤ d ∧ MachineM.ready U d ∧ ξ = root τ d m1 m2 ∧
      rootData U τ ξ = some (d, m1, m2) := by
  rcases h : rootData U τ ξ with _ | ⟨d, m1, m2⟩
  · exact Or.inl rfl
  · obtain ⟨hd, hr, e⟩ := rootData_eq_some_iff.1 h
    exact Or.inr ⟨d, m1, m2, hd, hr, e, rfl⟩

/-! ## The graph -/

variable (U τ) in
/-- **`pay:effective`**: the neighbours in `Γ_τ` of a ready root `𝐫_d(m₁, m₂)` are the four roots
`𝐫_d(m₁ ± 1, m₂)`, `𝐫_d(m₁, m₂ ± 1)`; other sites have no neighbours. -/
def gNbr (ξ : Plane) : Finset Plane :=
  match rootData U τ ξ with
  | some (d, m1, m2) =>
    {root τ d (m1 + 1) m2, root τ d (m1 - 1) m2, root τ d m1 (m2 + 1), root τ d m1 (m2 - 1)}
  | none => ∅

theorem gNbr_root {d : ℕ} (hd : 1 ≤ d) (hr : MachineM.ready U d) (m1 m2 : ℤ) :
    gNbr U τ (root τ d m1 m2) =
      {root τ d (m1 + 1) m2, root τ d (m1 - 1) m2, root τ d m1 (m2 + 1), root τ d m1 (m2 - 1)} := by
  simp only [gNbr, rootData_root hd hr]

theorem mem_gNbr {u v : Plane} :
    v ∈ gNbr U τ u ↔ ∃ d m1 m2, 1 ≤ d ∧ MachineM.ready U d ∧ u = root τ d m1 m2 ∧
      (v = root τ d (m1 + 1) m2 ∨ v = root τ d (m1 - 1) m2 ∨ v = root τ d m1 (m2 + 1) ∨
        v = root τ d m1 (m2 - 1)) := by
  rcases rootData_cases (U := U) (τ := τ) u with h | ⟨d, m1, m2, hd, hr, rfl, -⟩
  · simp only [gNbr, h, Finset.notMem_empty, false_iff]
    rintro ⟨d, m1, m2, hd, hr, rfl, -⟩
    rw [rootData_root hd hr] at h
    cases h
  · rw [gNbr_root hd hr]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hv
      exact ⟨d, m1, m2, hd, hr, rfl, hv⟩
    · rintro ⟨d', m1', m2', -, -, e, hv⟩
      obtain ⟨rfl, rfl, rfl⟩ := root_inj' e
      exact hv

theorem gNbr_symm (u v : Plane) (h : v ∈ gNbr U τ u) : u ∈ gNbr U τ v := by
  obtain ⟨d, m1, m2, hd, hr, rfl, hv⟩ := mem_gNbr.1 h
  rcases hv with rfl | rfl | rfl | rfl
  · exact mem_gNbr.2 ⟨d, m1 + 1, m2, hd, hr, rfl, Or.inr (Or.inl (by rw [add_sub_cancel_right]))⟩
  · exact mem_gNbr.2 ⟨d, m1 - 1, m2, hd, hr, rfl, Or.inl (by rw [sub_add_cancel])⟩
  · exact mem_gNbr.2 ⟨d, m1, m2 + 1, hd, hr, rfl,
      Or.inr (Or.inr (Or.inr (by rw [add_sub_cancel_right])))⟩
  · exact mem_gNbr.2 ⟨d, m1, m2 - 1, hd, hr, rfl, Or.inr (Or.inr (Or.inl (by rw [sub_add_cancel])))⟩

theorem gNbr_irrefl (u : Plane) : u ∉ gNbr U τ u := by
  intro h
  obtain ⟨d, m1, m2, hd, hr, rfl, hv⟩ := mem_gNbr.1 h
  rcases hv with e | e | e | e <;> have := root_inj' e <;> omega

variable (U τ) in
/-- The depth of a ready root (`some d`), and `none` at the other sites: it labels the components
of `Γ_τ` (`isComponentMap_depthOf`). -/
def depthOf (ξ : Plane) : Option ℕ := (rootData U τ ξ).map Prod.fst

theorem depthOf_root {d : ℕ} (hd : 1 ≤ d) (hr : MachineM.ready U d) (m1 m2 : ℤ) :
    depthOf U τ (root τ d m1 m2) = some d := by
  simp only [depthOf, rootData_root hd hr, Option.map_some]

/-- `J_b = ½ log(1 + 1/b) ≥ 0` for `b > 0`. -/
theorem Jc_nonneg {b : ℝ} (hb : 0 < b) : 0 ≤ Jc b := by
  unfold Jc
  have h1 : 1 ≤ 1 + 1 / b := by have := one_div_pos.2 hb; linarith
  exact div_nonneg (Real.log_nonneg h1) (by norm_num)

theorem Jc_bc_nonneg (n : ℕ) (β : ℝ) : 0 ≤ Jc (bc n β) := Jc_nonneg (bc_pos n β)

variable (U τ) in
/-- The coupling carried by a site: `J_{n(d)}(β)` at a ready root of depth `d`, `0` elsewhere. -/
def siteJ (β : ℝ) (ξ : Plane) : ℝ :=
  match depthOf U τ ξ with
  | some d => Jc (bc (MachineM.label d) β)
  | none => 0

theorem siteJ_root (β : ℝ) {d : ℕ} (hd : 1 ≤ d) (hr : MachineM.ready U d) (m1 m2 : ℤ) :
    siteJ U τ β (root τ d m1 m2) = Jc (bc (MachineM.label d) β) := by
  simp only [siteJ, depthOf_root hd hr]

theorem siteJ_nonneg (β : ℝ) (ξ : Plane) : 0 ≤ siteJ U τ β ξ := by
  unfold siteJ
  split
  · exact Jc_bc_nonneg _ _
  · exact le_rfl

theorem siteJ_cases (β : ℝ) (ξ : Plane) : siteJ U τ β ξ = 0 ∨
    ∃ d, 1 ≤ d ∧ MachineM.ready U d ∧ siteJ U τ β ξ = Jc (bc (MachineM.label d) β) := by
  rcases rootData_cases (U := U) (τ := τ) ξ with h | ⟨d, m1, m2, hd, hr, rfl, -⟩
  · left
    simp only [siteJ, depthOf, h, Option.map_none]
  · exact Or.inr ⟨d, hd, hr, siteJ_root β hd hr m1 m2⟩

variable (U τ) in
/-- **`pay:effective`**: the couplings of `Γ_τ`, `J_{n(d)}(β)` on the edges of depth `d` (the
larger of the couplings carried by the two ends; `0` on pairs that are not edges unless one end is
a ready root). -/
def gJ (β : ℝ) : Sym2 Plane → ℝ :=
  Sym2.lift ⟨fun u v => max (siteJ U τ β u) (siteJ U τ β v), fun _ _ => max_comm _ _⟩

variable (U τ) in
/-- **`pay:effective`**: the graph `Γ_τ` with its couplings, as an Ising model (`set:sub-ising`). -/
def Gamma (β : ℝ) : Gibbs.IsingGraph Plane where
  nbr := gNbr U τ
  symm := gNbr_symm
  irrefl := gNbr_irrefl
  J := gJ U τ β
  J_nonneg e := by
    induction e using Sym2.ind with
    | h u v => exact (siteJ_nonneg β u).trans (le_max_left _ _)

/-- **`pay:effective`**: the neighbours in `Γ_τ`. -/
theorem mem_Gamma_nbr (β : ℝ) {u v : Plane} :
    v ∈ (Gamma U τ β).nbr u ↔ ∃ d m1 m2, 1 ≤ d ∧ MachineM.ready U d ∧ u = root τ d m1 m2 ∧
      (v = root τ d (m1 + 1) m2 ∨ v = root τ d (m1 - 1) m2 ∨ v = root τ d m1 (m2 + 1) ∨
        v = root τ d m1 (m2 - 1)) :=
  mem_gNbr

/-- **`pay:effective`**: the coupling `J_{n(d)}(β)` between roots of a ready depth `d`. -/
theorem Gamma_J_root (β : ℝ) {d : ℕ} (hd : 1 ≤ d) (hr : MachineM.ready U d) (m1 m2 m1' m2' : ℤ) :
    (Gamma U τ β).J s(root τ d m1 m2, root τ d m1' m2') = Jc (bc (MachineM.label d) β) := by
  show max (siteJ U τ β (root τ d m1 m2)) (siteJ U τ β (root τ d m1' m2')) = _
  rw [siteJ_root β hd hr, siteJ_root β hd hr, max_self]

/-- **`pay:effective`**: every coupling of `Γ_τ` is `0` or some `J_{n(d)}(β)`, `d` a ready
depth. -/
theorem Gamma_J_cases (β : ℝ) (e : Sym2 Plane) : (Gamma U τ β).J e = 0 ∨
    ∃ d, 1 ≤ d ∧ MachineM.ready U d ∧ (Gamma U τ β).J e = Jc (bc (MachineM.label d) β) := by
  induction e using Sym2.ind with
  | h u v =>
    show max (siteJ U τ β u) (siteJ U τ β v) = 0 ∨
      ∃ d, 1 ≤ d ∧ MachineM.ready U d ∧
        max (siteJ U τ β u) (siteJ U τ β v) = Jc (bc (MachineM.label d) β)
    rcases max_choice (siteJ U τ β u) (siteJ U τ β v) with h | h <;> rw [h]
    · exact siteJ_cases β u
    · exact siteJ_cases β v

/-- `set:sub-ising`: every vertex of `Γ_τ` has at most four neighbours. -/
theorem card_Gamma_nbr_le (β : ℝ) (u : Plane) : ((Gamma U τ β).nbr u).card ≤ 4 := by
  show (gNbr U τ u).card ≤ 4
  rcases rootData_cases (U := U) (τ := τ) u with h | ⟨d, m1, m2, hd, hr, rfl, -⟩
  · simp only [gNbr, h, Finset.card_empty, Nat.zero_le]
  · rw [gNbr_root hd hr]
    exact Finset.card_le_four

/-! ## Components (`thm:main`, Step 3) -/

/-- **`thm:main`, Step 3** ("`Γ_𝔟` is a disjoint union of one square lattice for each ready depth
and of isolated vertices"): neighbours in `Γ_τ` have the same depth label. -/
theorem isComponentMap_depthOf (β : ℝ) : (Gamma U τ β).IsComponentMap (depthOf U τ) := by
  intro u v h
  obtain ⟨d, m1, m2, hd, hr, rfl, hv⟩ := mem_gNbr.1 h
  rw [depthOf_root hd hr]
  rcases hv with rfl | rfl | rfl | rfl <;> rw [depthOf_root hd hr]

variable (U τ) in
/-- `m ↦ 𝐫_d(m)`, into the vertices of depth label `d`. -/
def rootMap {d : ℕ} (hd : 1 ≤ d) (hr : MachineM.ready U d) (m : Plane) :
    {ξ : Plane // depthOf U τ ξ = some d} :=
  ⟨root τ d m.1 m.2, depthOf_root hd hr m.1 m.2⟩

theorem rootMap_bijective {d : ℕ} (hd : 1 ≤ d) (hr : MachineM.ready U d) :
    Function.Bijective (rootMap U τ hd hr) := by
  constructor
  · intro m m' h
    obtain ⟨-, h1, h2⟩ := root_inj' (congrArg Subtype.val h)
    exact Prod.ext h1 h2
  · rintro ⟨ξ, hξ⟩
    rcases rootData_cases (U := U) (τ := τ) ξ with h | ⟨d', m1, m2, hd', hr', rfl, -⟩
    · simp only [depthOf, h, Option.map_none, reduceCtorEq] at hξ
    · rw [depthOf_root hd' hr'] at hξ
      obtain rfl := Option.some_inj.1 hξ
      exact ⟨(m1, m2), rfl⟩

variable (U τ) in
/-- **`thm:main`, Step 3** (after `pay:effective`: "`m ↦ 𝐫_d(m)` is a graph isomorphism from
`ℤ²`"): for a ready depth `d ≥ 1`, `m ↦ 𝐫_d(m)` is an isomorphism from the square lattice with
coupling `J_{n(d)}(β)` onto the component of depth `d` of `Γ_τ`. -/
def squareIso (β : ℝ) {d : ℕ} (hd : 1 ≤ d) (hr : MachineM.ready U d)
    (h : 0 ≤ Jc (bc (MachineM.label d) β)) :
    Gibbs.IsingGraph.Iso (Peierls.squareLattice (Jc (bc (MachineM.label d) β)) h)
      ((Gamma U τ β).restrict (depthOf U τ) (some d)) where
  e := Equiv.ofBijective _ (rootMap_bijective hd hr)
  nbr u := by
    ext w
    show w ∈ (gNbr U τ (root τ d u.1 u.2)).subtype (fun v => depthOf U τ v = some d) ↔
      w ∈ (Peierls.nbrs u).map (Equiv.ofBijective _ (rootMap_bijective hd hr)).toEmbedding
    rw [Finset.mem_subtype, Finset.mem_map]
    show w.1 ∈ gNbr U τ (root τ d u.1 u.2) ↔ ∃ a ∈ Peierls.nbrs u, rootMap U τ hd hr a = w
    rw [gNbr_root hd hr]
    simp only [Peierls.nbrs, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (h | h | h | h)
      · exact ⟨u + e1, Or.inl rfl, Subtype.ext (by simp [rootMap, h, e1])⟩
      · exact ⟨u - e1, Or.inr (Or.inl rfl), Subtype.ext (by simp [rootMap, h, e1])⟩
      · exact ⟨u + e2, Or.inr (Or.inr (Or.inl rfl)), Subtype.ext (by simp [rootMap, h, e2])⟩
      · exact ⟨u - e2, Or.inr (Or.inr (Or.inr rfl)), Subtype.ext (by simp [rootMap, h, e2])⟩
    · rintro ⟨a, ha, rfl⟩
      rcases ha with rfl | rfl | rfl | rfl <;> simp [rootMap, e1, e2]
  J u v _ := by
    show (Gamma U τ β).J s(root τ d u.1 u.2, root τ d v.1 v.2) = Jc (bc (MachineM.label d) β)
    exact Gamma_J_root β hd hr _ _ _ _

theorem squareIso_e (β : ℝ) {d : ℕ} (hd : 1 ≤ d) (hr : MachineM.ready U d)
    (h : 0 ≤ Jc (bc (MachineM.label d) β)) (m : Plane) :
    ((squareIso U τ β hd hr h).e m).1 = root τ d m.1 m.2 := rfl

end UPD.BG

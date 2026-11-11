/-
# Section 3.2 and Appendix A: the substitutions `φ`, `φ'` and their soundness

Ported from the forgetting core (`C:/Infanox/fixed-noise-ergodicity-lean`,
`FixedNoiseErgodicity/Scaffold/Substitution.lean`, and the maps `F`, `se`, `nw` and the matching
relations of `FixedNoiseErgodicity/Scaffold/Tables.lean`; same authors), namespace `FNE.Scaffold`
→ `UPD.Scaffold`, onto the definitions of `Statements.lean` (`Thick.IsCorner`, `IsRed` are `Bool`
here). Paper labels of this paper:
* App. A: the maps `F`, `se`, `nw` and their listed identities; the thin matching pairs.
* `scf:def-base`, `tab:subst`: `Formal.child`; `app:sound` (a), (b), (c) (`Formal.inO_child`,
  `legalOn_phi_iff`, `Formal.child_injective`).
* `scf:def-ruler`: `Letter.child`; `app:ruler-sound` (a), (b), (c) (`Letter.InA.child`,
  `legalOn_phi'_iff`, `Letter.child_injective`); the edgewise bit property (after
  `scf:def-ruler`).
* `subst2`: blockwise `2 × 2` substitution of patterns, `φ(w)(2v + ς) = φ(w(v))(ς)`, and the
  generic criterion `legalOn_subst2_iff` (internal edges match, and the two fine edges across a
  seam match iff the coarse edge matches; then `φ(w)` is legal on `2U + [0,2)²` iff `w` is legal
  on `U`). This is the argument of `app:sound`(b) and `app:ruler-sound`(b), stated once.
* `σ = φ'∘φ'` and its powers: legal patterns on `[0,4ⁿ)²`; `exists_letter_tiling` (`𝔸` tiles,
  first claim of `scf:desub`), by compactness.
**[choice] (proof side)** A child `ς ∈ [0,2)²` is given by two Booleans `(ς₁ = 1, ς₂ = 1)`.
-/
import UndecidablePhaseDiagram.Scaffold.Tables
import UndecidablePhaseDiagram.Scaffold.Legal

set_option autoImplicit false

-- `child_inO_check` and `child_inA_check` walk the lists of 104 and 276 entries in the kernel.
-- Kernel checks are Boolean folds (`List.all … = true`): a `Decidable` instance for a bounded
-- quantifier over the same list builds proof terms at every step and needs more than 4 GB.
set_option maxRecDepth 20000

namespace UPD.Scaffold

/-! ## The maps `F`, `se`, `nw` (App. A, after `tab:edges`) -/

/-- App. A: `F(a) = ∠b`, `F(b) = ∠d`, `F(c) = ∠c`, `F(d) = ∠a`; the corner with the four
endpoints of a thin type. -/
def F : Thin → Corner
  | .a => .b | .b => .d | .c => .c | .d => .a

/-- App. A: the black map `se`. -/
def se : Black → Black
  | .A => .B | .B => .B | .C => .C | .D => .C | .E => .C

/-- App. A: the black map `nw`. -/
def nw : Black → Black
  | .A => .E | .B => .D | .C => .D | .D => .D | .E => .E

/-- App. A: each corner `F(θ)` has exactly the four endpoints of `θ`. -/
theorem F_epN (θ : Thin) : (F θ).epN = θ.epN := by cases θ <;> rfl
theorem F_epS (θ : Thin) : (F θ).epS = θ.epS := by cases θ <;> rfl
theorem F_epE (θ : Thin) : (F θ).epE = θ.epE := by cases θ <;> rfl
theorem F_epW (θ : Thin) : (F θ).epW = θ.epW := by cases θ <;> rfl

/-- `F` is a bijection from thin types to corners. -/
theorem F_injective : Function.Injective F := by
  intro x y h; cases x <;> cases y <;> first | rfl | cases h

theorem F_surjective : Function.Surjective F := by
  intro k; cases k
  · exact ⟨.d, rfl⟩
  · exact ⟨.a, rfl⟩
  · exact ⟨.c, rfl⟩
  · exact ⟨.b, rfl⟩

/-- App. A: thin types match horizontally (west tile first) exactly in the pairs
`(a,c), (c,a), (b,d), (d,b)`. -/
theorem thin_matchE_iff (θ θ' : Thin) :
    θ.epE = θ'.epW ↔ (θ, θ') ∈ [(.a, .c), (.c, .a), (.b, .d), (.d, .b)] := by
  cases θ <;> cases θ' <;> decide

/-- App. A: thin types match vertically (south tile first) exactly in the pairs
`(a,d), (d,a), (b,c), (c,b)`. -/
theorem thin_matchN_iff (θ θ' : Thin) :
    θ.epN = θ'.epS ↔ (θ, θ') ∈ [(.a, .d), (.d, .a), (.b, .c), (.c, .b)] := by
  cases θ <;> cases θ' <;> decide

/-- App. A: `se(ψ) ∈ {B, C}` and `∂_W se(ψ) = ∂_E ψ`. -/
theorem se_spec (ω : Black) : (se ω = .B ∨ se ω = .C) ∧ (se ω).bitW = ω.bitE := by
  cases ω <;> decide

/-- App. A: `nw(ψ) ∈ {D, E}` and `∂_S nw(ψ) = ∂_N ψ`. -/
theorem nw_spec (ω : Black) : (nw ω = .D ∨ nw ω = .E) ∧ (nw ω).bitS = ω.bitN := by
  cases ω <;> decide

/-- App. A: `se(ψ)` is the type in `{B, C}` with west bit `∂_E ψ`. -/
theorem se_unique (ω ω' : Black) (h : ω' = .B ∨ ω' = .C) (h' : ω'.bitW = ω.bitE) :
    ω' = se ω := by
  rcases h with rfl | rfl <;> cases ω <;> simp_all [Black.bitW, Black.bitE, se]

/-- App. A: `nw(ψ)` is the type in `{D, E}` with south bit `∂_N ψ`. -/
theorem nw_unique (ω ω' : Black) (h : ω' = .D ∨ ω' = .E) (h' : ω'.bitS = ω.bitN) :
    ω' = nw ω := by
  rcases h with rfl | rfl <;> cases ω <;> simp_all [Black.bitS, Black.bitN, nw]

/-- App. A: the further identities of `se` and `nw`. -/
theorem se_bitE (ω : Black) : (se ω).bitE = ω.bitE := by cases ω <;> rfl
theorem nw_bitN (ω : Black) : (nw ω).bitN = ω.bitN := by cases ω <;> rfl
theorem se_bitS (ω : Black) : (se ω).bitS = false := by cases ω <;> rfl
theorem nw_bitW (ω : Black) : (nw ω).bitW = false := by cases ω <;> rfl
theorem se_bitN (ω : Black) : (se ω).bitN = true := by cases ω <;> rfl
theorem nw_bitE (ω : Black) : (nw ω).bitE = true := by cases ω <;> rfl

/-! ## Matching of triples and letters (Section 3, "Wang sets") -/

namespace Formal

theorem mem_baseList {t : Formal} : t ∈ baseList ↔ t.inO = true := by
  simp [baseList, mem_all]

/-- `t, t'` match in direction `e₁` if `t_E = t'_W`. -/
def MatchE (t t' : Formal) : Prop := t.colE = t'.colW

/-- `t, t'` match in direction `e₂` if `t_N = t'_S`. -/
def MatchN (t t' : Formal) : Prop := t.colN = t'.colS

instance : DecidableRel MatchE := fun t t' => inferInstanceAs (Decidable (t.colE = t'.colW))

instance : DecidableRel MatchN := fun t t' => inferInstanceAs (Decidable (t.colN = t'.colS))

theorem matchE_iff {t t' : Formal} : MatchE t t' ↔
    t.thin.epE = t'.thin.epW ∧ t.thick.epE = t'.thick.epW ∧ t.black.bitE = t'.black.bitW := by
  simp [MatchE, colE, colW]

theorem matchN_iff {t t' : Formal} : MatchN t t' ↔
    t.thin.epN = t'.thin.epS ∧ t.thick.epN = t'.thick.epS ∧ t.black.bitN = t'.black.bitS := by
  simp [MatchN, colN, colS]

end Formal

namespace Letter

/-- Letters `x, y` match in direction `e₁` if `x_E = y_W`. -/
def MatchE (x y : Letter) : Prop := x.colE = y.colW

/-- Letters `x, y` match in direction `e₂` if `x_N = y_S`. -/
def MatchN (x y : Letter) : Prop := x.colN = y.colS

instance : DecidableRel MatchE := fun x y => inferInstanceAs (Decidable (x.colE = y.colW))

instance : DecidableRel MatchN := fun x y => inferInstanceAs (Decidable (x.colN = y.colS))

theorem matchE_iff {x y : Letter} : MatchE x y ↔ x.base.MatchE y.base ∧ x.b2 = y.b2 := by
  simp [MatchE, colE, colW, Formal.MatchE]

theorem matchN_iff {x y : Letter} : MatchN x y ↔ x.base.MatchN y.base ∧ x.b1 = y.b1 := by
  simp [MatchN, colN, colS, Formal.MatchN]

/-- After `scf:def-ruler`: letters that match vertically have the same column bit, and letters
that match horizontally have the same row bit. -/
theorem MatchN.b1_eq {x y : Letter} (h : MatchN x y) : x.b1 = y.b1 := (matchN_iff.1 h).2

theorem MatchE.b2_eq {x y : Letter} (h : MatchE x y) : x.b2 = y.b2 := (matchE_iff.1 h).2

end Letter


/-! ## Blockwise `2 × 2` substitution of patterns -/

section Subst2

variable {α β : Type*}

/-- The bit `0` or `1` of a Boolean, as an integer. -/
def bitZ (s : Bool) : ℤ := if s then 1 else 0

/-- `scf:def-base` (blockwise): `φ(w)(2v + ς) = φ(w(v))(ς)`. Children are indexed by two
Booleans, `ς = (bitZ s₁, bitZ s₂)`. -/
def subst2 (φ : α → Bool → Bool → β) (w : Plane → α) : Plane → β :=
  fun x => φ (w (x.1 / 2, x.2 / 2)) (decide (x.1 % 2 = 1)) (decide (x.2 % 2 = 1))

/-- The fine domain `2U + [0,2)²` of `φ(w)` for a pattern `w` on `U`. -/
def fine2 (U : Set Plane) : Set Plane := {x | (x.1 / 2, x.2 / 2) ∈ U}

/-- The fine site `2v + ς`. -/
def fineSite (v : Plane) (s1 s2 : Bool) : Plane := (2 * v.1 + bitZ s1, 2 * v.2 + bitZ s2)

theorem fineSite_div (v : Plane) (s1 s2 : Bool) :
    ((fineSite v s1 s2).1 / 2, (fineSite v s1 s2).2 / 2) = v := by
  obtain ⟨v1, v2⟩ := v
  cases s1 <;> cases s2 <;> simp only [fineSite, bitZ, Prod.mk.injEq] <;> omega

theorem subst2_fineSite (φ : α → Bool → Bool → β) (w : Plane → α) (v : Plane) (s1 s2 : Bool) :
    subst2 φ w (fineSite v s1 s2) = φ (w v) s1 s2 := by
  obtain ⟨v1, v2⟩ := v
  have hv := fineSite_div (v1, v2) s1 s2
  simp only [subst2]
  rw [hv]
  cases s1 <;> cases s2 <;> simp only [fineSite, bitZ] <;> congr <;> simp

theorem fineSite_mem {U : Set Plane} {v : Plane} {s1 s2 : Bool} :
    fineSite v s1 s2 ∈ fine2 U ↔ v ∈ U := by
  simp only [fine2, Set.mem_setOf_eq, fineSite_div]

theorem exists_fineSite (x : Plane) : ∃ v s1 s2, x = fineSite v s1 s2 := by
  refine ⟨(x.1 / 2, x.2 / 2), decide (x.1 % 2 = 1), decide (x.2 % 2 = 1), ?_⟩
  obtain ⟨x1, x2⟩ := x
  simp only [fineSite, bitZ, Prod.mk.injEq]
  constructor <;> split_ifs with h <;> simp_all <;> omega

theorem fineSite_false_add_e1 (v : Plane) (s2 : Bool) :
    fineSite v false s2 + (1, 0) = fineSite v true s2 := by
  simp only [fineSite, bitZ, Prod.mk_add_mk, Prod.mk.injEq]; constructor <;> simp

theorem fineSite_true_add_e1 (v : Plane) (s2 : Bool) :
    fineSite v true s2 + (1, 0) = fineSite (v + (1, 0)) false s2 := by
  simp only [fineSite, bitZ, Prod.mk_add_mk, Prod.fst_add, Prod.snd_add, Prod.mk.injEq]
  exact ⟨by simp; ring, by simp⟩

theorem fineSite_false_add_e2 (v : Plane) (s1 : Bool) :
    fineSite v s1 false + (0, 1) = fineSite v s1 true := by
  simp only [fineSite, bitZ, Prod.mk_add_mk, Prod.mk.injEq]; constructor <;> simp

theorem fineSite_true_add_e2 (v : Plane) (s1 : Bool) :
    fineSite v s1 true + (0, 1) = fineSite (v + (0, 1)) s1 false := by
  simp only [fineSite, bitZ, Prod.mk_add_mk, Prod.fst_add, Prod.snd_add, Prod.mk.injEq]
  exact ⟨by simp, by simp; ring⟩

/-- The argument of `app:sound`(b) and `app:ruler-sound`(b), once for all `2 × 2`
substitutions. If the internal edges of every block `φ(a)` match, and the two fine edges across a
vertical (horizontal) seam between `φ(a)` and `φ(a')` both match exactly when `a, a'` match in
direction `e₁` (`e₂`), then `φ(w)` is legal on `2U + [0,2)²` if and only if `w` is legal on
`U`. -/
theorem legalOn_subst2_iff {Hα Vα : α → α → Prop} {Hβ Vβ : β → β → Prop}
    (φ : α → Bool → Bool → β)
    (inH : ∀ a s2, Hβ (φ a false s2) (φ a true s2))
    (inV : ∀ a s1, Vβ (φ a s1 false) (φ a s1 true))
    (seamH : ∀ a a', (Hβ (φ a true false) (φ a' false false) ∧
      Hβ (φ a true true) (φ a' false true)) ↔ Hα a a')
    (seamV : ∀ a a', (Vβ (φ a false true) (φ a' false false) ∧
      Vβ (φ a true true) (φ a' true false)) ↔ Vα a a')
    {U : Set Plane} {w : Plane → α} :
    LegalOn Hβ Vβ (fine2 U) (subst2 φ w) ↔ LegalOn Hα Vα U w := by
  constructor
  · rintro ⟨hH, hV⟩
    refine ⟨fun u hu hu' => (seamH _ _).1 ?_, fun u hu hu' => (seamV _ _).1 ?_⟩
    · have key : ∀ s2, Hβ (φ (w u) true s2) (φ (w (u + (1, 0))) false s2) := by
        intro s2
        have := hH (fineSite u true s2) (fineSite_mem.2 hu)
          (by rw [fineSite_true_add_e1]; exact fineSite_mem.2 hu')
        rwa [fineSite_true_add_e1, subst2_fineSite, subst2_fineSite] at this
      exact ⟨key false, key true⟩
    · have key : ∀ s1, Vβ (φ (w u) s1 true) (φ (w (u + (0, 1))) s1 false) := by
        intro s1
        have := hV (fineSite u s1 true) (fineSite_mem.2 hu)
          (by rw [fineSite_true_add_e2]; exact fineSite_mem.2 hu')
        rwa [fineSite_true_add_e2, subst2_fineSite, subst2_fineSite] at this
      exact ⟨key false, key true⟩
  · rintro ⟨hH, hV⟩
    refine ⟨fun x hx hx' => ?_, fun x hx hx' => ?_⟩
    · obtain ⟨v, s1, s2, rfl⟩ := exists_fineSite x
      cases s1
      · rw [fineSite_false_add_e1, subst2_fineSite, subst2_fineSite]; exact inH _ _
      · rw [fineSite_true_add_e1] at hx' ⊢
        rw [subst2_fineSite, subst2_fineSite]
        have h := (seamH _ _).2 (hH v (fineSite_mem.1 hx) (fineSite_mem.1 hx'))
        cases s2
        · exact h.1
        · exact h.2
    · obtain ⟨v, s1, s2, rfl⟩ := exists_fineSite x
      cases s2
      · rw [fineSite_false_add_e2, subst2_fineSite, subst2_fineSite]; exact inV _ _
      · rw [fineSite_true_add_e2] at hx' ⊢
        rw [subst2_fineSite, subst2_fineSite]
        have h := (seamV _ _).2 (hV v (fineSite_mem.1 hx) (fineSite_mem.1 hx'))
        cases s1
        · exact h.1
        · exact h.2

/-- Values of `φ(w)` on `2U + [0,2)²` are children of values of `w` on `U`. -/
theorem subst2_mem {P : α → Prop} {Q : β → Prop} (φ : α → Bool → Bool → β)
    (hφ : ∀ a, P a → ∀ s1 s2, Q (φ a s1 s2)) {U : Set Plane} {w : Plane → α}
    (hw : ∀ u ∈ U, P (w u)) : ∀ x ∈ fine2 U, Q (subst2 φ w x) := by
  intro x hx
  obtain ⟨v, s1, s2, rfl⟩ := exists_fineSite x
  rw [subst2_fineSite]
  exact hφ _ (hw v (fineSite_mem.1 hx)) s1 s2

end Subst2

/-! ## `φ` on formal triples (`scf:def-base`, `app:sound`) -/

namespace Formal

/-- `scf:def-base`, `tab:subst` (left): the child `ς = (s₁, s₂)` of `φ(θ, κ, ω)`:
`(0,0) ↦ (a, κ, ω)`, `(1,0) ↦ (c, ⟨∂_S θ, ∂_E κ⟩, se ω)`, `(0,1) ↦ (d, ⟨∂_N κ, ∂_W θ⟩, nw ω)`,
`(1,1) ↦ (b, F(θ), A)`. Defined for every formal triple. -/
def child (t : Formal) : Bool → Bool → Formal
  | false, false => ⟨.a, t.thick, t.black⟩
  | true, false => ⟨.c, .line t.thin.epS t.thick.epE, se t.black⟩
  | false, true => ⟨.d, .line t.thick.epN t.thin.epW, nw t.black⟩
  | true, true => ⟨.b, .corner (F t.thin), .A⟩

/-- `app:sound`(a), first half: the four children of a tile of `𝕆` lie in `𝕆`
(a check over the 104 tiles). -/
theorem child_inO_check : (baseList.all fun t => [false, true].all fun s1 =>
    [false, true].all fun s2 => (t.child s1 s2).inO) = true := by
  decide +kernel

theorem inO_child {t : Formal} (h : t.inO = true) (s1 s2 : Bool) : (t.child s1 s2).inO = true := by
  have h1 := List.all_eq_true.1 child_inO_check t (mem_baseList.2 h)
  have h2 := List.all_eq_true.1 h1 s1 (by cases s1 <;> simp)
  exact List.all_eq_true.1 h2 s2 (by cases s2 <;> simp)

/-- `app:sound`(a), second half: the four internal edges of `φ(t)` match, for every formal
triple. -/
theorem child_matchE (t : Formal) (s2 : Bool) : MatchE (t.child false s2) (t.child true s2) := by
  rw [matchE_iff]
  cases s2
  · exact ⟨rfl, rfl, (se_spec t.black).2.symm⟩
  · exact ⟨rfl, (F_epW t.thin).symm, nw_bitE t.black⟩

theorem child_matchN (t : Formal) (s1 : Bool) : MatchN (t.child s1 false) (t.child s1 true) := by
  rw [matchN_iff]
  cases s1
  · exact ⟨rfl, rfl, (nw_spec t.black).2.symm⟩
  · exact ⟨rfl, (F_epS t.thin).symm, se_bitN t.black⟩

/-- `app:sound`(b), the seam in direction `e₁`: the two fine edges across the seam between `φ(t)`
and `φ(t')` both match if and only if `t, t'` match. -/
theorem seamE (t t' : Formal) :
    (MatchE (t.child true false) (t'.child false false) ∧
      MatchE (t.child true true) (t'.child false true)) ↔ MatchE t t' := by
  -- lower fine edge: thin `g₃, g₃`; thick `∂_E κ, ∂_W κ'`; black `∂_E se(ω) = ∂_E ω, ∂_W ω'`
  have h1 : MatchE (t.child true false) (t'.child false false) ↔
      t.thick.epE = t'.thick.epW ∧ t.black.bitE = t'.black.bitW := by
    rw [matchE_iff]
    change (HAtom.g3 = HAtom.g3 ∧ t.thick.epE = t'.thick.epW ∧
      (se t.black).bitE = t'.black.bitW) ↔ _
    rw [se_bitE]; simp
  -- upper fine edge: thin `g₁, g₁`; thick `∂_E F(θ) = ∂_E θ, ∂_W θ'`; black `0, 0`
  have h2 : MatchE (t.child true true) (t'.child false true) ↔ t.thin.epE = t'.thin.epW := by
    rw [matchE_iff]
    change (HAtom.g1 = HAtom.g1 ∧ (F t.thin).epE = t'.thin.epW ∧
      false = (nw t'.black).bitW) ↔ _
    rw [F_epE, nw_bitW]; simp
  rw [h1, h2, matchE_iff]
  tauto

/-- `app:sound`(b), the seam in direction `e₂`. -/
theorem seamN (t t' : Formal) :
    (MatchN (t.child false true) (t'.child false false) ∧
      MatchN (t.child true true) (t'.child true false)) ↔ MatchN t t' := by
  -- left fine edge: thin `g₂, g₂`; thick `∂_N κ, ∂_S κ'`; black `∂_N nw(ω) = ∂_N ω, ∂_S ω'`
  have h1 : MatchN (t.child false true) (t'.child false false) ↔
      t.thick.epN = t'.thick.epS ∧ t.black.bitN = t'.black.bitS := by
    rw [matchN_iff]
    change (VAtom.g2 = VAtom.g2 ∧ t.thick.epN = t'.thick.epS ∧
      (nw t.black).bitN = t'.black.bitS) ↔ _
    rw [nw_bitN]; simp
  -- right fine edge: thin `g₀, g₀`; thick `∂_N F(θ) = ∂_N θ, ∂_S θ'`; black `0, 0`
  have h2 : MatchN (t.child true true) (t'.child true false) ↔ t.thin.epN = t'.thin.epS := by
    rw [matchN_iff]
    change (VAtom.g0 = VAtom.g0 ∧ (F t.thin).epN = t'.thin.epS ∧
      false = (se t'.black).bitS) ↔ _
    rw [F_epN, se_bitS]; simp
  rw [h1, h2, matchN_iff]
  tauto

/-- `app:sound`(b): for every pattern `w` of formal triples on `U`, `φ(w)` is legal on
`2U + [0,2)²` if and only if `w` is legal on `U`. (Stated for all formal triples; the printed
statement is the case of patterns of `𝕆`.) -/
theorem legalOn_phi_iff {U : Set Plane} {w : Plane → Formal} :
    LegalOn MatchE MatchN (fine2 U) (subst2 child w) ↔ LegalOn MatchE MatchN U w :=
  legalOn_subst2_iff child child_matchE child_matchN seamE seamN

/-- `app:sound`(a): `φ(t)` is a legal pattern of tiles of `𝕆` on `[0,2)²`. -/
theorem phi_legal {t : Formal} (h : t.inO = true) :
    (∀ x ∈ fine2 {0}, (subst2 child (fun _ => t) x).inO = true) ∧
      LegalOn MatchE MatchN (fine2 {0}) (subst2 child (fun _ => t)) :=
  ⟨subst2_mem (P := fun t : Formal => t.inO = true) (Q := fun t : Formal => t.inO = true) child
    (fun _ h' => inO_child h') (fun _ _ => h),
    legalOn_phi_iff.2 ⟨fun u hu hu' => by simp_all, fun u hu hu' => by simp_all⟩⟩

/-- `app:sound`(c): `φ` is injective on formal triples: child `(0,0)` shows `κ` and `ω`, and
child `(1,1)` shows `F(θ)`. -/
theorem child_injective {t t' : Formal} (h : ∀ s1 s2, t.child s1 s2 = t'.child s1 s2) :
    t = t' := by
  obtain ⟨θ, κ, ω⟩ := t
  obtain ⟨θ', κ', ω'⟩ := t'
  have h00 := h false false
  have h11 := h true true
  simp only [child, mk.injEq, Thick.corner.injEq, true_and] at h00 h11
  rw [F_injective h11.1, h00.1, h00.2]

end Formal

/-! ## `φ'` on letters (`scf:def-ruler`, `app:ruler-sound`) -/

namespace Letter

/-- `scf:def-ruler`, `tab:subst` (right): the child `ς = (s₁, s₂)` of `φ'(𝔞)`: base
`φ(𝔞̄)(ς)`, column bit `1 - b₁` if `ς₁ = 0` and `0` if `ς₁ = 1`, row bit `1 - b₂` if `ς₂ = 0`
and `0` if `ς₂ = 1`. -/
def child (x : Letter) (s1 s2 : Bool) : Letter :=
  ⟨x.base.child s1 s2, if s1 then false else !x.b1, if s2 then false else !x.b2⟩

/-- `app:ruler-sound`(a), first half: the children of a letter of `𝔸` lie in `𝔸`
(a check over the 276 letters). -/
theorem child_inA_check : (letters.all fun x => [false, true].all fun s1 =>
    [false, true].all fun s2 => decide (x.child s1 s2).InA) = true := by
  decide +kernel

theorem InA.child {x : Letter} (h : x.InA) (s1 s2 : Bool) : (x.child s1 s2).InA := by
  have h1 := List.all_eq_true.1 child_inA_check x (mem_letters.2 h)
  have h2 := List.all_eq_true.1 h1 s1 (by cases s1 <;> simp)
  exact of_decide_eq_true (List.all_eq_true.1 h2 s2 (by cases s2 <;> simp))

theorem child_matchE (x : Letter) (s2 : Bool) : MatchE (x.child false s2) (x.child true s2) :=
  matchE_iff.2 ⟨Formal.child_matchE _ _, rfl⟩

theorem child_matchN (x : Letter) (s1 : Bool) : MatchN (x.child s1 false) (x.child s1 true) :=
  matchN_iff.2 ⟨Formal.child_matchN _ _, rfl⟩

/-- `app:ruler-sound`(b), the seam in direction `e₁`: bases as in `app:sound`(b); the lower
fine edge carries row bits `1 - b₂, 1 - b₂'`, the upper one `0, 0`. -/
theorem seamE (x y : Letter) :
    (MatchE (x.child true false) (y.child false false) ∧
      MatchE (x.child true true) (y.child false true)) ↔ MatchE x y := by
  have h := Formal.seamE x.base y.base
  simp only [matchE_iff]
  change ((x.base.child true false).MatchE (y.base.child false false) ∧ (!x.b2) = !y.b2) ∧
    ((x.base.child true true).MatchE (y.base.child false true) ∧ false = false) ↔ _
  constructor
  · rintro ⟨⟨h1, hb⟩, h2, -⟩
    exact ⟨h.1 ⟨h1, h2⟩, by simpa using hb⟩
  · rintro ⟨hm, hb⟩
    obtain ⟨h1, h2⟩ := h.2 hm
    exact ⟨⟨h1, by rw [hb]⟩, h2, rfl⟩

/-- `app:ruler-sound`(b), the seam in direction `e₂`. -/
theorem seamN (x y : Letter) :
    (MatchN (x.child false true) (y.child false false) ∧
      MatchN (x.child true true) (y.child true false)) ↔ MatchN x y := by
  have h := Formal.seamN x.base y.base
  simp only [matchN_iff]
  change ((x.base.child false true).MatchN (y.base.child false false) ∧ (!x.b1) = !y.b1) ∧
    ((x.base.child true true).MatchN (y.base.child true false) ∧ false = false) ↔ _
  constructor
  · rintro ⟨⟨h1, hb⟩, h2, -⟩
    exact ⟨h.1 ⟨h1, h2⟩, by simpa using hb⟩
  · rintro ⟨hm, hb⟩
    obtain ⟨h1, h2⟩ := h.2 hm
    exact ⟨⟨h1, by rw [hb]⟩, h2, rfl⟩

/-- `app:ruler-sound`(b): for every pattern `w` of letters on `U`, `φ'(w)` is legal on
`2U + [0,2)²` if and only if `w` is legal on `U`. -/
theorem legalOn_phi'_iff {U : Set Plane} {w : Plane → Letter} :
    LegalOn MatchE MatchN (fine2 U) (subst2 child w) ↔ LegalOn MatchE MatchN U w :=
  legalOn_subst2_iff child child_matchE child_matchN seamE seamN

/-- `app:ruler-sound`(a): `φ'(𝔞)` is a legal pattern of letters of `𝔸` on `[0,2)²`. -/
theorem phi'_legal {x : Letter} (h : x.InA) :
    (∀ y ∈ fine2 {0}, (subst2 child (fun _ => x) y).InA) ∧
      LegalOn MatchE MatchN (fine2 {0}) (subst2 child (fun _ => x)) :=
  ⟨subst2_mem child (fun _ h' => h'.child) (fun _ _ => h),
    legalOn_phi'_iff.2 ⟨fun u hu hu' => by simp_all, fun u hu hu' => by simp_all⟩⟩

/-- `app:ruler-sound`(c): `φ'` is injective: child `(0,0)` shows `κ`, `ω` and the complements
of both bits, and child `(1,1)` shows `θ`. -/
theorem child_injective {x y : Letter} (h : ∀ s1 s2, x.child s1 s2 = y.child s1 s2) : x = y := by
  obtain ⟨t, b1, b2⟩ := x
  obtain ⟨t', b1', b2'⟩ := y
  have ht : t = t' := Formal.child_injective fun s1 s2 => congrArg base (h s1 s2)
  have h00 := h false false
  simp only [child, mk.injEq, Bool.false_eq_true, ↓reduceIte, Bool.not_inj_iff] at h00
  rw [ht, h00.2.1, h00.2.2]

end Letter

/-! ## `σ = φ' ∘ φ'` and its powers (forgetting core's `prop:scaffold`) -/

/-- `φ'` on patterns of letters (blockwise, `scf:def-ruler`). -/
def phi' (w : Plane → Letter) : Plane → Letter := subst2 Letter.child w

/-- `σ` on patterns: `σ(w) = φ'(φ'(w))`, blockwise with `4 × 4` blocks. -/
def sigmaPat (w : Plane → Letter) : Plane → Letter := phi' (phi' w)

/-- `scf:def-ruler`: `σ(𝔞)(2τ + ς) = φ'(φ'(𝔞)(τ))(ς)`, a pattern on `[0,4)²`. -/
def sigma (x : Letter) : Plane → Letter := sigmaPat fun _ => x

/-- `scf:def-ruler`: `σⁿ(𝔞)`, a pattern on `[0,4ⁿ)²` (`n`-fold blockwise `σ`). -/
def sigmaPow (n : ℕ) (x : Letter) : Plane → Letter := sigmaPat^[n] fun _ => x

/-- The forgetting paper's remark at 06:19: `(φ')^{2n}(𝔞) = σⁿ(𝔞)` (blockwise substitution
 composes). -/
theorem phi'_iterate_two_mul (n : ℕ) (x : Letter) : phi'^[2 * n] (fun _ => x) = sigmaPow n x := by
  have h : sigmaPat = phi'^[2] := rfl
  rw [sigmaPow, h, ← Function.iterate_mul]

/-- The square `[0, 4ⁿ)²`. -/
def sq (n : ℕ) : Set Plane := square 0 (4 ^ n)

theorem fine2_fine2_sq (n : ℕ) : fine2 (fine2 (sq n)) = sq (n + 1) := by
  ext x
  obtain ⟨x1, x2⟩ := x
  simp only [fine2, sq, square, Set.mem_setOf_eq, Prod.fst_zero, Prod.snd_zero, zero_add,
    pow_succ]
  generalize (4 : ℤ) ^ n = N
  push_cast
  omega

theorem sq_zero : sq 0 = {0} := by
  ext x
  obtain ⟨x1, x2⟩ := x
  simp only [sq, square, Set.mem_setOf_eq, Prod.fst_zero, Prod.snd_zero, zero_add, pow_zero,
    Nat.cast_one, Set.mem_singleton_iff, Prod.mk_eq_zero]
  omega

/-- forgetting `prop:scaffold`(ii): for every pattern `w` of letters on `U`, `σ(w)` is legal on
`4U + [0,4)²` if and only if `w` is legal on `U`. -/
theorem legalOn_sigma_iff {U : Set Plane} {w : Plane → Letter} :
    LegalOn Letter.MatchE Letter.MatchN (fine2 (fine2 U)) (sigmaPat w) ↔
      LegalOn Letter.MatchE Letter.MatchN U w := by
  rw [sigmaPat, phi', phi', Letter.legalOn_phi'_iff, Letter.legalOn_phi'_iff]

theorem sigmaPat_mem {U : Set Plane} {w : Plane → Letter} (hw : ∀ u ∈ U, (w u).InA) :
    ∀ x ∈ fine2 (fine2 U), (sigmaPat w x).InA :=
  subst2_mem _ (fun _ h => h.child) (subst2_mem _ (fun _ h => h.child) hw)

/-- forgetting `prop:scaffold`(i): `σⁿ(𝔞)` is a legal pattern of letters of `𝔸` on `[0,4ⁿ)²`. -/
theorem sigmaPow_legal {x : Letter} (hx : x.InA) (n : ℕ) :
    (∀ y ∈ sq n, (sigmaPow n x y).InA) ∧
      LegalOn Letter.MatchE Letter.MatchN (sq n) (sigmaPow n x) := by
  induction n with
  | zero =>
    rw [sq_zero]
    exact ⟨fun _ _ => hx, fun u hu hu' => by simp_all, fun u hu hu' => by simp_all⟩
  | succ n ih =>
    simp only [sigmaPow, Function.iterate_succ_apply'] at ih ⊢
    rw [← fine2_fine2_sq]
    exact ⟨sigmaPat_mem ih.1, legalOn_sigma_iff.2 ih.2⟩

/-- forgetting `prop:scaffold`(i): `σ` is injective. -/
theorem sigma_injective {x y : Letter} (h : ∀ i ∈ sq 1, sigma x i = sigma y i) : x = y := by
  apply Letter.child_injective
  intro s1 s2
  apply Letter.child_injective
  intro s1' s2'
  have := h (fineSite (fineSite 0 s1 s2) s1' s2') (by
    rw [← fine2_fine2_sq, sq_zero, fineSite_mem, fineSite_mem]; rfl)
  simpa [sigma, sigmaPat, phi', subst2_fineSite] using this

/-- forgetting `prop:scaffold`(iv): the bits of `σ(𝔞)(i)`: the column bit is `χ₁(𝔞)` if
`i₁ = 0`, `0` if `i₁ ∈ {1, 3}` and `1` if `i₁ = 2`; the row bit likewise with `i₂`. -/
theorem sigma_bits (x : Letter) (τ1 τ2 s1 s2 : Bool) :
    (sigma x (fineSite (fineSite 0 τ1 τ2) s1 s2)).b1 =
      (if s1 then false else if τ1 then true else x.b1) ∧
    (sigma x (fineSite (fineSite 0 τ1 τ2) s1 s2)).b2 =
      (if s2 then false else if τ2 then true else x.b2) := by
  simp only [sigma, sigmaPat, phi', subst2_fineSite, Letter.child]
  cases s1 <;> cases s2 <;> cases τ1 <;> cases τ2 <;> simp

theorem mem_sq {n : ℕ} {y : Plane} :
    y ∈ sq n ↔ 0 ≤ y.1 ∧ y.1 < 4 ^ n ∧ 0 ≤ y.2 ∧ y.2 < 4 ^ n := by
  simp [sq, square]

/-- One step of `σ` on patterns: `σ(w)(4d + e) = σ(w(d))(e)` for `e ∈ [0,4)²`. -/
theorem sigmaPat_apply (w : Plane → Letter) (d e : Plane) (he : e ∈ sq 1) :
    sigmaPat w (4 * d.1 + e.1, 4 * d.2 + e.2) = sigma (w d) e := by
  obtain ⟨d1, d2⟩ := d
  obtain ⟨e1, e2⟩ := e
  rw [mem_sq] at he
  simp only [pow_one] at he
  have h1 : (4 * d1 + e1) / 2 / 2 = d1 := by omega
  have h2 : (4 * d2 + e2) / 2 / 2 = d2 := by omega
  have h3 : (4 * d1 + e1) / 2 % 2 = e1 / 2 % 2 := by omega
  have h4 : (4 * d2 + e2) / 2 % 2 = e2 / 2 % 2 := by omega
  have h5 : (4 * d1 + e1) % 2 = e1 % 2 := by omega
  have h6 : (4 * d2 + e2) % 2 = e2 % 2 := by omega
  simp only [sigma, sigmaPat, phi', subst2, h1, h2, h3, h4, h5, h6]

/-- Blockwise substitution is local: `σⁿ(w)(4ⁿ d + y) = σⁿ(w(d))(y)` for `y ∈ [0,4ⁿ)²` (the value
at a site depends only on the letter of `w` at its depth-`n` ancestor). -/
theorem iterate_sigmaPat_block (n : ℕ) (w : Plane → Letter) (d y : Plane) (hy : y ∈ sq n) :
    sigmaPat^[n] w (4 ^ n * d.1 + y.1, 4 ^ n * d.2 + y.2) = sigmaPat^[n] (fun _ => w d) y := by
  induction n generalizing w d y with
  | zero =>
    rw [sq_zero, Set.mem_singleton_iff] at hy
    subst hy
    simp
  | succ n ih =>
    obtain ⟨y1, y2⟩ := y
    rw [mem_sq] at hy
    obtain ⟨hy1, hy1', hy2, hy2'⟩ := hy
    have hN : (0 : ℤ) < 4 ^ n := by positivity
    have hN4 : (4 : ℤ) ^ (n + 1) = 4 * 4 ^ n := by rw [pow_succ]; ring
    rw [hN4] at hy1' hy2'
    -- `y = 4ⁿ e + y'` with `e ∈ [0,4)²` and `y' ∈ [0,4ⁿ)²`
    have he : ((y1 / 4 ^ n, y2 / 4 ^ n) : Plane) ∈ sq 1 := by
      rw [mem_sq, pow_one]
      exact ⟨Int.ediv_nonneg hy1 hN.le, (Int.ediv_lt_iff_lt_mul hN).2 (by linarith),
        Int.ediv_nonneg hy2 hN.le, (Int.ediv_lt_iff_lt_mul hN).2 (by linarith)⟩
    have hy' : ((y1 % 4 ^ n, y2 % 4 ^ n) : Plane) ∈ sq n := by
      rw [mem_sq]
      exact ⟨Int.emod_nonneg _ hN.ne', Int.emod_lt_of_pos _ hN, Int.emod_nonneg _ hN.ne',
        Int.emod_lt_of_pos _ hN⟩
    have hd1 := Int.mul_ediv_add_emod y1 (4 ^ n)
    have hd2 := Int.mul_ediv_add_emod y2 (4 ^ n)
    have hL : ((4 ^ (n + 1) * d.1 + (y1, y2).1, 4 ^ (n + 1) * d.2 + (y1, y2).2) : Plane) =
        (4 ^ n * (4 * d.1 + y1 / 4 ^ n) + y1 % 4 ^ n,
          4 ^ n * (4 * d.2 + y2 / 4 ^ n) + y2 % 4 ^ n) := by
      rw [hN4]; ext <;> simp only <;> linarith
    have hR : ((y1, y2) : Plane) =
        (4 ^ n * (0 + y1 / 4 ^ n) + y1 % 4 ^ n, 4 ^ n * (0 + y2 / 4 ^ n) + y2 % 4 ^ n) := by
      ext <;> simp only <;> linarith
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, hL, hR]
    rw [ih (sigmaPat w) (4 * d.1 + y1 / 4 ^ n, 4 * d.2 + y2 / 4 ^ n) _ hy',
      ih (sigmaPat fun _ => w d) (0 + y1 / 4 ^ n, 0 + y2 / 4 ^ n) _ hy']
    have hS : sigmaPat w (4 * d.1 + y1 / 4 ^ n, 4 * d.2 + y2 / 4 ^ n) =
        sigmaPat (fun _ => w d) (0 + y1 / 4 ^ n, 0 + y2 / 4 ^ n) := by
      rw [sigmaPat_apply w d _ he, zero_add, zero_add]
      rfl
    rw [hS]

/-- `scf:def-ruler`: `σ^{n+1}(𝔞)(4ⁿ d + y) = σⁿ(σ(𝔞)(d))(y)` for `y ∈ [0,4ⁿ)²` (the paper takes
`d ∈ [0,4)²`; the identity holds for every `d`). -/
theorem sigmaPow_succ_apply (n : ℕ) (x : Letter) (d y : Plane) (hy : y ∈ sq n) :
    sigmaPow (n + 1) x (4 ^ n * d.1 + y.1, 4 ^ n * d.2 + y.2) = sigmaPow n (sigma x d) y := by
  rw [sigmaPow, Function.iterate_succ_apply, iterate_sigmaPat_block n _ d y hy]
  rfl

/-- `scf:def-ruler`, the other order: `σ^{n+1}(𝔞) = σ(σⁿ(𝔞))` blockwise. -/
theorem sigmaPow_succ' (n : ℕ) (x : Letter) : sigmaPow (n + 1) x = sigmaPat (sigmaPow n x) :=
  Function.iterate_succ_apply' _ _ _


/-! ## `𝔸` tiles (first claim of `scf:desub`) -/

/-- A tiling of `𝔸` is a map `f : ℤ² → 𝔸`, as a map into letters with every value in `𝔸`, that
matches on every edge (Section 3, "Wang sets"). -/
def IsLetterTiling (f : Plane → Letter) : Prop :=
  (∀ u, (f u).InA) ∧ LegalOn Letter.MatchE Letter.MatchN Set.univ f

theorem two_mul_add_one_le_four_pow (n : ℕ) : 2 * n + 1 ≤ 4 ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ]; omega

/-- **`scf:desub`, first claim: `𝔸` tiles.** As printed ("`φ'^m(𝔞)` is legal on `[0, 2^m)²` for
every `m`"), with `σⁿ = φ'^{2n}` and compactness of `Letter^{ℤ²}` (König's lemma; the forgetting
core's `set:compact` and `fam:tower-exists`, in Tychonoff form). -/
theorem exists_letter_tiling : ∃ f : Plane → Letter, IsLetterTiling f := by
  letI : TopologicalSpace Letter := ⊥
  haveI : DiscreteTopology Letter := ⟨rfl⟩
  let x0 : Letter := ⟨⟨.a, .corner .b, .A⟩, false, false⟩
  have hx0 : x0.InA := by decide
  let S : ℕ → Set Plane := fun n => square (-(n : ℤ), -(n : ℤ)) (2 * n + 1)
  let C : ℕ → Set (Plane → Letter) := fun n =>
    {f | (∀ u ∈ S n, (f u).InA) ∧ LegalOn Letter.MatchE Letter.MatchN (S n) f}
  have hcl1 : ∀ u, IsClosed {f : Plane → Letter | (f u).InA} := by
    intro u
    have hc : Continuous fun f : Plane → Letter => f u := continuous_apply u
    exact (isClosed_discrete {a : Letter | a.InA}).preimage hc
  have hcl2 : ∀ (u v : Plane) (R : Letter → Letter → Prop),
      IsClosed {f : Plane → Letter | R (f u) (f v)} := by
    intro u v R
    have hc : Continuous fun f : Plane → Letter => (f u, f v) :=
      (continuous_apply u).prodMk (continuous_apply v)
    exact (isClosed_discrete {q : Letter × Letter | R q.1 q.2}).preimage hc
  have hclosed : ∀ n, IsClosed (C n) := by
    intro n
    have e : C n = (⋂ u ∈ S n, {f : Plane → Letter | (f u).InA}) ∩
        ((⋂ u ∈ S n, ⋂ (_ : u + (1, 0) ∈ S n),
          {f : Plane → Letter | Letter.MatchE (f u) (f (u + (1, 0)))}) ∩
        (⋂ u ∈ S n, ⋂ (_ : u + (0, 1) ∈ S n),
          {f : Plane → Letter | Letter.MatchN (f u) (f (u + (0, 1)))})) := by
      ext f; simp [C, LegalOn]
    rw [e]
    exact (isClosed_biInter fun u _ => hcl1 u).inter
      ((isClosed_biInter fun u _ => isClosed_iInter fun _ => hcl2 _ _ _).inter
        (isClosed_biInter fun u _ => isClosed_iInter fun _ => hcl2 _ _ _))
  have hsub : ∀ n, S n ⊆ {u | u + ((n : ℤ), (n : ℤ)) ∈ sq n} := by
    intro n u hu
    have h4 : ((2 * n + 1 : ℕ) : ℤ) ≤ ((4 ^ n : ℕ) : ℤ) := by
      exact_mod_cast two_mul_add_one_le_four_pow n
    simp only [S, square, Set.mem_setOf_eq] at hu
    simp only [Set.mem_setOf_eq, mem_sq, Prod.fst_add, Prod.snd_add]
    push_cast at h4 hu
    omega
  have hne : ∀ n, (C n).Nonempty := by
    intro n
    obtain ⟨hA, hL⟩ := sigmaPow_legal hx0 n
    exact ⟨fun u => sigmaPow n x0 (u + ((n : ℤ), (n : ℤ))),
      fun u hu => hA _ (hsub n hu), (hL.translate _).mono (hsub n)⟩
  have hdec : ∀ n, C (n + 1) ⊆ C n := by
    intro n f hf
    have hS : S n ⊆ S (n + 1) := by
      intro u hu
      simp only [S, square, Set.mem_setOf_eq] at hu ⊢
      push_cast at hu ⊢
      omega
    exact ⟨fun u hu => hf.1 u (hS hu), hf.2.mono hS⟩
  obtain ⟨f, hf⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed C hdec hne
    (hclosed 0).isCompact hclosed
  rw [Set.mem_iInter] at hf
  -- every site and its two forward neighbours lie in `S n` for `n = |u₁| + |u₂| + 1`
  have hin : ∀ u : Plane, u ∈ S (u.1.natAbs + u.2.natAbs + 1) ∧
      u + (1, 0) ∈ S (u.1.natAbs + u.2.natAbs + 1) ∧
      u + (0, 1) ∈ S (u.1.natAbs + u.2.natAbs + 1) := by
    intro u
    obtain ⟨u1, u2⟩ := u
    simp only [S, square, Set.mem_setOf_eq, Prod.mk_add_mk]
    push_cast
    have := le_abs_self u1; have := neg_abs_le u1; have := le_abs_self u2; have := neg_abs_le u2
    omega
  refine ⟨f, fun u => (hf _).1 u (hin u).1, fun u _ _ => ?_, fun u _ _ => ?_⟩
  · exact (hf _).2.1 u (hin u).1 (hin u).2.1
  · exact (hf _).2.2 u (hin u).1 (hin u).2.2

end UPD.Scaffold

/-
# Section 5.4: the law of the background (`prop:background`(a), (c))

New in this project.

* `bgMap U τ` (`𝔟_τ`): the background of the construction `cfg U τ σ` (it does not depend on the
  spins, `bgOf_cfg`); **`background_eq`** (`prop:background`(a)): every legal configuration whose
  quarters have typical phase `τ` has background `𝔟_τ`.
* **`measurable_bgMap`**: `τ ↦ 𝔟_τ` is measurable. Each field of `𝔟_τ(ξ)` is built by countable
  operations from the quarters `Y_τ(ξ')` (measurable, `measurable_qtilingOf`) and from frame
  predicates that depend on finitely many digits of `τ` (`MLevel`: every level set is measurable).
* **`bgMap_shift`**: `𝔟_{τ+a} = T_a 𝔟_τ` (by uniqueness and `scf:quarter`).
* `phaseMap` (`ω ↦ τ(ω)`, the quarter phase of `ω`), measurable; **`background_law`**
  (`prop:background`(c)): every translation-invariant probability measure on `X_Φ` has background
  marginal `𝕂`, the image of Haar measure under `τ ↦ 𝔟_τ`, and is concentrated on the
  backgrounds `𝔟_τ` with `τ` typical.
-/
import UndecidablePhaseDiagram.Background.Construct

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace UPD.BG

open UPD.Scaffold

variable {U : Machine}

/-! ## The map `τ ↦ 𝔟_τ` -/

/-- `𝔟_τ`: the background of the construction of `prop:background`(b). -/
def bgMap (U : Machine) (τ : ℕ → Bool × Bool) : Plane → BgVal U :=
  bgOf (cfg U τ fun _ => Spin.plus)

/-- The background of the construction does not depend on the spins. -/
theorem bgOf_cfg (τ : ℕ → Bool × Bool) (σ : Plane → Spin) : bgOf (cfg U τ σ) = bgMap U τ := rfl

/-- **`prop:background`(a)**: every legal configuration whose quarters have typical phase `τ` has
background `𝔟_τ`. -/
theorem background_eq {ω : Config (SiteVal U)} {τ : ℕ → Bool × Bool} (hs : Setting ω τ) :
    bgOf ω = bgMap U τ :=
  hs.background_unique (cfg_setting hs.typical _)

/-! ## Translations -/

/-- Legality is translation invariant. -/
theorem isLegal_shift {ω : Config (SiteVal U)} (h : IsLegal (Phi U) ω) (a : Plane) :
    IsLegal (Phi U) (shift a ω) := by
  intro A
  have e : (A.image fun ξ => ξ - a).image (fun ξ => ξ + a) = A := by
    rw [Finset.image_image]
    convert Finset.image_id (s := A) using 2
    funext ξ; simp
  rw [← e, phi_translationInvariant]
  exact h _

/-- The quarter phase of a translate (`scf:quarter`): `τ(T_a Y) = τ(Y) + a`. -/
theorem isQPhase_shift {Y : Plane → Quarter} {τ : ℕ → Bool × Bool} (hY : IsQTiling Y)
    (h : IsQPhase Y τ) (a : Plane) : IsQPhase (shift a Y) (addDig a τ) := by
  have h' := qphaseOf_spec (hY.shift a)
  have e : qphaseOf (shift a Y) = addDig a τ :=
    eq_of_shift_congr (qphase_shift h a h') (wsum_addDig a τ)
  rw [← e]; exact h'

/-- **`prop:background`(a)**: `𝔟_{τ+a} = T_a 𝔟_τ` (for typical `τ` and `τ + a`). -/
theorem bgMap_shift {τ : ℕ → Bool × Bool} (hτ : Typical τ) (a : Plane)
    (hτ' : Typical (addDig a τ)) : bgMap U (addDig a τ) = shift a (bgMap U τ) := by
  have hs := cfg_setting (U := U) hτ fun _ => Spin.plus
  have hs' : Setting (shift a (cfg U τ fun _ => Spin.plus)) (addDig a τ) :=
    ⟨isLegal_shift hs.legal a, isQPhase_shift (qphase_cfg hτ).1 (qphase_cfg hτ).2 a, hτ'⟩
  rw [← background_eq hs', bgOf_shift]
  rfl

/-- [gap] 10, in the almost-everywhere form of QB's ruling (session 9): for every `a`,
Haar-almost every `τ` has `τ` and `τ + a` typical (Haar measure is invariant under `τ ↦ τ + a`,
`haar_map_addDig`). -/
theorem ae_typical_addDig (a : Plane) : ∀ᵐ τ ∂haar, Typical τ ∧ Typical (addDig a τ) := by
  have h : ∀ᵐ τ ∂haar, Typical (addDig a τ) := by
    have h0 := ae_typical
    rw [← haar_map_addDig a] at h0
    exact ae_of_ae_map (measurable_addDig a).aemeasurable h0
  filter_upwards [ae_typical, h] with τ h1 h2 using ⟨h1, h2⟩

/-- **`prop:background`(a)**, `𝔟_{τ+a} = T_a 𝔟_τ`, for Haar-almost every `τ` (the form in which it
is used; [gap] 10). -/
theorem ae_bgMap_shift (a : Plane) : ∀ᵐ τ ∂haar, bgMap U (addDig a τ) = shift a (bgMap U τ) :=
  (ae_typical_addDig a).mono fun _ h => bgMap_shift h.1 a h.2

/-! ## Level sets -/

section MLevel

variable {Ω : Type} [MeasurableSpace Ω]

/-- Every level set of `f` is measurable (for maps into countable discrete types this is
measurability). -/
def MLevel {α : Type} (f : Ω → α) : Prop := ∀ v, MeasurableSet {ω | f ω = v}

theorem MLevel.of_measurable {α : Type} [MeasurableSpace α] [MeasurableSingletonClass α]
    {f : Ω → α} (hf : Measurable f) : MLevel f := fun v => hf (measurableSet_singleton v)

theorem MLevel.measurableSet {α : Type} [Countable α] {f : Ω → α} (hf : MLevel f)
    (P : α → Prop) : MeasurableSet {ω | P (f ω)} := by
  have e : {ω | P (f ω)} = ⋃ v ∈ {v | P v}, {ω | f ω = v} := by ext; simp
  rw [e]; exact MeasurableSet.biUnion (Set.to_countable _) fun v _ => hf v

theorem MLevel.comp {α β : Type} [Countable α] {f : Ω → α} (hf : MLevel f) (g : α → β) :
    MLevel (fun ω => g (f ω)) := fun w => hf.measurableSet (fun v => g v = w)

theorem MLevel.prod {α β : Type} {f : Ω → α} {g : Ω → β} (hf : MLevel f) (hg : MLevel g) :
    MLevel (fun ω => (f ω, g ω)) := fun v => by
  have e : {ω | (f ω, g ω) = v} = {ω | f ω = v.1} ∩ {ω | g ω = v.2} := by
    ext; simp [Prod.ext_iff]
  rw [e]; exact (hf _).inter (hg _)

theorem MLevel.ite {α : Type} {P : Ω → Prop} [∀ ω, Decidable (P ω)]
    (hP : MeasurableSet {ω | P ω}) {f g : Ω → α} (hf : MLevel f) (hg : MLevel g) :
    MLevel (fun ω => if P ω then f ω else g ω) := fun v => by
  have e : {ω | (if P ω then f ω else g ω) = v} =
      ({ω | P ω} ∩ {ω | f ω = v}) ∪ ({ω | P ω}ᶜ ∩ {ω | g ω = v}) := by
    ext ω; by_cases h : P ω <;> simp [h]
  rw [e]; exact (hP.inter (hf v)).union (hP.compl.inter (hg v))

theorem MLevel.dep {κ α : Type} [Countable κ] {n : Ω → κ} (hn : MLevel n) {F : κ → Ω → α}
    (hF : ∀ k, MLevel (F k)) : MLevel (fun ω => F (n ω) ω) := fun v => by
  have e : {ω | F (n ω) ω = v} = ⋃ k, {ω | n ω = k} ∩ {ω | F k ω = v} := by ext ω; simp
  rw [e]; exact MeasurableSet.iUnion fun k => (hn k).inter (hF k v)

theorem MLevel.const {α : Type} (a : α) : MLevel (fun _ : Ω => a) := fun v => by
  by_cases h : a = v <;> simp [h]

theorem MLevel.decide {P : Ω → Prop} [∀ ω, Decidable (P ω)] (hP : MeasurableSet {ω | P ω}) :
    MLevel (fun ω => decide (P ω)) := by
  have := MLevel.ite (α := Bool) hP (MLevel.const true) (MLevel.const false)
  convert this using 2 with ω
  by_cases h : P ω <;> simp [h]

theorem MLevel.wdL {S : Type} {W : Ω → ℤ → Option S} (hW : ∀ x, MLevel fun ω => W ω x) (z : ℤ) :
    MLevel (fun ω => UPD.BG.wdL (W ω) z) := by
  classical
  intro n
  have e : {ω | UPD.BG.wdL (W ω) z = n} =
      ({ω | W ω (z - n) = none}ᶜ ∩ ⋂ k : Fin n, {ω | W ω (z - k) = none}) ∪
        ((⋂ k : ℕ, {ω | W ω (z - k) = none}) ∩ {_ω | n = 0}) := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_inter_iff, Set.mem_iInter,
      Set.mem_compl_iff]
    constructor
    · intro h
      by_cases hex : ∃ k : ℕ, W ω (z - k) ≠ none
      · left
        obtain ⟨h1, h2⟩ := wdL_spec hex
        rw [h] at h1 h2
        exact ⟨h1, fun k => h2 k k.2⟩
      · right
        push Not at hex
        refine ⟨hex, ?_⟩
        rw [← h, UPD.BG.wdL, dif_neg (by push Not; exact hex)]
    · rintro (⟨h1, h2⟩ | ⟨h1, rfl⟩)
      · exact wdL_eq h1 fun k hk => h2 ⟨k, hk⟩
      · rw [UPD.BG.wdL, dif_neg (by push Not; exact h1)]
  rw [e]
  refine ((hW _ none).compl.inter (MeasurableSet.iInter fun k => hW _ none)).union
    ((MeasurableSet.iInter fun k => hW _ none).inter ?_)
  by_cases h : n = 0 <;> simp [h]

theorem MLevel.wdR {S : Type} {W : Ω → ℤ → Option S} (hW : ∀ x, MLevel fun ω => W ω x) (z : ℤ) :
    MLevel (fun ω => UPD.BG.wdR (W ω) z) := by
  classical
  intro n
  have e : {ω | UPD.BG.wdR (W ω) z = n} =
      ({ω | W ω (z + 1 + n) = none}ᶜ ∩ ⋂ k : Fin n, {ω | W ω (z + 1 + k) = none}) ∪
        ((⋂ k : ℕ, {ω | W ω (z + 1 + k) = none}) ∩ {_ω | n = 0}) := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_inter_iff, Set.mem_iInter,
      Set.mem_compl_iff]
    constructor
    · intro h
      by_cases hex : ∃ k : ℕ, W ω (z + 1 + k) ≠ none
      · left
        obtain ⟨h1, h2⟩ := wdR_spec hex
        rw [h] at h1 h2
        exact ⟨h1, fun k => h2 k k.2⟩
      · right
        push Not at hex
        refine ⟨hex, ?_⟩
        rw [← h, UPD.BG.wdR, dif_neg (by push Not; exact hex)]
    · rintro (⟨h1, h2⟩ | ⟨h1, rfl⟩)
      · exact wdR_eq h1 fun k hk => h2 ⟨k, hk⟩
      · rw [UPD.BG.wdR, dif_neg (by push Not; exact h1)]
  rw [e]
  refine ((hW _ none).compl.inter (MeasurableSet.iInter fun k => hW _ none)).union
    ((MeasurableSet.iInter fun k => hW _ none).inter ?_)
  by_cases h : n = 0 <;> simp [h]

theorem MLevel.wtag {S : Type} [Countable S] {W : Ω → ℤ → Option S}
    (hW : ∀ x, MLevel fun ω => W ω x) (dflt : S) (z : ℤ) :
    MLevel (fun ω => UPD.BG.wtag (W ω) dflt z) := by
  unfold UPD.BG.wtag
  refine MLevel.prod ?_ ?_
  · exact MLevel.dep (MLevel.wdL hW z) (F := fun k ω => (W ω (z - k)).getD dflt)
      fun k => (hW (z - k)).comp (fun o => o.getD dflt)
  · exact MLevel.dep (MLevel.wdR hW z) (F := fun k ω => (W ω (z + 1 + k)).getD dflt)
      fun k => (hW (z + 1 + k)).comp (fun o => o.getD dflt)

theorem MLevel.evTag {S : Type} [Countable S] {W : Ω → ℤ → Option S}
    (hW : ∀ x, MLevel fun ω => W ω x) (L R : S) {act : Ω → ℤ → Prop}
    (hact : ∀ x, MeasurableSet {ω | act ω x}) (z : ℤ) :
    MLevel (fun ω => UPD.BG.evTag (W ω) L R (act ω) z) := by
  classical
  unfold UPD.BG.evTag
  have hl := MLevel.wdL hW z
  have hr := MLevel.wdR hW z
  have h1 : MeasurableSet {ω | ∃ x, z - (UPD.BG.wdL (W ω) z : ℤ) < x ∧ x ≤ z ∧ act ω x} := by
    have e : {ω | ∃ x, z - (UPD.BG.wdL (W ω) z : ℤ) < x ∧ x ≤ z ∧ act ω x} =
        ⋃ x : ℤ, ({ω | z - (UPD.BG.wdL (W ω) z : ℤ) < x} ∩ {_ω | x ≤ z} ∩ {ω | act ω x}) := by
      ext ω; simp [and_assoc]
    rw [e]
    refine MeasurableSet.iUnion fun x => ((hl.measurableSet (fun n => z - (n : ℤ) < x)).inter ?_).inter
      (hact x)
    by_cases h : x ≤ z <;> simp [h]
  have h2 : MeasurableSet {ω | ∃ x, z < x ∧ x < z + 1 + (UPD.BG.wdR (W ω) z : ℤ) ∧ act ω x} := by
    have e : {ω | ∃ x, z < x ∧ x < z + 1 + (UPD.BG.wdR (W ω) z : ℤ) ∧ act ω x} =
        ⋃ x : ℤ, ({_ω | z < x} ∩ {ω | x < z + 1 + (UPD.BG.wdR (W ω) z : ℤ)} ∩ {ω | act ω x}) := by
      ext ω; simp [and_assoc]
    rw [e]
    refine MeasurableSet.iUnion fun x => (MeasurableSet.inter ?_
      (hr.measurableSet (fun n => x < z + 1 + (n : ℤ)))).inter (hact x)
    by_cases h : z < x <;> simp [h]
  refine MLevel.ite ((MLevel.wtag hW L z) (L, R)) ?_ (MLevel.const _)
  exact (MLevel.prod (MLevel.ite h1 (MLevel.const _) (MLevel.const _))
    (MLevel.ite h2 (MLevel.const _) (MLevel.const _))).comp some

end MLevel

/-! ## Frame predicates depend on finitely many digits -/

theorem measurableSet_prefix (n : ℕ) (P : (ℕ → Bool × Bool) → Prop)
    (hP : ∀ x y, (∀ m < n, x m = y m) → P x → P y) : MeasurableSet {x | P x} := by
  classical
  have hm := measurable_of_prefix (B := Bool × Bool) n (fun x => decide (P x)) (fun x y h => by
    have h' : ∀ m < n, y m = x m := fun m hm => (h m hm).symm
    exact decide_eq_decide.2 ⟨hP x y h, hP y x h'⟩)
  have e : {x | P x} = (fun x => decide (P x)) ⁻¹' {true} := by ext; simp
  rw [e]; exact hm (measurableSet_singleton _)

theorem a1_congr {τ τ' : ℕ → Bool × Bool} {D : ℕ} (h : ∀ m < 2 * D + 2, τ m = τ' m) {e : ℕ}
    (he : e ≤ D) : a1 τ e = a1 τ' e :=
  wsum_congr fun m hm => by simp only [col]; rw [h m (by omega)]

theorem a2_congr {τ τ' : ℕ → Bool × Bool} {D : ℕ} (h : ∀ m < 2 * D + 2, τ m = τ' m) {e : ℕ}
    (he : e ≤ D) : a2 τ e = a2 τ' e :=
  wsum_congr fun m hm => by simp only [row]; rw [h m (by omega)]

theorem inFrame_congr {a a' : ℕ → ℤ} {e : ℕ} (h : a e = a' e) (z : ℤ) :
    InFrame a e z ↔ InFrame a' e z := by
  simp only [InFrame, frameLo, frameHi, h]

theorem isFree_congr {a a' : ℕ → ℤ} {d : ℕ} (h : ∀ e ≤ d, a e = a' e) (m z : ℤ) :
    IsFree a d m z ↔ IsFree a' d m z := by
  simp only [IsFree, frameLo, frameHi, h d le_rfl]
  constructor <;> rintro ⟨h1, h2, h3⟩ <;> refine ⟨h1, h2, fun e he hed => ?_⟩
  · rw [← inFrame_congr (h e hed.le)]; exact h3 e he hed
  · rw [inFrame_congr (h e hed.le)]; exact h3 e he hed

theorem freeSet_congr {a a' : ℕ → ℤ} {d : ℕ} (h : ∀ e ≤ d, a e = a' e) (m : ℤ) :
    freeSet a d m = freeSet a' d m := by
  classical
  unfold freeSet
  rw [show frameLo a d m = frameLo a' d m by simp [frameLo, h d le_rfl],
    show frameHi a d m = frameHi a' d m by simp [frameHi, h d le_rfl]]
  exact Finset.filter_congr fun z _ => isFree_congr h m z

theorem zeta_congr {a a' : ℕ → ℤ} {d : ℕ} (h : ∀ e ≤ d, a e = a' e) (m : ℤ) (i : ℕ) :
    zeta a d m i = zeta a' d m i := by
  have key : ∀ s t : Finset ℤ, s = t →
      (if h : i < s.card then s.orderEmbOfFin rfl ⟨i, h⟩ else 0) =
        (if h : i < t.card then t.orderEmbOfFin rfl ⟨i, h⟩ else 0) := by
    rintro s t rfl; rfl
  unfold zeta
  exact key _ _ (freeSet_congr h m)

theorem rfree_congr {a a' : ℕ → ℤ} {d : ℕ} (h : a d = a' d) (m : ℤ) : rfree a d m = rfree a' d m := by
  simp [rfree, frameLo, h]

/-! ## Measurability of the fields of `𝔟_τ` -/

section Fields

theorem mlevel_qtiling (ξ : Plane) : MLevel (fun τ : ℕ → Bool × Bool => qtilingOf τ ξ) :=
  MLevel.of_measurable ((measurable_pi_apply ξ).comp measurable_qtilingOf)

theorem mlevel_rowW (y z : ℤ) : MLevel (fun τ => rowW τ y z) :=
  (mlevel_qtiling (z, y)).comp _

theorem mlevel_colW (x z : ℤ) : MLevel (fun τ => colW τ x z) :=
  (mlevel_qtiling (x, z)).comp _

theorem measurableSet_actF (ξ : Plane) : MeasurableSet {τ | actF τ ξ} := by
  have e : {τ | actF τ ξ} = ⋃ (d : ℕ) (m1 : ℤ) (m2 : ℤ),
      {τ | 1 ≤ d ∧ IsFree (a1 τ) d m1 ξ.1 ∧ IsFree (a2 τ) d m2 ξ.2} := by
    ext τ; simp [actF]
  rw [e]
  refine MeasurableSet.iUnion fun d => MeasurableSet.iUnion fun m1 => MeasurableSet.iUnion
    fun m2 => measurableSet_prefix (2 * d + 2) _ fun x y h hx => ?_
  obtain ⟨hd, h1, h2⟩ := hx
  exact ⟨hd, (isFree_congr (fun e he => a1_congr h he) m1 _).1 h1,
    (isFree_congr (fun e he => a2_congr h he) m2 _).1 h2⟩

theorem mlevel_oEc (ξ : Plane) : MLevel (fun τ => oEc τ ξ) :=
  MLevel.wtag (fun x => mlevel_rowW ξ.2 x) _ _

theorem mlevel_oNc (ξ : Plane) : MLevel (fun τ => oNc τ ξ) :=
  MLevel.wtag (fun x => mlevel_colW ξ.1 x) _ _

theorem mlevel_eEc (ξ : Plane) : MLevel (fun τ => eEc τ ξ) :=
  MLevel.evTag (fun x => mlevel_rowW ξ.2 x) _ _ (act := fun τ x => actF τ (x, ξ.2))
    (fun x => measurableSet_actF (x, ξ.2)) _

theorem mlevel_eNc (ξ : Plane) : MLevel (fun τ => eNc τ ξ) :=
  MLevel.evTag (fun x => mlevel_colW ξ.1 x) _ _ (act := fun τ z => actF τ (ξ.1, z))
    (fun z => measurableSet_actF (ξ.1, z)) _

theorem measurableSet_HSeg (p : ℕ × ℕ × ℕ) (ξ : Plane) : MeasurableSet {τ | HSeg τ p ξ} := by
  have e : {τ | HSeg τ p ξ} = ⋃ (m1 : ℤ) (m2 : ℤ), {τ | 1 ≤ p.1 ∧ p.2.1 + 1 < MachineM.Nd p.1 ∧
      p.2.2 < MachineM.Nd p.1 ∧ ξ.2 = zeta (a2 τ) p.1 m2 p.2.2 ∧
      zeta (a1 τ) p.1 m1 p.2.1 ≤ ξ.1 ∧ ξ.1 < zeta (a1 τ) p.1 m1 (p.2.1 + 1)} := by
    ext τ; simp only [HSeg, Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨h1, h2, h3, m1, m2, h4⟩; exact ⟨m1, m2, h1, h2, h3, h4⟩
    · rintro ⟨m1, m2, h1, h2, h3, h4⟩; exact ⟨h1, h2, h3, m1, m2, h4⟩
  rw [e]
  refine MeasurableSet.iUnion fun m1 => MeasurableSet.iUnion fun m2 =>
    measurableSet_prefix (2 * p.1 + 2) _ fun x y h hx => ?_
  have z1 := zeta_congr (fun e he => a1_congr h he) m1
  have z2 := zeta_congr (fun e he => a2_congr h he) m2
  rw [z1, z1, z2] at hx
  exact hx

theorem measurableSet_VSeg (p : ℕ × ℕ × ℕ) (ξ : Plane) : MeasurableSet {τ | VSeg τ p ξ} := by
  have e : {τ | VSeg τ p ξ} = ⋃ (m1 : ℤ) (m2 : ℤ), {τ | 1 ≤ p.1 ∧ p.2.1 < MachineM.Nd p.1 ∧
      p.2.2 + 1 < MachineM.Nd p.1 ∧ ξ.1 = zeta (a1 τ) p.1 m1 p.2.1 ∧
      zeta (a2 τ) p.1 m2 p.2.2 ≤ ξ.2 ∧ ξ.2 < zeta (a2 τ) p.1 m2 (p.2.2 + 1)} := by
    ext τ; simp only [VSeg, Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨h1, h2, h3, m1, m2, h4⟩; exact ⟨m1, m2, h1, h2, h3, h4⟩
    · rintro ⟨m1, m2, h1, h2, h3, h4⟩; exact ⟨h1, h2, h3, m1, m2, h4⟩
  rw [e]
  refine MeasurableSet.iUnion fun m1 => MeasurableSet.iUnion fun m2 =>
    measurableSet_prefix (2 * p.1 + 2) _ fun x y h hx => ?_
  have z1 := zeta_congr (fun e he => a1_congr h he) m1
  have z2 := zeta_congr (fun e he => a2_congr h he) m2
  rw [z1, z2, z2] at hx
  exact hx

theorem measurableSet_GPos (p : ℕ × ℕ × ℕ) (ξ : Plane) : MeasurableSet {τ | GPos τ p ξ} := by
  have e : {τ | GPos τ p ξ} = ⋃ (m1 : ℤ) (m2 : ℤ), {τ | 1 ≤ p.1 ∧ p.2.1 < MachineM.Nd p.1 ∧
      p.2.2 < MachineM.Nd p.1 ∧ ξ = gsite τ p.1 m1 m2 p.2.1 p.2.2} := by
    ext τ; simp only [GPos, Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨h1, h2, h3, m1, m2, h4⟩; exact ⟨m1, m2, h1, h2, h3, h4⟩
    · rintro ⟨m1, m2, h1, h2, h3, h4⟩; exact ⟨h1, h2, h3, m1, m2, h4⟩
  rw [e]
  refine MeasurableSet.iUnion fun m1 => MeasurableSet.iUnion fun m2 =>
    measurableSet_prefix (2 * p.1 + 2) _ fun x y h hx => ?_
  have z1 := zeta_congr (fun e he => a1_congr h he) m1
  have z2 := zeta_congr (fun e he => a2_congr h he) m2
  simp only [gsite] at hx ⊢
  rw [z1, z2] at hx
  exact hx

/-- A choice-defined field is measurable when its defining predicate has measurable level sets
and determines the witness (`HSeg_unique` etc.). -/
theorem mlevel_choose {α : Type} {P : (ℕ → Bool × Bool) → ℕ × ℕ × ℕ → Prop}
    (hP : ∀ p, MeasurableSet {τ | P τ p})
    (F : ℕ × ℕ × ℕ → α) (dflt : α) {f : (ℕ → Bool × Bool) → α}
    (hf : ∀ τ, (∀ p, P τ p → f τ = F p) ∧ ((¬ ∃ p, P τ p) → f τ = dflt)) : MLevel f := by
  intro v
  have e : {τ | f τ = v} = (⋃ p ∈ {p | F p = v}, {τ | P τ p}) ∪
      ({τ | ∃ p, P τ p}ᶜ ∩ {_τ | dflt = v}) := by
    ext τ
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_compl_iff, exists_prop]
    constructor
    · intro h
      by_cases hex : ∃ p, P τ p
      · obtain ⟨p, hp⟩ := hex; exact Or.inl ⟨p, by rw [← (hf τ).1 p hp, h], hp⟩
      · exact Or.inr ⟨hex, by rw [← (hf τ).2 hex, h]⟩
    · rintro (⟨p, hFp, hp⟩ | ⟨hex, hd⟩)
      · rw [(hf τ).1 p hp, hFp]
      · rw [(hf τ).2 hex, hd]
  have hex : MeasurableSet {τ | ∃ p, P τ p} := by
    have e' : {τ | ∃ p, P τ p} = ⋃ p, {τ | P τ p} := by ext; simp
    rw [e']; exact MeasurableSet.iUnion hP
  rw [e]
  refine (MeasurableSet.biUnion (Set.to_countable _) fun p _ => hP p).union (hex.compl.inter ?_)
  by_cases h : dflt = v <;> simp [h]

theorem mlevel_lEc (ξ : Plane) : MLevel (fun τ => lEc U τ ξ) :=
  mlevel_choose (fun p => measurableSet_HSeg p ξ)
    (fun p => some (hcolFormula U p.1 p.2.1 p.2.2)) none
    fun _ => ⟨fun _ hp => lEc_of U hp, fun h => lEc_none U h⟩

theorem mlevel_lNc (ξ : Plane) : MLevel (fun τ => lNc U τ ξ) :=
  mlevel_choose (fun p => measurableSet_VSeg p ξ)
    (fun p => some ((vcolFormula U p.1 p.2.1 p.2.2).withX fun _ => false)) none
    fun _ => ⟨fun _ hp => lNc_of U hp, fun h => lNc_none U h⟩

theorem mlevel_kF (ξ : Plane) : MLevel (fun τ => kF U τ ξ) :=
  mlevel_choose (fun p => measurableSet_GPos p ξ)
    (fun p => some ((cellFormula U p.1 p.2.1 p.2.2).withXY (fun _ => false) fun _ => false)) none
    fun _ => ⟨fun _ hp => kF_of U hp, fun h => kF_none U h⟩

theorem mlevel_rowMc (ξ : Plane) : MLevel (fun τ => rowMc τ ξ) := by
  classical
  unfold rowMc
  refine MLevel.decide ?_
  have e : {τ | ∃ d m, 1 ≤ d ∧ ξ.2 = rfree (a2 τ) d m} =
      ⋃ (d : ℕ) (m : ℤ), {τ | 1 ≤ d ∧ ξ.2 = rfree (a2 τ) d m} := by ext; simp
  rw [e]
  exact MeasurableSet.iUnion fun d => MeasurableSet.iUnion fun m =>
    measurableSet_prefix (2 * d + 2) _ fun x y h hx => by
      rw [rfree_congr (a2_congr h le_rfl) m] at hx; exact hx

theorem mlevel_colMc (ξ : Plane) : MLevel (fun τ => colMc τ ξ) := by
  classical
  unfold colMc
  refine MLevel.decide ?_
  have e : {τ | ∃ d m, 1 ≤ d ∧ ξ.1 = rfree (a1 τ) d m} =
      ⋃ (d : ℕ) (m : ℤ), {τ | 1 ≤ d ∧ ξ.1 = rfree (a1 τ) d m} := by ext; simp
  rw [e]
  exact MeasurableSet.iUnion fun d => MeasurableSet.iUnion fun m =>
    measurableSet_prefix (2 * d + 2) _ fun x y h hx => by
      rw [rfree_congr (a1_congr h le_rfl) m] at hx; exact hx

end Fields

/-! ## `τ ↦ 𝔟_τ` is measurable -/

instance : MeasurableSpace (BgVal U) := ⊤

instance : MeasurableSingletonClass (BgVal U) := ⟨fun _ => trivial⟩

/-- A fixed payload value (used to embed background values into site values). -/
def payZero : PayVal :=
  ⟨.plus, none, none, none, none, fun _ => false, fun _ => false, fun _ => false, fun _ => false⟩

instance : Countable (BgVal U) :=
  Function.Injective.countable (f := fun b : BgVal U => merge b payZero) fun b b' h => by
    have := congrArg bgPart h; rwa [bgPart_merge, bgPart_merge] at this

theorem mlevel_bgMap (ξ : Plane) : MLevel (fun τ => bgMap U τ ξ) := by
  intro v
  obtain ⟨q, oW, oE, oS, oN, eW, eE, eS, eN, lW, lE, lS, lN, k, rM, cM⟩ := v
  have e : {τ | bgMap U τ ξ = ⟨q, oW, oE, oS, oN, eW, eE, eS, eN, lW, lE, lS, lN, k, rM, cM⟩} =
      {τ | qtilingOf τ ξ = q} ∩ {τ | oEc τ (ξ.1 - 1, ξ.2) = oW} ∩ {τ | oEc τ ξ = oE} ∩
      {τ | oNc τ (ξ.1, ξ.2 - 1) = oS} ∩ {τ | oNc τ ξ = oN} ∩ {τ | eEc τ (ξ.1 - 1, ξ.2) = eW} ∩
      {τ | eEc τ ξ = eE} ∩ {τ | eNc τ (ξ.1, ξ.2 - 1) = eS} ∩ {τ | eNc τ ξ = eN} ∩
      {τ | lEc U τ (ξ.1 - 1, ξ.2) = lW} ∩ {τ | lEc U τ ξ = lE} ∩
      {τ | (lNc U τ (ξ.1, ξ.2 - 1)).map VCol.bg = lS} ∩ {τ | (lNc U τ ξ).map VCol.bg = lN} ∩
      {τ | (kF U τ ξ).map CellRec.bg = k} ∩ {τ | rowMc τ ξ = rM} ∩ {τ | colMc τ ξ = cM} := by
    ext τ
    simp only [bgMap, bgOf, bgPart, cfg, BgVal.mk.injEq, Set.mem_setOf_eq, Set.mem_inter_iff]
    tauto
  rw [e]
  exact ((((((((((((((((mlevel_qtiling ξ q).inter (mlevel_oEc _ oW)).inter (mlevel_oEc ξ oE)).inter
    (mlevel_oNc _ oS)).inter (mlevel_oNc ξ oN)).inter (mlevel_eEc _ eW)).inter (mlevel_eEc ξ eE)).inter
    (mlevel_eNc _ eS)).inter (mlevel_eNc ξ eN)).inter (mlevel_lEc _ lW)).inter (mlevel_lEc ξ lE)).inter
    ((mlevel_lNc _).comp _ lS)).inter ((mlevel_lNc ξ).comp _ lN)).inter
    ((mlevel_kF ξ).comp _ k)).inter (mlevel_rowMc ξ rM)).inter (mlevel_colMc ξ cM))

/-- **`prop:background`(a)**: `τ ↦ 𝔟_τ` is measurable. -/
theorem measurable_bgMap : Measurable (bgMap U) :=
  Measurable.of_eval fun ξ => measurable_to_countable' fun v => mlevel_bgMap ξ v

/-! ## `prop:background`(c): the law of the background -/

/-- The quarters of a configuration. -/
def quartersOf (ω : Config (SiteVal U)) : Plane → Quarter := fun ξ => (ω ξ).q

/-- The quarter phase `τ(ω)` of a configuration (`0` if its quarters are not a tiling). -/
def phaseMap (ω : Config (SiteVal U)) : ℕ → Bool × Bool := qphaseOf (quartersOf ω)

theorem measurable_quartersOf : Measurable (quartersOf (U := U)) :=
  Measurable.of_eval fun ξ => (measurable_from_top (f := fun s : SiteVal U => s.q)).comp
    (measurable_pi_apply ξ)

theorem measurable_phaseMap : Measurable (phaseMap (U := U)) :=
  measurable_qphaseOf.comp measurable_quartersOf

theorem measurable_bgOf : Measurable (bgOf (U := U)) :=
  Measurable.of_eval fun ξ => (measurable_from_top (f := fun s : SiteVal U => bgPart s)).comp
    (measurable_pi_apply ξ)

theorem quartersOf_shift (a : Plane) (ω : Config (SiteVal U)) :
    quartersOf (shift a ω) = shift a (quartersOf ω) := rfl

/-- A legal configuration with typical quarter phase is in the setting of Section 5, with its
own phase. -/
theorem setting_phaseMap {ω : Config (SiteVal U)} (h : IsLegal (Phi U) ω)
    (ht : Typical (phaseMap ω)) : Setting ω (phaseMap ω) :=
  ⟨h, qphaseOf_spec (isQTiling_of_legal h), ht⟩

section Law

variable {μ : Measure (Config (SiteVal U))} [IsProbabilityMeasure μ]
  (hleg : μ {ω | IsLegal (Phi U) ω} = 1) (hti : ∀ a : Plane, μ.map (shift a) = μ)
include hleg

theorem ae_legal : ∀ᵐ ω ∂μ, IsLegal (Phi U) ω :=
  (ae_iff_measure_eq (Gibbs.measurableSet_legal phi_isInteraction).nullMeasurableSet).2 (by rw [hleg, measure_univ])

include hti

/-- The quarter marginal of a translation-invariant probability measure on `X_Φ` is a
translation-invariant law of `𝔸^q`. -/
theorem isTILaw_quarters : IsTILaw {Y : Plane → Quarter | IsQTiling Y} (μ.map quartersOf) := by
  have hm := measurable_quartersOf (U := U)
  refine ⟨(Measure.isProbabilityMeasure_map_iff hm.aemeasurable).2 inferInstance, ?_, fun a => ?_⟩
  · rw [Measure.map_apply hm measurableSet_qTilings]
    refine le_antisymm prob_le_one ?_
    rw [← hleg]
    exact measure_mono fun ω hω => isQTiling_of_legal hω
  · rw [Measure.map_map (measurable_shift a) hm]
    have e : shift a ∘ quartersOf = quartersOf ∘ (shift a : Config (SiteVal U) → _) := rfl
    rw [e, ← Measure.map_map hm (measurable_shift a), hti a]

/-- Under a translation-invariant probability measure on `X_Φ` the quarter phase is Haar
distributed. -/
theorem map_phaseMap : μ.map phaseMap = haar := by
  rw [show (phaseMap : Config (SiteVal U) → _) = qphaseOf ∘ quartersOf from rfl,
    ← Measure.map_map measurable_qphaseOf measurable_quartersOf]
  exact quarter_phase_haar (isTILaw_quarters hleg hti)

theorem ae_typical_phaseMap : ∀ᵐ ω ∂μ, Typical (phaseMap ω) := by
  have h := quarter_phase_typical (isTILaw_quarters hleg hti)
  exact ae_of_ae_map measurable_quartersOf.aemeasurable h

/-- `μ`-almost every configuration is legal, has a typical quarter phase, and has background
`𝔟_{τ(ω)}`. -/
theorem ae_bgOf : ∀ᵐ ω ∂μ, Setting ω (phaseMap ω) ∧ bgOf ω = bgMap U (phaseMap ω) := by
  filter_upwards [ae_legal hleg, ae_typical_phaseMap hleg hti] with ω h1 h2
  have hs := setting_phaseMap h1 h2
  exact ⟨hs, background_eq hs⟩

/-- **`prop:background`(c)**: every translation-invariant probability measure on `X_Φ` has the
background marginal `𝕂`, the image of Haar measure under `τ ↦ 𝔟_τ`, and it is concentrated on the
backgrounds `𝔟_τ` with `τ` typical. -/
theorem background_law :
    μ.map bgOf = haar.map (bgMap U) ∧
      ∀ᵐ ω ∂μ, ∃ τ, Typical τ ∧ bgOf ω = bgMap U τ := by
  refine ⟨?_, (ae_bgOf hleg hti).mono fun ω h => ⟨_, h.1.typical, h.2⟩⟩
  rw [Measure.map_congr ((ae_bgOf hleg hti).mono fun ω h => h.2),
    ← map_phaseMap hleg hti, Measure.map_map measurable_bgMap measurable_phaseMap]
  rfl

end Law

end UPD.BG

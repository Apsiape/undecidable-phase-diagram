/-
# Appendix A: counts of the scaffold tables

Ported from the forgetting core (`C:/Infanox/fixed-noise-ergodicity-lean`,
`FixedNoiseErgodicity/Scaffold/Tables.lean`, same authors), onto the definitions of
`Statements.lean`:
* explicit enumeration lists (`all`) of the atoms and types, of the 400 triples and of the 1600
  tuples; the base set `𝕆` has 104 triples (`tab:alphabet`), the scaffold `𝔸` has 276 letters
  (`tab:letters`), the quarter set `𝔸^q` has `4 · 276 = 1104` quarters (`tab:fields`);
* on each axis the red endpoints of a thick type carry at most one atom value (the remark after
  `scf:def-walls`; it makes the reading order of `Thick.vRedAtom`, `Thick.hRedAtom` immaterial).
Kernel checks are `decide +kernel` on linear Boolean computations over the explicit lists (as in
the forgetting core: a few seconds, well under 1 GB).
-/
import UndecidablePhaseDiagram.Statements

set_option autoImplicit false

-- The kernel checks below walk lists of up to 1600 entries.
set_option maxRecDepth 20000

namespace UPD.Scaffold

/-- A `flatMap` of a duplicate-free list is duplicate-free if each block is, and every entry of
the block of `a` remembers `a` (forgetting core, `nodup_flatMap_of_key`). -/
theorem nodup_flatMap_of_key {α β : Type*} {l : List α} {f : α → List β} (key : β → α)
    (hl : l.Nodup) (hf : ∀ a ∈ l, (f a).Nodup) (hkey : ∀ a, ∀ b ∈ f a, key b = a) :
    (l.flatMap f).Nodup :=
  List.nodup_flatMap.2 ⟨hf, hl.imp fun {a a'} hne b hb hb' =>
    hne ((hkey a b hb).symm.trans (hkey a' b hb'))⟩

/-! ## Enumeration lists -/

/-- All vertical atoms. -/
def VAtom.all : List VAtom := [.r0, .r2, .g0, .g2]
/-- All horizontal atoms. -/
def HAtom.all : List HAtom := [.r1, .r3, .g1, .g3]
/-- All thin types. -/
def Thin.all : List Thin := [.a, .b, .c, .d]
/-- All corners. -/
def Corner.all : List Corner := [.a, .b, .c, .d]
/-- All black types. -/
def Black.all : List Black := [.A, .B, .C, .D, .E]
/-- All thick types: the four corners, then the sixteen lines. -/
def Thick.all : List Thick :=
  Corner.all.map .corner ++ VAtom.all.flatMap fun α => HAtom.all.map (.line α)

theorem VAtom.mem_all (x : VAtom) : x ∈ VAtom.all := by cases x <;> decide
theorem HAtom.mem_all (x : HAtom) : x ∈ HAtom.all := by cases x <;> decide
theorem Thin.mem_all (x : Thin) : x ∈ Thin.all := by cases x <;> decide
theorem Corner.mem_all (x : Corner) : x ∈ Corner.all := by cases x <;> decide
theorem Black.mem_all (x : Black) : x ∈ Black.all := by cases x <;> decide

theorem Thick.mem_all (x : Thick) : x ∈ Thick.all := by
  cases x with
  | corner k => exact List.mem_append_left _ (List.mem_map_of_mem (Corner.mem_all k))
  | line α γ =>
    exact List.mem_append_right _
      (List.mem_flatMap.2 ⟨α, VAtom.mem_all α, List.mem_map_of_mem (HAtom.mem_all γ)⟩)

theorem Thin.all_nodup : Thin.all.Nodup := by decide
theorem Thick.all_nodup : Thick.all.Nodup := by decide
theorem Black.all_nodup : Black.all.Nodup := by decide

/-- All 400 triples (thin, then thick, then black). -/
def Formal.all : List Formal :=
  Thin.all.flatMap fun θ => Thick.all.flatMap fun κ => Black.all.map fun ψ => ⟨θ, κ, ψ⟩

theorem Formal.mem_all (t : Formal) : t ∈ Formal.all := by
  obtain ⟨θ, κ, ψ⟩ := t
  exact List.mem_flatMap.2 ⟨θ, Thin.mem_all θ, List.mem_flatMap.2
    ⟨κ, Thick.mem_all κ, List.mem_map_of_mem (Black.mem_all ψ)⟩⟩

theorem Formal.all_nodup : Formal.all.Nodup :=
  nodup_flatMap_of_key Formal.thin Thin.all_nodup
    (fun θ _ => nodup_flatMap_of_key Formal.thick Thick.all_nodup
      (fun κ _ => Black.all_nodup.map fun _ _ h => by cases h; rfl)
      (fun κ t ht => by obtain ⟨ψ, -, rfl⟩ := List.mem_map.1 ht; rfl))
    (fun θ t ht => by
      obtain ⟨κ, -, ht⟩ := List.mem_flatMap.1 ht
      obtain ⟨ψ, -, rfl⟩ := List.mem_map.1 ht; rfl)

/-- All 1600 tuples `(θ, κ, ψ, χ₁, χ₂)`. -/
def Letter.all : List Letter :=
  Formal.all.flatMap fun t => [false, true].flatMap fun b1 => [false, true].map fun b2 =>
    ⟨t, b1, b2⟩

theorem Letter.mem_all (x : Letter) : x ∈ Letter.all := by
  obtain ⟨t, b1, b2⟩ := x
  exact List.mem_flatMap.2 ⟨t, Formal.mem_all t, List.mem_flatMap.2
    ⟨b1, by cases b1 <;> simp, List.mem_map_of_mem (by cases b2 <;> simp)⟩⟩

theorem Letter.all_nodup : Letter.all.Nodup :=
  nodup_flatMap_of_key Letter.base Formal.all_nodup
    (fun t _ => nodup_flatMap_of_key Letter.b1 (by decide)
      (fun b1 _ => (by decide : [false, true].Nodup).map fun _ _ h => by cases h; rfl)
      (fun b1 x hx => by obtain ⟨b2, -, rfl⟩ := List.mem_map.1 hx; rfl))
    (fun t x hx => by
      obtain ⟨b1, -, hx⟩ := List.mem_flatMap.1 hx
      obtain ⟨b2, -, rfl⟩ := List.mem_map.1 hx; rfl)

/-! ## The counts -/

/-- The 104 triples of `𝕆`. -/
def Formal.baseList : List Formal := Formal.all.filter Formal.inO

/-- `tab:alphabet`: `𝕆` has 104 triples. -/
theorem Formal.baseList_length : Formal.baseList.length = 104 := by decide +kernel

/-- The 276 letters of `𝔸`, in the order of `Letter.all`. -/
def Letter.letters : List Letter := Letter.all.filter fun x => decide x.InA

theorem Letter.mem_letters {x : Letter} : x ∈ Letter.letters ↔ x.InA := by
  simp [Letter.letters, Letter.mem_all]

theorem Letter.letters_nodup : Letter.letters.Nodup := Letter.all_nodup.filter _

/-- `tab:letters`: `𝔸` has 276 letters (as a list). -/
theorem Letter.letters_length : Letter.letters.length = 276 := by decide +kernel

/-- `tab:letters`: `|𝔸| = 276`. -/
theorem card_letterA : Fintype.card LetterA = 276 := by
  rw [Fintype.card_subtype]
  have h : (Finset.univ.filter Letter.InA) = Letter.letters.toFinset := by
    ext x; simp [Letter.mem_letters]
  rw [h, List.toFinset_card_of_nodup Letter.letters_nodup, Letter.letters_length]

/-- A quarter is a quadrant and a letter of `𝔸`. -/
def Quarter.equivProd : Quarter ≃ (Bool × Bool) × LetterA where
  toFun q := (q.quad, q.parent)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- `tab:fields`: `|𝔸^q| = 4 · 276 = 1104`. -/
theorem card_quarter : Fintype.card Quarter = 1104 := by
  rw [Fintype.card_congr Quarter.equivProd, Fintype.card_prod, Fintype.card_prod,
    Fintype.card_bool, card_letterA]

/-! ## Red atoms (remark after `scf:def-walls`) -/

/-- On the north–south axis the red endpoints of a thick type carry at most one atom value. -/
theorem Thick.vRed_unique (κ : Thick) (hN : κ.epN.IsRed = true) (hS : κ.epS.IsRed = true) :
    κ.epN = κ.epS := by
  revert hN hS; revert κ; decide

/-- On the east–west axis the red endpoints of a thick type carry at most one atom value. -/
theorem Thick.hRed_unique (κ : Thick) (hE : κ.epE.IsRed = true) (hW : κ.epW.IsRed = true) :
    κ.epE = κ.epW := by
  revert hE hW; revert κ; decide

end UPD.Scaffold

/-
# Appendix A: red paths (`app:red`)

Ported from the forgetting core (`C:/Infanox/fixed-noise-ergodicity-lean`,
`FixedNoiseErgodicity/Family/Red.lean`; same authors), namespace `FNE.Family` → `UPD.Scaffold`,
`fam:red` → `app:red`. The red atoms are those of `Statements.lean` (`Thick.vRedAtom`,
`Thick.hRedAtom`, read north (east) first); the forgetting core's `Thick.vRed`, `Thick.hRed` agree
with them (`vRedAtom_line`, and the same formula for corners).

* `app:red` for a *chain* of formal triples `P_m = φ(P_{m+1})(ς_m)`, `m ≤ r + 1`
  (`red_chain_col`, `red_chain_row`), by the printed induction on `r`; the base case `r = 0` is
  the printed table (a finite check).
* `app:red` for towers (`red_col`, `red_row`): the chain is the chain of ancestors of a site, and
  `s_i(x_i) = (x_i - ϖ_i) mod 2^{r+2}` is the digit sum of `scf:eq-digits`.
-/
import UndecidablePhaseDiagram.Scaffold.Tower

set_option autoImplicit false

namespace UPD.Scaffold.Thick

/-- App. A ("Ranks and red paths"): a line `⟨α, α'⟩` has the vertical red atom `α` if it is red. -/
theorem vRedAtom_line (α : VAtom) (γ : HAtom) :
    (line α γ).vRedAtom = if α.IsRed then some α else none := by
  cases α <;> rfl

/-- A line `⟨α, α'⟩` has the horizontal red atom `α'` if it is red. -/
theorem hRedAtom_line (α : VAtom) (γ : HAtom) :
    (line α γ).hRedAtom = if γ.IsRed then some γ else none := by
  cases γ <;> rfl

theorem vRedAtom_of_epN {κ : Thick} (h : κ.epN.IsRed = true) : κ.vRedAtom = some κ.epN := by
  simp [vRedAtom, h]

theorem hRedAtom_of_epE {κ : Thick} (h : κ.epE.IsRed = true) : κ.hRedAtom = some κ.epE := by
  simp [hRedAtom, h]

theorem not_epN_of_vRedAtom {κ : Thick} (h : κ.vRedAtom = none) : ¬ κ.epN.IsRed = true :=
  fun h' => by rw [vRedAtom_of_epN h'] at h; cases h

theorem not_epE_of_hRedAtom {κ : Thick} (h : κ.hRedAtom = none) : ¬ κ.epE.IsRed = true :=
  fun h' => by rw [hRedAtom_of_epE h'] at h; cases h

/-- A corner with red south endpoint has a green north endpoint. -/
theorem corner_not_epN {k : Corner} (h : k.epS.IsRed = true) : ¬ (corner k).epN.IsRed = true := by
  cases k <;> simp_all [epN, Corner.epN, Corner.epS, VAtom.IsRed]

/-- A corner with red west endpoint has a green east endpoint. -/
theorem corner_not_epE {k : Corner} (h : k.epW.IsRed = true) : ¬ (corner k).epE.IsRed = true := by
  cases k <;> simp_all [epE, Corner.epE, Corner.epW, HAtom.IsRed]

end UPD.Scaffold.Thick

namespace UPD.Scaffold


/-! ## Base case `r = 0` (the printed tables) -/

/-- `app:red`, columns, `r = 0`: the letter is child `(1, ς_{0,2})` of `P`, and `P` is child
`ς_1` of `Q`; `s₂ = ς_{0,2} + 2 ς_{1,2}` and `s₁ = 1 + 2 ς_{1,1}`. -/
theorem red_base_col (Q : Formal) (a b c : Bool) :
    ((Q.child b c).child true a).thick.vRedAtom =
      (if (2 : ℤ) ^ 0 ≤ bitZ a + 2 * (bitZ c + 2 * 0) ∧
          bitZ a + 2 * (bitZ c + 2 * 0) ≤ 3 * 2 ^ 0 then
        some (if b then .r2 else .r0) else none) ∧
    (bitZ a + 2 * (bitZ c + 2 * 0) = 2 ^ 0 →
      ∃ k, ((Q.child b c).child true a).thick = .corner k ∧ k.epN.IsRed) ∧
    (bitZ a + 2 * (bitZ c + 2 * 0) = 3 * 2 ^ 0 →
      ∃ k, ((Q.child b c).child true a).thick = .corner k ∧ k.epS.IsRed) ∧
    ((2 : ℤ) ^ 0 < bitZ a + 2 * (bitZ c + 2 * 0) → bitZ a + 2 * (bitZ c + 2 * 0) < 3 * 2 ^ 0 →
      ¬ ((Q.child b c).child true a).thick.IsCorner) := by
  cases a <;> cases b <;> cases c <;>
    simp [Formal.child, Thick.vRedAtom, Thick.epN, Thick.epS, bitZ, F, Thin.epS, Corner.epN, Corner.epS, VAtom.IsRed,
      Thick.IsCorner]

/-- `app:red`, rows, `r = 0`: the letter is child `(ς_{0,1}, 1)` of `P`, and `P` is child `ς_1`
of `Q`; `s₁ = ς_{0,1} + 2 ς_{1,1}` and `s₂ = 1 + 2 ς_{1,2}`. -/
theorem red_base_row (Q : Formal) (a b c : Bool) :
    ((Q.child b c).child a true).thick.hRedAtom =
      (if (2 : ℤ) ^ 0 ≤ bitZ a + 2 * (bitZ b + 2 * 0) ∧
          bitZ a + 2 * (bitZ b + 2 * 0) ≤ 3 * 2 ^ 0 then
        some (if c then .r3 else .r1) else none) ∧
    (bitZ a + 2 * (bitZ b + 2 * 0) = 2 ^ 0 →
      ∃ k, ((Q.child b c).child a true).thick = .corner k ∧ k.epE.IsRed) ∧
    (bitZ a + 2 * (bitZ b + 2 * 0) = 3 * 2 ^ 0 →
      ∃ k, ((Q.child b c).child a true).thick = .corner k ∧ k.epW.IsRed) ∧
    ((2 : ℤ) ^ 0 < bitZ a + 2 * (bitZ b + 2 * 0) → bitZ a + 2 * (bitZ b + 2 * 0) < 3 * 2 ^ 0 →
      ¬ ((Q.child b c).child a true).thick.IsCorner) := by
  cases a <;> cases b <;> cases c <;>
    simp [Formal.child, Thick.hRedAtom, Thick.epE, Thick.epW, bitZ, F, Thin.epW, Corner.epE, Corner.epW, HAtom.IsRed,
      Thick.IsCorner]

/-! ## `app:red` for chains -/

/-- **`app:red`** (columns), for a chain `P_m = φ(P_{m+1})(ς_m)`, `m ≤ r + 1`, whose column digits
`ς_{m,1}` vanish below `r` with `ς_{r,1} = 1` (a column of rank `r`). With
`s₂ = Σ_{m<r+2} 2^m ς_{m,2}` and `s₁ = 2^r + 2^{r+1} ς_{r+1,1}`:
(a), (b) the thick type of `P_0` has a vertical red atom iff `s₂ ∈ [2^r, 3·2^r]`, and the atom is
`r₀` if `s₁ = 2^r` (`ς_{r+1,1} = 0`) and `r₂` if `s₁ = 3·2^r`;
(c) it is the corner with red north endpoint if `s₂ = 2^r`, the corner with red south endpoint if
`s₂ = 3·2^r`, and a line in between. -/
theorem red_chain_col (r : ℕ) (P : ℕ → Formal) (s1 s2 : ℕ → Bool)
    (hP : ∀ m ≤ r + 1, P m = (P (m + 1)).child (s1 m) (s2 m)) (h0 : ∀ m < r, s1 m = false)
    (hr : s1 r = true) :
    (P 0).thick.vRedAtom = (if 2 ^ r ≤ wsum s2 (r + 2) ∧ wsum s2 (r + 2) ≤ 3 * 2 ^ r then
        some (if s1 (r + 1) then .r2 else .r0) else none) ∧
    (wsum s2 (r + 2) = 2 ^ r → ∃ k, (P 0).thick = .corner k ∧ k.epN.IsRed) ∧
    (wsum s2 (r + 2) = 3 * 2 ^ r → ∃ k, (P 0).thick = .corner k ∧ k.epS.IsRed) ∧
    (2 ^ r < wsum s2 (r + 2) → wsum s2 (r + 2) < 3 * 2 ^ r → ¬ (P 0).thick.IsCorner) := by
  induction r generalizing P s1 s2 with
  | zero =>
    rw [hP 0 (by omega), hP 1 (by omega), hr]
    exact red_base_col (P 2) (s2 0) (s1 1) (s2 1)
  | succ r ih =>
    obtain ⟨hv, hcN, hcS, hl⟩ := ih (fun m => P (m + 1)) (fun m => s1 (m + 1))
      (fun m => s2 (m + 1)) (fun m hm => hP (m + 1) (by omega)) (fun m hm => h0 (m + 1) (by omega))
      hr
    have hW : wsum s2 (r + 1 + 2) = bitZ (s2 0) + 2 * wsum (fun m => s2 (m + 1)) (r + 2) := rfl
    rw [hW, hP 0 (by omega), h0 0 (by omega)]
    have hp : (2 : ℤ) ^ (r + 1) = 2 * 2 ^ r := by ring
    rw [hp]
    have hpos : (0 : ℤ) < 2 ^ r := by positivity
    generalize wsum (fun m => s2 (m + 1)) (r + 2) = W at hv hcN hcS hl ⊢
    generalize (2 : ℤ) ^ r = p at hv hcN hcS hl hpos ⊢
    generalize P (0 + 1) = Q at hv hcN hcS hl ⊢
    cases s2 0
    · -- child `(0,0)`: the thick type of `Q`
      simp only [Formal.child, bitZ, Bool.false_eq_true, if_false, zero_add]
      refine ⟨?_, fun h => hcN (by omega), fun h => hcS (by omega), fun h h' => hl (by omega)
        (by omega)⟩
      rw [hv]
      exact if_congr (by omega) rfl rfl
    · -- child `(0,1)`: the line `⟨∂_N κ_Q, ·⟩`
      simp only [Formal.child, bitZ, if_true, Thick.vRedAtom_line]
      refine ⟨?_, fun h => by omega, fun h => by omega, fun _ _ => by simp [Thick.IsCorner]⟩
      by_cases hc : p ≤ W ∧ W < 3 * p
      · -- the north endpoint of `κ_Q` is red
        have hN : Q.thick.epN.IsRed := by
          by_cases hWp : W = p
          · obtain ⟨k, hk, hkN⟩ := hcN hWp
            rw [hk]; exact hkN
          · have hlin := hl (by omega) (by omega)
            have hv' := hv
            rw [if_pos (by omega)] at hv'
            cases hQ : Q.thick with
            | corner k => rw [hQ] at hlin; exact absurd rfl hlin
            | line α γ =>
              rw [hQ, Thick.vRedAtom_line] at hv'
              by_cases hα : α.IsRed
              · exact hα
              · rw [if_neg hα] at hv'; cases hv'
        have hv' := hv
        rw [if_pos (by omega), Thick.vRedAtom_of_epN hN] at hv'
        rw [if_pos hN, if_pos (by omega), hv']
      · -- the north endpoint of `κ_Q` is green
        have hN : ¬ Q.thick.epN.IsRed := by
          by_cases hW3 : W = 3 * p
          · obtain ⟨k, hk, hkS⟩ := hcS hW3
            rw [hk]; exact Thick.corner_not_epN hkS
          · apply Thick.not_epN_of_vRedAtom
            rw [hv, if_neg (by omega)]
        rw [if_neg hN, if_neg (by omega)]

/-- **`app:red`** (rows), for a chain whose row digits `ς_{m,2}` vanish below `r` with
`ς_{r,2} = 1` (a row of rank `r`). With `s₁ = Σ_{m<r+2} 2^m ς_{m,1}`: the thick type of `P_0` has
a horizontal red atom iff `s₁ ∈ [2^r, 3·2^r]`; it is `r₁` if `ς_{r+1,2} = 0` (`s₂ = 2^r`) and `r₃`
otherwise; it is the corner with red east endpoint if `s₁ = 2^r`, the corner with red west
endpoint if `s₁ = 3·2^r`, and a line in between. -/
theorem red_chain_row (r : ℕ) (P : ℕ → Formal) (s1 s2 : ℕ → Bool)
    (hP : ∀ m ≤ r + 1, P m = (P (m + 1)).child (s1 m) (s2 m)) (h0 : ∀ m < r, s2 m = false)
    (hr : s2 r = true) :
    (P 0).thick.hRedAtom = (if 2 ^ r ≤ wsum s1 (r + 2) ∧ wsum s1 (r + 2) ≤ 3 * 2 ^ r then
        some (if s2 (r + 1) then .r3 else .r1) else none) ∧
    (wsum s1 (r + 2) = 2 ^ r → ∃ k, (P 0).thick = .corner k ∧ k.epE.IsRed) ∧
    (wsum s1 (r + 2) = 3 * 2 ^ r → ∃ k, (P 0).thick = .corner k ∧ k.epW.IsRed) ∧
    (2 ^ r < wsum s1 (r + 2) → wsum s1 (r + 2) < 3 * 2 ^ r → ¬ (P 0).thick.IsCorner) := by
  induction r generalizing P s1 s2 with
  | zero =>
    rw [hP 0 (by omega), hP 1 (by omega), hr]
    exact red_base_row (P 2) (s1 0) (s1 1) (s2 1)
  | succ r ih =>
    obtain ⟨hv, hcE, hcW, hl⟩ := ih (fun m => P (m + 1)) (fun m => s1 (m + 1))
      (fun m => s2 (m + 1)) (fun m hm => hP (m + 1) (by omega)) (fun m hm => h0 (m + 1) (by omega))
      hr
    have hW : wsum s1 (r + 1 + 2) = bitZ (s1 0) + 2 * wsum (fun m => s1 (m + 1)) (r + 2) := rfl
    rw [hW, hP 0 (by omega), h0 0 (by omega)]
    have hp : (2 : ℤ) ^ (r + 1) = 2 * 2 ^ r := by ring
    rw [hp]
    have hpos : (0 : ℤ) < 2 ^ r := by positivity
    generalize wsum (fun m => s1 (m + 1)) (r + 2) = W at hv hcE hcW hl ⊢
    generalize (2 : ℤ) ^ r = p at hv hcE hcW hl hpos ⊢
    generalize P (0 + 1) = Q at hv hcE hcW hl ⊢
    cases s1 0
    · -- child `(0,0)`: the thick type of `Q`
      simp only [Formal.child, bitZ, Bool.false_eq_true, if_false, zero_add]
      refine ⟨?_, fun h => hcE (by omega), fun h => hcW (by omega), fun h h' => hl (by omega)
        (by omega)⟩
      rw [hv]
      exact if_congr (by omega) rfl rfl
    · -- child `(1,0)`: the line `⟨·, ∂_E κ_Q⟩`
      simp only [Formal.child, bitZ, if_true, Thick.hRedAtom_line]
      refine ⟨?_, fun h => by omega, fun h => by omega, fun _ _ => by simp [Thick.IsCorner]⟩
      by_cases hc : p ≤ W ∧ W < 3 * p
      · have hE : Q.thick.epE.IsRed := by
          by_cases hWp : W = p
          · obtain ⟨k, hk, hkE⟩ := hcE hWp
            rw [hk]; exact hkE
          · have hlin := hl (by omega) (by omega)
            have hv' := hv
            rw [if_pos (by omega)] at hv'
            cases hQ : Q.thick with
            | corner k => rw [hQ] at hlin; exact absurd rfl hlin
            | line α γ =>
              rw [hQ, Thick.hRedAtom_line] at hv'
              by_cases hγ : γ.IsRed
              · exact hγ
              · rw [if_neg hγ] at hv'; cases hv'
        have hv' := hv
        rw [if_pos (by omega), Thick.hRedAtom_of_epE hE] at hv'
        rw [if_pos hE, if_pos (by omega), hv']
      · have hE : ¬ Q.thick.epE.IsRed := by
          by_cases hW3 : W = 3 * p
          · obtain ⟨k, hk, hkW⟩ := hcW hW3
            rw [hk]; exact Thick.corner_not_epE hkW
          · apply Thick.not_epE_of_hRedAtom
            rw [hv, if_neg (by omega)]
        rw [if_neg hE, if_neg (by omega)]

/-! ## `app:red` for towers -/

/-- `app:red`: `s_i(z) = (z - ϖ_i) mod 2^{r+2}`, for the digits `c` of coordinate `i`. -/
def sres (c : ℕ → Bool) (r : ℕ) (z : ℤ) : ℤ := (z - wsum c (r + 2)) % 2 ^ (r + 2)

/-- `app:red` (proof, first line): for a coordinate of rank `r`,
`s(z) = 2^r + 2^{r+1} ς_{r+1}(z)`. -/
theorem sres_of_rank {c : ℕ → Bool} {z : ℤ} {r : ℕ} (hz : IsRank c z r) :
    sres c r z = 2 ^ r + 2 * 2 ^ r * bitZ (dig c (r + 1) z) := by
  have e1 := hz.emod
  rw [emod_eq_wsum_dig] at e1
  have e2 := wsum_succ_top (fun m => dig c m z) (r + 1)
  rw [sres, emod_eq_wsum_dig, show r + 2 = r + 1 + 1 from rfl, e2, e1, pow_succ]
  ring

theorem sres_cases {c : ℕ → Bool} {z : ℤ} {r : ℕ} (hz : IsRank c z r) :
    sres c r z = 2 ^ r ∨ sres c r z = 3 * 2 ^ r := by
  rw [sres_of_rank hz]
  cases dig c (r + 1) z
  · left; simp [bitZ]
  · right; simp only [bitZ, if_true]; ring

/-- **`app:red`** (columns). Let `(f_m)` be a tower of height `h ≥ r + 2` and `x₁` a column of rank
`r`. Then `s₁(x₁) ∈ {2^r, 3·2^r}`, and for every `x = (x₁, x₂)`: (a), (b) the thick type of `f_0(x)`
has a vertical red atom iff `s₂(x₂) ∈ [2^r, 3·2^r]`, and this atom is `r₀` if `s₁(x₁) = 2^r` and
`r₂` if `s₁(x₁) = 3·2^r`; (c) it is the corner with red north endpoint if `s₂(x₂) = 2^r`, the
corner with red south endpoint if `s₂(x₂) = 3·2^r`, and a line if `2^r < s₂(x₂) < 3·2^r`. -/
theorem red_col {υ : ℕ → Bool × Bool} {f : ℕ → Plane → Letter} {h r : ℕ} (hf : TowerRel υ f h)
    (hrh : r + 2 ≤ h) {x : Plane} (hx : IsRank (col υ) x.1 r) :
    (sres (col υ) r x.1 = 2 ^ r ∨ sres (col υ) r x.1 = 3 * 2 ^ r) ∧
    (f 0 x).base.thick.vRedAtom =
      (if 2 ^ r ≤ sres (row υ) r x.2 ∧ sres (row υ) r x.2 ≤ 3 * 2 ^ r then
        some (if sres (col υ) r x.1 = 2 ^ r then .r0 else .r2) else none) ∧
    (sres (row υ) r x.2 = 2 ^ r → ∃ k, (f 0 x).base.thick = .corner k ∧ k.epN.IsRed) ∧
    (sres (row υ) r x.2 = 3 * 2 ^ r → ∃ k, (f 0 x).base.thick = .corner k ∧ k.epS.IsRed) ∧
    (2 ^ r < sres (row υ) r x.2 → sres (row υ) r x.2 < 3 * 2 ^ r →
      ¬ (f 0 x).base.thick.IsCorner) := by
  obtain ⟨hv, hN, hS, hl⟩ := red_chain_col r (fun m => (f m (ancP υ m x)).base)
    (fun m => dig (col υ) m x.1) (fun m => dig (row υ) m x.2)
    (fun m hm => by show (f m (ancP υ m x)).base = _; rw [hf.chain (by omega) x]; rfl) hx.2 hx.1
  have h2 : sres (row υ) r x.2 = wsum (fun m => dig (row υ) m x.2) (r + 2) :=
    emod_eq_wsum_dig _ _ _
  rw [← h2] at hv hN hS hl
  refine ⟨sres_cases hx, ?_, hN, hS, hl⟩
  rw [show (f 0 x).base = (f 0 (ancP υ 0 x)).base from rfl, hv]
  refine if_congr Iff.rfl ?_ rfl
  rw [sres_of_rank hx]
  have hpos : (0 : ℤ) < 2 ^ r := by positivity
  cases dig (col υ) (r + 1) x.1
  · simp [bitZ]
  · simp only [bitZ, if_true]
    rw [if_neg (by intro h; nlinarith)]

/-- **`app:red`** (rows): the same for a row `x₂` of rank `r`, with the coordinates exchanged:
`s₂(x₂) ∈ {2^r, 3·2^r}`; a horizontal red atom occurs iff `s₁(x₁) ∈ [2^r, 3·2^r]`; it is `r₁` if
`s₂(x₂) = 2^r` and `r₃` if `s₂(x₂) = 3·2^r`; the thick type is the corner with red east endpoint
if `s₁(x₁) = 2^r`, the corner with red west endpoint if `s₁(x₁) = 3·2^r`, and a line in
between. -/
theorem red_row {υ : ℕ → Bool × Bool} {f : ℕ → Plane → Letter} {h r : ℕ} (hf : TowerRel υ f h)
    (hrh : r + 2 ≤ h) {x : Plane} (hx : IsRank (row υ) x.2 r) :
    (sres (row υ) r x.2 = 2 ^ r ∨ sres (row υ) r x.2 = 3 * 2 ^ r) ∧
    (f 0 x).base.thick.hRedAtom =
      (if 2 ^ r ≤ sres (col υ) r x.1 ∧ sres (col υ) r x.1 ≤ 3 * 2 ^ r then
        some (if sres (row υ) r x.2 = 2 ^ r then .r1 else .r3) else none) ∧
    (sres (col υ) r x.1 = 2 ^ r → ∃ k, (f 0 x).base.thick = .corner k ∧ k.epE.IsRed) ∧
    (sres (col υ) r x.1 = 3 * 2 ^ r → ∃ k, (f 0 x).base.thick = .corner k ∧ k.epW.IsRed) ∧
    (2 ^ r < sres (col υ) r x.1 → sres (col υ) r x.1 < 3 * 2 ^ r →
      ¬ (f 0 x).base.thick.IsCorner) := by
  obtain ⟨hv, hE, hW, hl⟩ := red_chain_row r (fun m => (f m (ancP υ m x)).base)
    (fun m => dig (col υ) m x.1) (fun m => dig (row υ) m x.2)
    (fun m hm => by show (f m (ancP υ m x)).base = _; rw [hf.chain (by omega) x]; rfl) hx.2 hx.1
  have h1 : sres (col υ) r x.1 = wsum (fun m => dig (col υ) m x.1) (r + 2) :=
    emod_eq_wsum_dig _ _ _
  rw [← h1] at hv hE hW hl
  refine ⟨sres_cases hx, ?_, hE, hW, hl⟩
  rw [show (f 0 x).base = (f 0 (ancP υ 0 x)).base from rfl, hv]
  refine if_congr Iff.rfl ?_ rfl
  rw [sres_of_rank hx]
  have hpos : (0 : ℤ) < 2 ^ r := by positivity
  cases dig (row υ) (r + 1) x.2
  · simp [bitZ]
  · simp only [bitZ, if_true]
    rw [if_neg (by intro h; nlinarith)]

end UPD.Scaffold

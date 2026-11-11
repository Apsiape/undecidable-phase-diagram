/-
# Section 3.3: towers, digits and ranks

Ported from the forgetting core (`C:/Infanox/fixed-noise-ergodicity-lean`,
`FixedNoiseErgodicity/Family/Tower.lean`; same authors), namespace `FNE.Family` →
`UPD.Scaffold`; labels renamed to this paper's (`fam:eq-digits` → `scf:eq-digits`,
`fam:rank-bits` → `app:rank-bits`, `fam:tower-exists` → the proof of `scf:phase`(c)).

* Towers (Section 3.3, after `scf:desub`): towers of height `h` (`TowerRel`) and of height `∞`
  (`IsInfTower`). **[choice] (proof side)** Patterns are total maps `ℤ² → Letter` (as in
  `Scaffold/Legal.lean`): the relation `f_m(υ_m + 2v + ς) = φ'(f_{m+1}(v))(ς)` is required on all
  of `ℤ²` (`subAt`), and legality is required only for towers of height `∞` (every `f_m` a
  tiling). The phase `ϖ = Σ 2^m υ_m ∈ ℤ₂²` is represented by its digit sequence
  `υ : ℕ → Bool × Bool` (decision D9); its truncations `ϖ mod 2^l` are the integers `wsum`.
* Towers of height `∞` with every digit sequence (`exists_tower`; the proof of `scf:phase`(c)).
* The digits `ς_m(x)` and ancestors `x^{(m)}` of a site, coordinatewise (`dig`, `anc`), and
  `scf:eq-digits` in exact form: `z = (ϖ mod 2^l) + Σ_{m<l} 2^m ς_m + 2^l z^{(l)}`.
* Ranks (App. A, "Ranks and red paths") and `app:rank-bits`.
-/
import UndecidablePhaseDiagram.Scaffold.Substitution

set_option autoImplicit false

namespace UPD.Scaffold


/-! ## Digit sums -/

/-- `Σ_{m<l} 2^m b_m` for a sequence of bits `b` (bit `true` is `1`), by the shift recursion
`Σ_{m<l+1} 2^m b_m = b_0 + 2 Σ_{m<l} 2^m b_{m+1}`. -/
def wsum : (ℕ → Bool) → ℕ → ℤ
  | _, 0 => 0
  | b, l + 1 => bitZ (b 0) + 2 * wsum (fun m => b (m + 1)) l

theorem bitZ_nonneg (s : Bool) : 0 ≤ bitZ s := by cases s <;> simp [bitZ]

theorem bitZ_le_one (s : Bool) : bitZ s ≤ 1 := by cases s <;> simp [bitZ]

theorem wsum_nonneg (b : ℕ → Bool) (l : ℕ) : 0 ≤ wsum b l := by
  induction l generalizing b with
  | zero => simp [wsum]
  | succ l ih =>
    have e : wsum b (l + 1) = bitZ (b 0) + 2 * wsum (fun m => b (m + 1)) l := rfl
    rw [e]; have := bitZ_nonneg (b 0); have := ih fun m => b (m + 1); omega

theorem wsum_lt (b : ℕ → Bool) (l : ℕ) : wsum b l < 2 ^ l := by
  induction l generalizing b with
  | zero => simp [wsum]
  | succ l ih =>
    have e : wsum b (l + 1) = bitZ (b 0) + 2 * wsum (fun m => b (m + 1)) l := rfl
    rw [e, pow_succ]
    have := bitZ_le_one (b 0); have := ih fun m => b (m + 1); omega

/-- The top digit: `Σ_{m<l+1} 2^m b_m = Σ_{m<l} 2^m b_m + 2^l b_l`. -/
theorem wsum_succ_top (b : ℕ → Bool) (l : ℕ) : wsum b (l + 1) = wsum b l + 2 ^ l * bitZ (b l) := by
  induction l generalizing b with
  | zero => simp [wsum]
  | succ l ih =>
    have e1 : wsum b (l + 1 + 1) = bitZ (b 0) + 2 * wsum (fun m => b (m + 1)) (l + 1) := rfl
    have e2 : wsum b (l + 1) = bitZ (b 0) + 2 * wsum (fun m => b (m + 1)) l := rfl
    rw [e1, e2, ih, pow_succ]
    ring

theorem wsum_congr {b b' : ℕ → Bool} {l : ℕ} (h : ∀ m < l, b m = b' m) : wsum b l = wsum b' l := by
  induction l generalizing b b' with
  | zero => rfl
  | succ l ih =>
    have e : ∀ b : ℕ → Bool, wsum b (l + 1) = bitZ (b 0) + 2 * wsum (fun m => b (m + 1)) l :=
      fun _ => rfl
    rw [e, e, h 0 (Nat.succ_pos l), ih fun m hm => h (m + 1) (by omega)]

theorem wsum_false (l : ℕ) : wsum (fun _ => false) l = 0 := by
  induction l with
  | zero => rfl
  | succ l ih => rw [wsum_succ_top, ih]; simp [bitZ]

/-- `Σ_{m<j+n} 2^m b_m = Σ_{m<j} 2^m b_m + 2^j Σ_{m<n} 2^m b_{m+j}`. -/
theorem wsum_add (b : ℕ → Bool) (j n : ℕ) :
    wsum b (j + n) = wsum b j + 2 ^ j * wsum (fun m => b (m + j)) n := by
  induction n with
  | zero => simp [wsum]
  | succ n ih =>
    rw [← add_assoc, wsum_succ_top, ih, wsum_succ_top, pow_add]
    simp only [Nat.add_comm n j]
    ring

/-- Truncation: `(Σ_{m<l} 2^m b_m) mod 2^j = Σ_{m<j} 2^m b_m` for `j ≤ l`. -/
theorem wsum_emod (b : ℕ → Bool) {j l : ℕ} (h : j ≤ l) : wsum b l % 2 ^ j = wsum b j := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [wsum_add, Int.add_mul_emod_self_left]
  exact Int.emod_eq_of_lt (wsum_nonneg _ _) (wsum_lt _ _)

/-- A digit sum `Σ_{m≤k} 2^m b_m = 2^k` has digits `0` below `k` and digit `1` at `k`. -/
theorem digits_of_wsum_eq {b : ℕ → Bool} {k : ℕ} (h : wsum b (k + 1) = 2 ^ k) :
    (∀ m < k, b m = false) ∧ b k = true := by
  induction k generalizing b with
  | zero =>
    have e : wsum b (0 + 1) = bitZ (b 0) + 2 * wsum (fun m => b (m + 1)) 0 := rfl
    rw [e] at h
    simp only [wsum, mul_zero, add_zero, pow_zero] at h
    refine ⟨fun m hm => absurd hm (Nat.not_lt_zero m), ?_⟩
    cases hb : b 0
    · rw [hb] at h; simp [bitZ] at h
    · rfl
  | succ k ih =>
    have e : wsum b (k + 1 + 1) = bitZ (b 0) + 2 * wsum (fun m => b (m + 1)) (k + 1) := rfl
    rw [e, pow_succ] at h
    have hb0 : b 0 = false := by
      cases hb : b 0
      · rfl
      · rw [hb] at h; simp only [bitZ, if_true] at h; omega
    rw [hb0] at h
    simp only [bitZ, Bool.false_eq_true, if_false, zero_add] at h
    have h' : wsum (fun m => b (m + 1)) (k + 1) = 2 ^ k := by omega
    obtain ⟨hlow, htop⟩ := ih h'
    refine ⟨fun m hm => ?_, htop⟩
    cases m with
    | zero => exact hb0
    | succ m => exact hlow m (by omega)

/-! ## Ancestors and digits of a coordinate (Section 3.3, after `scf:desub`) -/

/-- The ancestors of a coordinate for the digit sequence `c` (`υ_{m,i}`): `z^{(0)} = z` and
`z^{(m+1)} = ⌊(z^{(m)} - υ_m)/2⌋`, so that `z^{(m)} = υ_m + 2 z^{(m+1)} + ς_m`. -/
def anc (c : ℕ → Bool) : ℕ → ℤ → ℤ
  | 0, z => z
  | m + 1, z => (anc c m z - bitZ (c m)) / 2

/-- The digit `ς_m(z) ∈ {0,1}` of a coordinate (Section 3.3): `z^{(m)} - υ_m mod 2`. -/
def dig (c : ℕ → Bool) (m : ℕ) (z : ℤ) : Bool := decide ((anc c m z - bitZ (c m)) % 2 = 1)

theorem bitZ_decide_emod_two (y : ℤ) : bitZ (decide (y % 2 = 1)) = y % 2 := by
  rcases Int.emod_two_eq_zero_or_one y with h | h <;> simp [bitZ, h]

/-- Section 3.3: `z^{(m)} = υ_m + 2 z^{(m+1)} + ς_m(z)`. -/
theorem anc_eq (c : ℕ → Bool) (m : ℕ) (z : ℤ) :
    anc c m z = bitZ (c m) + 2 * anc c (m + 1) z + bitZ (dig c m z) := by
  simp only [anc, dig, bitZ_decide_emod_two]
  have := Int.mul_ediv_add_emod (anc c m z - bitZ (c m)) 2
  omega

/-- The shift: ancestors of `z` for `c` above level `1` are ancestors of `z^{(1)}` for the
shifted sequence. -/
theorem anc_succ' (c : ℕ → Bool) (m : ℕ) (z : ℤ) :
    anc c (m + 1) z = anc (fun k => c (k + 1)) m ((z - bitZ (c 0)) / 2) := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [anc] at ih ⊢; rw [ih]

theorem dig_succ (c : ℕ → Bool) (m : ℕ) (z : ℤ) :
    dig c (m + 1) z = dig (fun k => c (k + 1)) m ((z - bitZ (c 0)) / 2) := by
  simp only [dig, anc_succ']

theorem dig_zero (c : ℕ → Bool) (z : ℤ) : dig c 0 z = decide ((z - bitZ (c 0)) % 2 = 1) := rfl

/-- **`scf:eq-digits`**, in exact form: `z = (ϖ mod 2^l) + Σ_{m<l} 2^m ς_m(z) + 2^l z^{(l)}`. -/
theorem eq_digits (c : ℕ → Bool) (l : ℕ) (z : ℤ) :
    z = wsum c l + wsum (fun m => dig c m z) l + 2 ^ l * anc c l z := by
  induction l generalizing c z with
  | zero => simp [wsum, anc]
  | succ l ih =>
    have h1 := ih (fun k => c (k + 1)) ((z - bitZ (c 0)) / 2)
    have h0 : z = bitZ (c 0) + 2 * ((z - bitZ (c 0)) / 2) + bitZ (dig c 0 z) := anc_eq c 0 z
    have e1 : wsum c (l + 1) = bitZ (c 0) + 2 * wsum (fun m => c (m + 1)) l := rfl
    have e2 : wsum (fun m => dig c m z) (l + 1) =
        bitZ (dig c 0 z) + 2 * wsum (fun m => dig c (m + 1) z) l := rfl
    rw [e1, e2, anc_succ', pow_succ]
    simp only [dig_succ]
    linear_combination h0 + 2 * h1

/-- `scf:eq-digits`: `(z - ϖ) mod 2^l = Σ_{m<l} 2^m ς_m(z)`. -/
theorem emod_eq_wsum_dig (c : ℕ → Bool) (l : ℕ) (z : ℤ) :
    (z - wsum c l) % 2 ^ l = wsum (fun m => dig c m z) l := by
  have h := eq_digits c l z
  have : z - wsum c l = wsum (fun m => dig c m z) l + 2 ^ l * anc c l z := by linarith
  rw [this, Int.add_mul_emod_self_left]
  exact Int.emod_eq_of_lt (wsum_nonneg _ _) (wsum_lt _ _)

/-- App. A ("Ranks and red paths"): the coordinate `z` has *rank* `r` if `ς_r(z) = 1` and `ς_m(z) = 0` for `m < r`. -/
def IsRank (c : ℕ → Bool) (z : ℤ) (r : ℕ) : Prop := dig c r z = true ∧ ∀ m < r, dig c m z = false

theorem IsRank.unique {c : ℕ → Bool} {z : ℤ} {r r' : ℕ} (h : IsRank c z r) (h' : IsRank c z r') :
    r = r' := by
  rcases lt_trichotomy r r' with hlt | heq | hgt
  · have := h'.2 r hlt; rw [h.1] at this; exact absurd this (by decide)
  · exact heq
  · have := h.2 r' hgt; rw [h'.1] at this; exact absurd this (by decide)

/-- App. A ("Ranks and red paths"): a coordinate of rank `r` satisfies `z - ϖ ≡ 2^r (mod 2^{r+1})`. -/
theorem IsRank.emod {c : ℕ → Bool} {z : ℤ} {r : ℕ} (h : IsRank c z r) :
    (z - wsum c (r + 1)) % 2 ^ (r + 1) = 2 ^ r := by
  rw [emod_eq_wsum_dig]
  simp only [wsum_succ_top, h.1]
  rw [wsum_congr (b' := fun _ => false) h.2, wsum_false]
  simp [bitZ]

/-- Conversely, `z - ϖ ≡ 2^r (mod 2^{r+1})` gives rank `r`. -/
theorem isRank_of_emod {c : ℕ → Bool} {z : ℤ} {r l : ℕ} (hl : r + 1 ≤ l)
    (h : (z - wsum c l) % 2 ^ (r + 1) = 2 ^ r) : IsRank c z r := by
  have e : (z - wsum c l) % 2 ^ (r + 1) = (z - wsum c l) % 2 ^ l % 2 ^ (r + 1) :=
    (Int.emod_emod_of_dvd _ (pow_dvd_pow 2 hl)).symm
  rw [e, emod_eq_wsum_dig, wsum_emod _ hl] at h
  exact ⟨(digits_of_wsum_eq h).2, (digits_of_wsum_eq h).1⟩

/-! ## Towers (Section 3.3 (towers)) -/

/-- The site `x - υ`. -/
def shiftBy (υ : Bool × Bool) (x : Plane) : Plane := (x.1 - bitZ υ.1, x.2 - bitZ υ.2)

/-- `scf:phase`(c) (proof): `sub_υ(g)(υ + 2v + ς) = φ'(g(v))(ς)`. -/
def subAt (υ : Bool × Bool) (g : Plane → Letter) : Plane → Letter :=
  fun x => subst2 Letter.child g (shiftBy υ x)

theorem subAt_fineSite (υ : Bool × Bool) (g : Plane → Letter) (v : Plane) (s1 s2 : Bool) :
    subAt υ g (fineSite v s1 s2 + (bitZ υ.1, bitZ υ.2)) = (g v).child s1 s2 := by
  have : shiftBy υ (fineSite v s1 s2 + (bitZ υ.1, bitZ υ.2)) = fineSite v s1 s2 := by
    simp [shiftBy]
  rw [subAt, this, subst2_fineSite]

/-- Section 3.3 (towers): the relation of a tower of height `h` with digits `υ`, on all of `ℤ²`:
`f_m = sub_{υ_m}(f_{m+1})` for `m < h`. -/
def TowerRel (υ : ℕ → Bool × Bool) (f : ℕ → Plane → Letter) (h : ℕ) : Prop :=
  ∀ m < h, f m = subAt (υ m) (f (m + 1))

/-- Section 3.3 (towers), `h = ∞`: every `f_m` is a tiling of `𝔸` and `f_m = sub_{υ_m}(f_{m+1})` for
every `m`. The phase is the 2-adic integer with digits `υ`. -/
structure IsInfTower (υ : ℕ → Bool × Bool) (f : ℕ → Plane → Letter) : Prop where
  tiling : ∀ m, IsLetterTiling (f m)
  rel : ∀ m, f m = subAt (υ m) (f (m + 1))

theorem IsInfTower.towerRel {υ : ℕ → Bool × Bool} {f : ℕ → Plane → Letter} (hf : IsInfTower υ f)
    (h : ℕ) : TowerRel υ f h := fun m _ => hf.rel m

theorem fine2_univ : fine2 (Set.univ : Set Plane) = Set.univ := by
  ext x; simp [fine2]

/-- `scf:phase`(c) (proof): `sub_υ` maps tilings of `𝔸` to tilings, by
`scf:ruler-forward`(a),(b). -/
theorem IsLetterTiling.sub {g : Plane → Letter} (hg : IsLetterTiling g) (υ : Bool × Bool) :
    IsLetterTiling (subAt υ g) := by
  refine ⟨fun x => ?_, ?_⟩
  · exact subst2_mem _ (fun _ h => h.child) (U := Set.univ) (fun u _ => hg.1 u) _ trivial
  · have hl : LegalOn Letter.MatchE Letter.MatchN Set.univ (subst2 Letter.child g) := by
      rw [← fine2_univ]; exact Letter.legalOn_phi'_iff.2 hg.2
    have ht := hl.translate (-bitZ υ.1, -bitZ υ.2)
    refine (ht.mono (fun _ _ => trivial)).congr fun x _ => ?_
    simp only [subAt, shiftBy]
    congr 1

/-- **`scf:phase`(c).** For every digit sequence `υ` (every phase `ϖ ∈ ℤ₂²`) there is a tower
of height `∞` with digits `υ`. Proof as printed: the sets `𝒯_l` of sequences of tilings with
`f_m = sub_{υ_m}(f_{m+1})` for `m < l` are closed, nonempty and decreasing in the compact space
`(𝔸^{ℤ²})^ℕ`. -/
theorem exists_tower (υ : ℕ → Bool × Bool) : ∃ f, IsInfTower υ f := by
  letI : TopologicalSpace Letter := ⊥
  haveI : DiscreteTopology Letter := ⟨rfl⟩
  -- every condition on two coordinates is closed
  have hcl : ∀ (m m' : ℕ) (x y : Plane) (Rel : Letter → Letter → Prop),
      IsClosed {F : ℕ → Plane → Letter | Rel (F m x) (F m' y)} := by
    intro m m' x y Rel
    have hc : Continuous fun F : ℕ → Plane → Letter => (F m x, F m' y) :=
      ((continuous_apply x).comp (continuous_apply m)).prodMk
        ((continuous_apply y).comp (continuous_apply m'))
    exact (isClosed_discrete {p : Letter × Letter | Rel p.1 p.2}).preimage hc
  let T : ℕ → Set (ℕ → Plane → Letter) := fun l =>
    {F | (∀ m, IsLetterTiling (F m)) ∧ ∀ m < l, F m = subAt (υ m) (F (m + 1))}
  have hT : ∀ l, T l =
      (⋂ m, ⋂ u, {F : ℕ → Plane → Letter | (fun a _ => a.InA) (F m u) (F m u)}) ∩
      (⋂ m, ⋂ u, {F : ℕ → Plane → Letter | Letter.MatchE (F m u) (F m (u + (1, 0)))}) ∩
      (⋂ m, ⋂ u, {F : ℕ → Plane → Letter | Letter.MatchN (F m u) (F m (u + (0, 1)))}) ∩
      (⋂ m, ⋂ (_ : m < l), ⋂ x, {F : ℕ → Plane → Letter |
        F m x = subAt (υ m) (F (m + 1)) x}) := by
    intro l
    ext F
    simp only [T, IsLetterTiling, LegalOn, Set.mem_univ, true_implies, Set.mem_setOf_eq,
      Set.mem_inter_iff, Set.mem_iInter, funext_iff]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨⟨fun m => (h1 m).1, fun m => (h1 m).2.1⟩, fun m => (h1 m).2.2⟩, h2⟩
    · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
      exact ⟨fun m => ⟨h1 m, h2 m, h3 m⟩, h4⟩
  have hclosed : ∀ l, IsClosed (T l) := by
    intro l
    rw [hT]
    refine IsClosed.inter (IsClosed.inter (IsClosed.inter ?_ ?_) ?_) ?_
    · exact isClosed_iInter fun m => isClosed_iInter fun u => hcl m m u u (fun a _ => a.InA)
    · exact isClosed_iInter fun m => isClosed_iInter fun u => hcl m m u _ _
    · exact isClosed_iInter fun m => isClosed_iInter fun u => hcl m m u _ _
    · exact isClosed_iInter fun m => isClosed_iInter fun _ => isClosed_iInter fun x =>
        hcl m (m + 1) x _ (fun a b => a = Letter.child b _ _)
  -- nonempty: a tiling at the top, substituted downwards
  obtain ⟨g, hgt⟩ := exists_letter_tiling
  let aux : ℕ → ℕ → Plane → Letter := fun k => Nat.rec (fun _ => g)
    (fun _ ih m => subAt (υ m) (ih (m + 1))) k
  have aux_tiling : ∀ k m, IsLetterTiling (aux k m) := by
    intro k
    induction k with
    | zero => intro m; exact hgt
    | succ k ih => intro m; exact (ih (m + 1)).sub (υ m)
  have hne : ∀ l, (T l).Nonempty := by
    intro l
    refine ⟨fun m => aux (l - m) m, fun m => aux_tiling _ _, fun m hm => ?_⟩
    have : l - m = (l - (m + 1)) + 1 := by omega
    show aux (l - m) m = _
    rw [this]
  have hdec : ∀ l, T (l + 1) ⊆ T l := fun l F hF => ⟨hF.1, fun m hm => hF.2 m (by omega)⟩
  obtain ⟨F, hF⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed T hdec hne
    (hclosed 0).isCompact hclosed
  rw [Set.mem_iInter] at hF
  exact ⟨F, (hF 0).1, fun m => (hF (m + 1)).2 m (Nat.lt_succ_self m)⟩

/-! ## The chain of ancestors of a site -/

/-- The column digits `υ_{m,1}` of a tower. -/
def col (υ : ℕ → Bool × Bool) : ℕ → Bool := fun m => (υ m).1

/-- The row digits `υ_{m,2}` of a tower. -/
def row (υ : ℕ → Bool × Bool) : ℕ → Bool := fun m => (υ m).2

/-- The ancestor `x^{(m)}` of a site (Section 3.3). -/
def ancP (υ : ℕ → Bool × Bool) (m : ℕ) (x : Plane) : Plane :=
  (anc (col υ) m x.1, anc (row υ) m x.2)

/-- Section 3.3: `f_m(x^{(m)}) = φ'(f_{m+1}(x^{(m+1)}))(ς_m(x))` for `m < h`. -/
theorem TowerRel.chain {υ : ℕ → Bool × Bool} {f : ℕ → Plane → Letter} {h : ℕ}
    (hf : TowerRel υ f h) {m : ℕ} (hm : m < h) (x : Plane) :
    f m (ancP υ m x) = (f (m + 1) (ancP υ (m + 1) x)).child (dig (col υ) m x.1)
      (dig (row υ) m x.2) := by
  rw [hf m hm]
  rfl

/-! ## `app:rank-bits` -/

/-- `app:rank-bits`, for a chain of letters: if `P_m = φ'(P_{m+1})(ς_m)` for `m ≤ r`, the column
digits `ς_{m,1}` vanish below `r` and `ς_{r,1} = 1`, then `χ₁(P_0) ≡ r (mod 2)`. -/
theorem chain_b1 (r : ℕ) (P : ℕ → Letter) (s1 s2 : ℕ → Bool)
    (hP : ∀ m ≤ r, P m = (P (m + 1)).child (s1 m) (s2 m)) (h0 : ∀ m < r, s1 m = false)
    (hr : s1 r = true) : (P 0).b1 = decide (r % 2 = 1) := by
  induction r generalizing P s1 s2 with
  | zero => rw [hP 0 le_rfl, hr]; rfl
  | succ r ih =>
    have h := ih (fun m => P (m + 1)) (fun m => s1 (m + 1)) (fun m => s2 (m + 1))
      (fun m hm => hP (m + 1) (by omega)) (fun m hm => h0 (m + 1) (by omega)) hr
    rw [hP 0 (Nat.zero_le _), h0 0 (Nat.succ_pos r)]
    simp only [Letter.child, Bool.false_eq_true, if_false]
    rw [h]
    by_cases hr2 : r % 2 = 1
    · have : ¬ ((r + 1) % 2 = 1) := by omega
      simp [hr2, this]
    · have : (r + 1) % 2 = 1 := by omega
      simp [hr2, this]

/-- `app:rank-bits`, rows: `χ₂(P_0) ≡ r (mod 2)` when the row digits have rank `r`. -/
theorem chain_b2 (r : ℕ) (P : ℕ → Letter) (s1 s2 : ℕ → Bool)
    (hP : ∀ m ≤ r, P m = (P (m + 1)).child (s1 m) (s2 m)) (h0 : ∀ m < r, s2 m = false)
    (hr : s2 r = true) : (P 0).b2 = decide (r % 2 = 1) := by
  induction r generalizing P s1 s2 with
  | zero => rw [hP 0 le_rfl, hr]; rfl
  | succ r ih =>
    have h := ih (fun m => P (m + 1)) (fun m => s1 (m + 1)) (fun m => s2 (m + 1))
      (fun m hm => hP (m + 1) (by omega)) (fun m hm => h0 (m + 1) (by omega)) hr
    rw [hP 0 (Nat.zero_le _), h0 0 (Nat.succ_pos r)]
    simp only [Letter.child, Bool.false_eq_true, if_false]
    rw [h]
    by_cases hr2 : r % 2 = 1
    · have : ¬ ((r + 1) % 2 = 1) := by omega
      simp [hr2, this]
    · have : (r + 1) % 2 = 1 := by omega
      simp [hr2, this]

/-- **`app:rank-bits`.** If the column `x₁` has rank `r < h`, then `χ₁(f_0(x)) ≡ r (mod 2)`. -/
theorem rank_bits_col {υ : ℕ → Bool × Bool} {f : ℕ → Plane → Letter} {h r : ℕ}
    (hf : TowerRel υ f h) (hr : r < h) {x : Plane} (hx : IsRank (col υ) x.1 r) :
    (f 0 x).b1 = decide (r % 2 = 1) :=
  chain_b1 r (fun m => f m (ancP υ m x)) (fun m => dig (col υ) m x.1) (fun m => dig (row υ) m x.2)
    (fun m hm => hf.chain (by omega) x) hx.2 hx.1

/-- **`app:rank-bits`**, rows: if the row `x₂` has rank `r < h`, then `χ₂(f_0(x)) ≡ r (mod 2)`. -/
theorem rank_bits_row {υ : ℕ → Bool × Bool} {f : ℕ → Plane → Letter} {h r : ℕ}
    (hf : TowerRel υ f h) (hr : r < h) {x : Plane} (hx : IsRank (row υ) x.2 r) :
    (f 0 x).b2 = decide (r % 2 = 1) :=
  chain_b2 r (fun m => f m (ancP υ m x)) (fun m => dig (col υ) m x.1) (fun m => dig (row υ) m x.2)
    (fun m hm => hf.chain (by omega) x) hx.2 hx.1

end UPD.Scaffold

/-
# Appendix A: desubstitution (`app:thin`, `app:parents`, `app:base-desub`, `scf:desub`)

New in this project: the forgetting core proves the forward half (`app:sound`,
`app:ruler-sound`, `Scaffold/Substitution.lean`); the backward half is proved here by the printed
arguments, which "compare components of tiles": no list of local patterns is enumerated. The
few finite facts used are Boolean folds over the 400 formal triples (`decide +kernel`, linear).

* `app:thin` (`thin_phase`, `thin_phase_unique`): in a tiling of `𝕆` the thin types form the
  pattern `a, c, d, b` on the blocks of a unique coset of `2ℤ²`.
* `app:parents` (`parents_eq`, `parent_inO`): a legal block with thin types `a, c, d, b` is
  `φ(t)` for `t = (F⁻¹(κ₁₁), κ₀₀, ψ₀₀)`, and `t ∈ 𝕆` once the block extends below and to the left.
* `app:base-desub` (`base_desub`): every tiling of `𝕆` is `sub_υ(z)` for a unique `υ ∈ {0,1}²`
  and a unique tiling `z` of `𝕆`.
* `tab:witness` (`witness_col`, `witness_row`) and **`scf:desub`** (`desub`): every tiling of `𝔸`
  is `sub_υ(g)` for a unique `υ` and a unique tiling `g` of `𝔸`, with the printed proof of (R1),
  (R2) for `g` (two levels of base desubstitution and the witness cells).
-/
import UndecidablePhaseDiagram.Scaffold.Tower

set_option autoImplicit false

-- The finite checks below walk the list of 400 formal triples in the kernel.
set_option maxRecDepth 20000

namespace UPD.Scaffold

/-! ## Parity -/

/-- The parity bit of an integer (`true` for odd). -/
def par (z : ℤ) : Bool := decide (z % 2 = 1)

theorem par_add_one (z : ℤ) : par (z + 1) = !par z := by
  unfold par
  rcases Int.emod_two_eq_zero_or_one z with h | h
  · have h' : (z + 1) % 2 = 1 := by omega
    simp [h, h']
  · have h' : (z + 1) % 2 = 0 := by omega
    simp [h, h']

theorem par_zero : par 0 = false := rfl

/-- A function on `ℤ` that does not change from `j` to `j + 1` is constant. -/
theorem eq_const {α : Type*} {q : ℤ → α} (h : ∀ j, q (j + 1) = q j) (j : ℤ) : q j = q 0 := by
  induction j with
  | zero => rfl
  | succ i ih => rw [h, ih]
  | pred i ih =>
    have h1 := h (-(i : ℤ) - 1)
    rw [show -(i : ℤ) - 1 + 1 = -(i : ℤ) by ring, ih] at h1
    exact h1.symm

/-- A Boolean function on `ℤ` that flips at each step is `q 0` plus the parity. -/
theorem eq_xor_par {q : ℤ → Bool} (h : ∀ j, q (j + 1) = !q j) (j : ℤ) :
    q j = xor (q 0) (par j) := by
  induction j with
  | zero => simp [par_zero]
  | succ i ih =>
    rw [h, ih, par_add_one]
    cases q 0 <;> cases par (i : ℤ) <;> rfl
  | pred i ih =>
    have h1 := h (-(i : ℤ) - 1)
    have h2 := par_add_one (-(i : ℤ) - 1)
    rw [show -(i : ℤ) - 1 + 1 = -(i : ℤ) by ring] at h1 h2
    rw [ih, h2] at h1
    cases hq : q (-(i : ℤ) - 1) <;> cases h0 : q 0 <;> cases hp : par (-(i : ℤ) - 1) <;>
      simp_all

theorem par_fineSite (v : ℤ) (s u : Bool) : par (2 * v + bitZ s + bitZ u) = xor s u := by
  unfold par
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  cases s <;> cases u <;> simp [bitZ] <;> omega

/-- A map on `ℤ²` with values in `{0,1}²` whose first bit flips along `e₁` and whose second bit
flips along `e₂` (each staying put along the other direction) is `p(0) + x mod 2`. -/
theorem eq_of_flips {p : Plane → Bool × Bool}
    (hE : ∀ x, p (x + (1, 0)) = (!(p x).1, (p x).2))
    (hN : ∀ x, p (x + (0, 1)) = ((p x).1, !(p x).2)) (x : Plane) :
    p x = (xor (p (0, 0)).1 (par x.1), xor (p (0, 0)).2 (par x.2)) := by
  obtain ⟨i, j⟩ := x
  have hE' : ∀ i j : ℤ, p (i + 1, j) = (!(p (i, j)).1, (p (i, j)).2) := fun i j => by
    have := hE (i, j); rwa [Prod.mk_add_mk, add_zero] at this
  have hN' : ∀ i j : ℤ, p (i, j + 1) = ((p (i, j)).1, !(p (i, j)).2) := fun i j => by
    have := hN (i, j); rwa [Prod.mk_add_mk, add_zero] at this
  have a1 : (p (i, j)).1 = xor (p (0, j)).1 (par i) :=
    eq_xor_par (q := fun i => (p (i, j)).1) (fun i => by simp only [hE']) i
  have a2 : (p (i, j)).2 = (p (0, j)).2 :=
    eq_const (q := fun i => (p (i, j)).2) (fun i => by simp only [hE']) i
  have b1 : (p (0, j)).1 = (p (0, 0)).1 :=
    eq_const (q := fun j => (p (0, j)).1) (fun j => by simp only [hN']) j
  have b2 : (p (0, j)).2 = xor (p (0, 0)).2 (par j) :=
    eq_xor_par (q := fun j => (p (0, j)).2) (fun j => by simp only [hN']) j
  exact Prod.ext (by rw [a1, b1]) (by rw [a2, b2])

/-! ## Thin types (`app:thin`) -/

/-- `app:thin`: the thin types `a, c, d, b` at `ς = (0,0), (1,0), (0,1), (1,1)`. -/
def thinPat : Bool → Bool → Thin
  | false, false => .a
  | true, false => .c
  | false, true => .d
  | true, true => .b

/-- The position of a thin type in the pattern of `app:thin`. -/
def thinInv : Thin → Bool × Bool
  | .a => (false, false)
  | .c => (true, false)
  | .d => (false, true)
  | .b => (true, true)

theorem thinPat_thinInv (θ : Thin) : thinPat (thinInv θ).1 (thinInv θ).2 = θ := by
  cases θ <;> rfl

theorem thinPat_injective {s1 s2 s1' s2' : Bool} (h : thinPat s1 s2 = thinPat s1' s2') :
    s1 = s1' ∧ s2 = s2' := by
  cases s1 <;> cases s2 <;> cases s1' <;> cases s2' <;> simp_all [thinPat]

theorem child_thin (t : Formal) (s1 s2 : Bool) : (t.child s1 s2).thin = thinPat s1 s2 := by
  cases s1 <;> cases s2 <;> rfl

/-- `app:thin` (proof): the thin type of the east neighbour is determined: `a ↔ c`, `b ↔ d`. -/
theorem thinInv_E {θ θ' : Thin} (h : θ.epE = θ'.epW) :
    thinInv θ' = (!(thinInv θ).1, (thinInv θ).2) := by
  revert h; cases θ <;> cases θ' <;> decide

/-- `app:thin` (proof): the thin type of the north neighbour is determined: `a ↔ d`, `b ↔ c`. -/
theorem thinInv_N {θ θ' : Thin} (h : θ.epN = θ'.epS) :
    thinInv θ' = ((thinInv θ).1, !(thinInv θ).2) := by
  revert h; cases θ <;> cases θ' <;> decide

/-- The site `υ + 2v + ς`. -/
def bsite (υ : Bool × Bool) (v : Plane) (s1 s2 : Bool) : Plane :=
  fineSite v s1 s2 + (bitZ υ.1, bitZ υ.2)

theorem exists_bsite (υ : Bool × Bool) (x : Plane) : ∃ v s1 s2, x = bsite υ v s1 s2 := by
  obtain ⟨v, s1, s2, h⟩ := exists_fineSite (x - (bitZ υ.1, bitZ υ.2))
  exact ⟨v, s1, s2, by rw [bsite, ← h]; abel⟩

theorem bsite_false_add_e1 (υ : Bool × Bool) (v : Plane) (s2 : Bool) :
    bsite υ v false s2 + (1, 0) = bsite υ v true s2 := by
  rw [bsite, bsite, add_right_comm, fineSite_false_add_e1]

theorem bsite_true_add_e1 (υ : Bool × Bool) (v : Plane) (s2 : Bool) :
    bsite υ v true s2 + (1, 0) = bsite υ (v + (1, 0)) false s2 := by
  rw [bsite, bsite, add_right_comm, fineSite_true_add_e1]

theorem bsite_false_add_e2 (υ : Bool × Bool) (v : Plane) (s1 : Bool) :
    bsite υ v s1 false + (0, 1) = bsite υ v s1 true := by
  rw [bsite, bsite, add_right_comm, fineSite_false_add_e2]

theorem bsite_true_add_e2 (υ : Bool × Bool) (v : Plane) (s1 : Bool) :
    bsite υ v s1 true + (0, 1) = bsite υ (v + (0, 1)) s1 false := by
  rw [bsite, bsite, add_right_comm, fineSite_true_add_e2]

/-- **`app:thin`.** In a tiling of `𝕆` (every edge matches) there is `υ ∈ {0,1}²` such that the
thin type of the tile at `υ + 2v + ς` is `a, c, d, b` for `ς = (0,0), (1,0), (0,1), (1,1)`. -/
theorem thin_phase {g : Plane → Formal} (hg : LegalOn Formal.MatchE Formal.MatchN Set.univ g) :
    ∃ υ : Bool × Bool, ∀ v s1 s2, (g (bsite υ v s1 s2)).thin = thinPat s1 s2 := by
  have hE : ∀ x, thinInv (g (x + (1, 0))).thin =
      (!(thinInv (g x).thin).1, (thinInv (g x).thin).2) :=
    fun x => thinInv_E (Formal.matchE_iff.1 (hg.1 x trivial trivial)).1
  have hN : ∀ x, thinInv (g (x + (0, 1))).thin =
      ((thinInv (g x).thin).1, !(thinInv (g x).thin).2) :=
    fun x => thinInv_N (Formal.matchN_iff.1 (hg.2 x trivial trivial)).1
  have key := eq_of_flips (p := fun x => thinInv (g x).thin) hE hN
  refine ⟨thinInv (g (0, 0)).thin, fun v s1 s2 => ?_⟩
  have hx := key (bsite (thinInv (g (0, 0)).thin) v s1 s2)
  have e1 : (bsite (thinInv (g (0, 0)).thin) v s1 s2).1 =
      2 * v.1 + bitZ s1 + bitZ (thinInv (g (0, 0)).thin).1 := rfl
  have e2 : (bsite (thinInv (g (0, 0)).thin) v s1 s2).2 =
      2 * v.2 + bitZ s2 + bitZ (thinInv (g (0, 0)).thin).2 := rfl
  simp only [e1, e2, par_fineSite] at hx
  rw [← thinPat_thinInv (g (bsite _ v s1 s2)).thin, hx]
  generalize (thinInv (g (0, 0)).thin).1 = u1
  generalize (thinInv (g (0, 0)).thin).2 = u2
  cases u1 <;> cases u2 <;> cases s1 <;> cases s2 <;> rfl

/-- **`app:thin`**, uniqueness of the coset. -/
theorem thin_phase_unique {g : Plane → Formal} {υ υ' : Bool × Bool}
    (h : ∀ v s1 s2, (g (bsite υ v s1 s2)).thin = thinPat s1 s2)
    (h' : ∀ v s1 s2, (g (bsite υ' v s1 s2)).thin = thinPat s1 s2) : υ = υ' := by
  obtain ⟨v, s1, s2, hx⟩ := exists_bsite υ (bsite υ' 0 false false)
  have h1 := h v s1 s2
  rw [← hx, h' 0 false false] at h1
  obtain ⟨rfl, rfl⟩ := thinPat_injective h1
  obtain ⟨u1, u2⟩ := υ
  obtain ⟨u1', u2'⟩ := υ'
  simp only [bsite, fineSite, Prod.mk_add_mk, Prod.mk.injEq] at hx
  cases u1 <;> cases u2 <;> cases u1' <;> cases u2' <;> simp_all [bitZ] <;> omega

/-! ## Parents (`app:parents`) -/

theorem inO_thin_b {t : Formal} (h : t.inO = true) (hb : t.thin = .b) :
    (∃ k, t.thick = .corner k) ∧ t.black = .A := by
  obtain ⟨θ, κ, ψ⟩ := t
  simp only at hb; subst hb
  rcases κ with k | ⟨α, γ⟩ <;> cases ψ <;> simp_all [Formal.inO]

theorem inO_thin_c {t : Formal} (h : t.inO = true) (hc : t.thin = .c) :
    (∃ α γ, t.thick = .line α γ) ∧ (t.black = .B ∨ t.black = .C) := by
  obtain ⟨θ, κ, ψ⟩ := t
  simp only at hc; subst hc
  rcases κ with k | ⟨α, γ⟩ <;> cases ψ <;> simp_all [Formal.inO]

theorem inO_thin_d {t : Formal} (h : t.inO = true) (hd : t.thin = .d) :
    (∃ α γ, t.thick = .line α γ) ∧ (t.black = .D ∨ t.black = .E) := by
  obtain ⟨θ, κ, ψ⟩ := t
  simp only at hd; subst hd
  rcases κ with k | ⟨α, γ⟩ <;> cases ψ <;> simp_all [Formal.inO]

/-- `F⁻¹` on thick types (a line, which never occurs, goes to `a`). -/
def Finv : Thick → Thin
  | .corner .a => .d
  | .corner .b => .a
  | .corner .c => .c
  | .corner .d => .b
  | .line _ _ => .a

theorem F_Finv (k : Corner) : F (Finv (.corner k)) = k := by cases k <;> rfl

/-- `app:parents`: the parent `t = (F⁻¹(κ₁₁), κ₀₀, ψ₀₀)` read off a block. -/
def parentOf (t00 t11 : Formal) : Formal := ⟨Finv t11.thick, t00.thick, t00.black⟩

/-- **`app:parents`**, first claim: a legal block of `𝕆` on `[0,2)²` with thin types `a, c, d, b`
is `φ(t)` for `t = (F⁻¹(κ₁₁), κ₀₀, ψ₀₀)` (unique by `Formal.child_injective`). -/
theorem parents_eq {t00 t10 t01 t11 : Formal} (h00 : t00.thin = .a) (h10 : t10.thin = .c)
    (h01 : t01.thin = .d) (h11 : t11.thin = .b) (i10 : t10.inO = true) (i01 : t01.inO = true)
    (i11 : t11.inO = true) (mE0 : Formal.MatchE t00 t10) (mE1 : Formal.MatchE t01 t11)
    (mN0 : Formal.MatchN t00 t01) (mN1 : Formal.MatchN t10 t11) :
    (parentOf t00 t11).child false false = t00 ∧ (parentOf t00 t11).child true false = t10 ∧
      (parentOf t00 t11).child false true = t01 ∧ (parentOf t00 t11).child true true = t11 := by
  obtain ⟨⟨k, hk⟩, hA⟩ := inO_thin_b i11 h11
  obtain ⟨⟨α, γ, hl⟩, hBC⟩ := inO_thin_c i10 h10
  obtain ⟨⟨α', γ', hl'⟩, hDE⟩ := inO_thin_d i01 h01
  rw [Formal.matchE_iff] at mE0 mE1
  rw [Formal.matchN_iff] at mN0 mN1
  obtain ⟨θ0, κ0, ψ0⟩ := t00
  obtain ⟨θ1, κ1, ψ1⟩ := t10
  obtain ⟨θ2, κ2, ψ2⟩ := t01
  obtain ⟨θ3, κ3, ψ3⟩ := t11
  simp only at h00 h10 h01 h11 hk hA hl hBC hl' hDE mE0 mE1 mN0 mN1
  subst h00 h10 h01 h11 hk hA hl hl'
  simp only [Thick.epN, Thick.epS, Thick.epE, Thick.epW] at mE0 mE1 mN0 mN1
  have hF := F_Finv k
  refine ⟨rfl, ?_, ?_, ?_⟩
  · simp only [parentOf, Formal.child, Formal.mk.injEq, Thick.line.injEq, true_and]
    refine ⟨⟨?_, mE0.2.1⟩, (se_unique ψ0 ψ1 hBC mE0.2.2.symm).symm⟩
    rw [← F_epS, hF]; exact mN1.2.1.symm
  · simp only [parentOf, Formal.child, Formal.mk.injEq, Thick.line.injEq, true_and]
    refine ⟨⟨mN0.2.1, ?_⟩, (nw_unique ψ0 ψ2 hDE mN0.2.2.symm).symm⟩
    rw [← F_epW, hF]; exact mE1.2.1.symm
  · simp only [parentOf, Formal.child, hF]

/-- `app:parents`: the triples not in `𝕆` whose four children are in `𝕆`, first kind:
`(c, ⟨α, α'⟩, D)` with `α' ≠ r₃`. -/
def badBelow : Formal → Bool
  | ⟨.c, .line _ γ, .D⟩ => γ != .r3
  | _ => false

/-- Second kind: `(d, ⟨α, α'⟩, C)` with `α ≠ r₂`. -/
def badLeft : Formal → Bool
  | ⟨.d, .line α _, .C⟩ => α != .r2
  | _ => false

/-- `app:parents` (proof, second paragraph): if the four children of `t` lie in `𝕆`, then `t ∈ 𝕆`
or `t` is of one of the two kinds (a check over the 400 triples). -/
theorem parents_check : (Formal.all.all fun t =>
    !([false, true].all fun s1 => [false, true].all fun s2 => (t.child s1 s2).inO) || t.inO ||
      badBelow t || badLeft t) = true := by
  decide +kernel

theorem inO_or_bad {t : Formal} (hc : ∀ s1 s2, (t.child s1 s2).inO = true) :
    t.inO = true ∨ badBelow t = true ∨ badLeft t = true := by
  have h := List.all_eq_true.1 parents_check t (Formal.mem_all t)
  have hall : ([false, true].all fun s1 => [false, true].all fun s2 =>
      (t.child s1 s2).inO) = true := by simp [hc]
  rw [hall] at h
  simpa [Bool.or_eq_true, or_assoc] using h

/-- `app:parents` (proof, first kind): a tile of `𝕆` whose north colour is `(g₀, g₀, 0)` is
`(b, ∠d, A)`. -/
theorem below_check1 : (Formal.all.all fun y =>
    !(y.inO && decide (y.colN = (.g0, .g0, false))) ||
      decide (y = ⟨.b, .corner .d, .A⟩)) = true := by
  decide +kernel

/-- `app:parents` (proof, first kind): no tile of `𝕆` has thin north endpoint `g₂`, black north
bit `1` and east colour `(r₃, r₃, 1)`. -/
theorem below_check2 : (Formal.all.all fun p =>
    !(p.inO && decide (p.colN.1 = .g2) && p.colN.2.2 &&
      decide (p.colE = (.r3, .r3, true)))) = true := by
  decide +kernel

/-- `app:parents` (proof, second kind): a tile of `𝕆` whose east colour is `(g₁, g₁, 0)` is
`(b, ∠d, A)`. -/
theorem left_check1 : (Formal.all.all fun s =>
    !(s.inO && decide (s.colE = (.g1, .g1, false))) ||
      decide (s = ⟨.b, .corner .d, .A⟩)) = true := by
  decide +kernel

/-- `app:parents` (proof, second kind): no tile of `𝕆` has north colour `(r₂, r₂, 1)`, thin east
endpoint `g₃` and black east bit `1`. -/
theorem left_check2 : (Formal.all.all fun r =>
    !(r.inO && decide (r.colN = (.r2, .r2, true)) && decide (r.colE.1 = .g3) &&
      r.colE.2.2)) = true := by
  decide +kernel

/-- **`app:parents`**, second claim: if `φ(t)` is a legal block of `𝕆` that extends to a legal
pattern of `𝕆` on `[0,2)² ∪ {(0,-1), (1,-1), (-1,0), (-1,1)}` (tiles `p, y, r, s` there), then
`t ∈ 𝕆`. -/
theorem parent_inO {t p y r s : Formal} (hc : ∀ s1 s2, (t.child s1 s2).inO = true)
    (ip : p.inO = true) (iy : y.inO = true) (ir : r.inO = true) (is : s.inO = true)
    (m1 : Formal.MatchN p (t.child false false)) (m2 : Formal.MatchN y (t.child true false))
    (m3 : Formal.MatchE p y) (m4 : Formal.MatchE r (t.child false false))
    (m5 : Formal.MatchE s (t.child false true)) (m6 : Formal.MatchN r s) : t.inO = true := by
  rcases inO_or_bad hc with h | h | h
  · exact h
  · exfalso
    obtain ⟨θ, κ, ψ⟩ := t
    rcases κ with k | ⟨α, γ⟩ <;> cases θ <;> cases ψ <;> simp [badBelow] at h
    -- `t = (c, ⟨α, γ⟩, D)`: the tile below child `(1,0)` is `(b, ∠d, A)`
    have hy : y = ⟨.b, .corner .d, .A⟩ := by
      have := List.all_eq_true.1 below_check1 y (Formal.mem_all y)
      have hN : y.colN = (.g0, .g0, false) := m2
      simpa [iy, hN] using this
    have hpN : p.colN = (.g2, α, true) := m1
    have hpE : p.colE = (.r3, .r3, true) := by rw [hy] at m3; exact m3
    have := List.all_eq_true.1 below_check2 p (Formal.mem_all p)
    simp [ip, hpN, hpE] at this
  · exfalso
    obtain ⟨θ, κ, ψ⟩ := t
    rcases κ with k | ⟨α, γ⟩ <;> cases θ <;> cases ψ <;> simp [badLeft] at h
    -- `t = (d, ⟨α, γ⟩, C)`: the tile left of child `(0,1)` is `(b, ∠d, A)`
    have hs : s = ⟨.b, .corner .d, .A⟩ := by
      have := List.all_eq_true.1 left_check1 s (Formal.mem_all s)
      have hE : s.colE = (.g1, .g1, false) := m5
      simpa [is, hE] using this
    have hrN : r.colN = (.r2, .r2, true) := by rw [hs] at m6; exact m6
    have hrE : r.colE = (.g3, γ, true) := m4
    have := List.all_eq_true.1 left_check2 r (Formal.mem_all r)
    simp [ir, hrN, hrE] at this

/-! ## Base desubstitution (`app:base-desub`) -/

/-- A tiling of the base set `𝕆`. -/
def IsBaseTiling (g : Plane → Formal) : Prop :=
  (∀ u, (g u).inO = true) ∧ LegalOn Formal.MatchE Formal.MatchN Set.univ g

/-- `sub_υ` on patterns of triples: `subB υ z (υ + 2v + ς) = φ(z(v))(ς)`. -/
def subB (υ : Bool × Bool) (z : Plane → Formal) : Plane → Formal :=
  fun x => subst2 Formal.child z (shiftBy υ x)

theorem shiftBy_bsite (υ : Bool × Bool) (v : Plane) (s1 s2 : Bool) :
    shiftBy υ (bsite υ v s1 s2) = fineSite v s1 s2 := by
  simp [shiftBy, bsite]

theorem subB_bsite (υ : Bool × Bool) (z : Plane → Formal) (v : Plane) (s1 s2 : Bool) :
    subB υ z (bsite υ v s1 s2) = (z v).child s1 s2 := by
  rw [subB, shiftBy_bsite, subst2_fineSite]

theorem subAt_bsite (υ : Bool × Bool) (g : Plane → Letter) (v : Plane) (s1 s2 : Bool) :
    subAt υ g (bsite υ v s1 s2) = (g v).child s1 s2 := by
  rw [subAt, shiftBy_bsite, subst2_fineSite]

/-- **`app:base-desub`**, existence: every tiling `g` of `𝕆` is `sub_υ(z)` for some `υ ∈ {0,1}²`
and some tiling `z` of `𝕆`. As printed: the coset of `app:thin`; each block equals `φ(z(v))`
by `app:parents` (the tiling supplies the cells below and to the left, so `z(v) ∈ 𝕆`); `z` is
legal by `app:sound`(b). -/
theorem base_desub_exists {g : Plane → Formal} (hg : IsBaseTiling g) :
    ∃ υ z, IsBaseTiling z ∧ g = subB υ z := by
  obtain ⟨υ, hυ⟩ := thin_phase hg.2
  have mE : ∀ v s2, Formal.MatchE (g (bsite υ v false s2)) (g (bsite υ v true s2)) := by
    intro v s2
    have := hg.2.1 (bsite υ v false s2) trivial trivial
    rwa [bsite_false_add_e1] at this
  have mN : ∀ v s1, Formal.MatchN (g (bsite υ v s1 false)) (g (bsite υ v s1 true)) := by
    intro v s1
    have := hg.2.2 (bsite υ v s1 false) trivial trivial
    rwa [bsite_false_add_e2] at this
  obtain ⟨z, hz⟩ : ∃ z : Plane → Formal,
      ∀ v, z v = parentOf (g (bsite υ v false false)) (g (bsite υ v true true)) :=
    ⟨_, fun _ => rfl⟩
  have hblock : ∀ v s1 s2, (z v).child s1 s2 = g (bsite υ v s1 s2) := by
    intro v s1 s2
    have hpe := parents_eq (hυ v false false) (hυ v true false) (hυ v false true)
      (hυ v true true) (hg.1 _) (hg.1 _) (hg.1 _) (mE v false) (mE v true) (mN v false)
      (mN v true)
    rw [hz]
    cases s1 <;> cases s2
    exacts [hpe.1, hpe.2.2.1, hpe.2.1, hpe.2.2.2]
  have hgz : g = subB υ z := by
    funext x
    obtain ⟨v, s1, s2, rfl⟩ := exists_bsite υ x
    rw [subB_bsite, hblock]
  refine ⟨υ, z, ⟨fun v => ?_, ?_⟩, hgz⟩
  · -- `z v ∈ 𝕆`: the block of `v` extends below and to the left
    have hc : ∀ s1 s2, ((z v).child s1 s2).inO = true := fun s1 s2 => by
      rw [hblock]; exact hg.1 _
    have eB : ∀ s1, bsite υ (v - (0, 1)) s1 true + (0, 1) = bsite υ v s1 false := fun s1 => by
      rw [bsite_true_add_e2, sub_add_cancel]
    have eL : ∀ s2, bsite υ (v - (1, 0)) true s2 + (1, 0) = bsite υ v false s2 := fun s2 => by
      rw [bsite_true_add_e1, sub_add_cancel]
    refine parent_inO hc (hg.1 (bsite υ (v - (0, 1)) false true))
      (hg.1 (bsite υ (v - (0, 1)) true true)) (hg.1 (bsite υ (v - (1, 0)) true false))
      (hg.1 (bsite υ (v - (1, 0)) true true)) ?_ ?_ ?_ ?_ ?_ ?_
    · rw [hblock, ← eB]; exact hg.2.2 _ trivial trivial
    · rw [hblock, ← eB]; exact hg.2.2 _ trivial trivial
    · have := hg.2.1 (bsite υ (v - (0, 1)) false true) trivial trivial
      rwa [bsite_false_add_e1] at this
    · rw [hblock, ← eL]; exact hg.2.1 _ trivial trivial
    · rw [hblock, ← eL]; exact hg.2.1 _ trivial trivial
    · have := hg.2.2 (bsite υ (v - (1, 0)) true false) trivial trivial
      rwa [bsite_false_add_e2] at this
  · -- `z` is legal: `φ(z)` is a translate of `g` (`app:sound`(b))
    have hsub : subst2 Formal.child z = fun x => g (x + (bitZ υ.1, bitZ υ.2)) := by
      funext x
      obtain ⟨v, s1, s2, rfl⟩ := exists_fineSite x
      rw [subst2_fineSite, hblock]; rfl
    have hl : LegalOn Formal.MatchE Formal.MatchN (fine2 Set.univ) (subst2 Formal.child z) := by
      rw [hsub, fine2_univ]
      exact (hg.2.translate _).mono (fun _ _ => trivial)
    exact Formal.legalOn_phi_iff.1 hl

/-- **`app:base-desub`**, uniqueness: the coset `υ` (by `app:thin`) and `z` (by `app:sound`(c),
`φ` injective). -/
theorem base_desub_unique {g : Plane → Formal} {υ υ' : Bool × Bool} {z z' : Plane → Formal}
    (h : g = subB υ z) (h' : g = subB υ' z') : υ = υ' ∧ z = z' := by
  have hυ : ∀ v s1 s2, (g (bsite υ v s1 s2)).thin = thinPat s1 s2 := fun v s1 s2 => by
    rw [h, subB_bsite, child_thin]
  have hυ' : ∀ v s1 s2, (g (bsite υ' v s1 s2)).thin = thinPat s1 s2 := fun v s1 s2 => by
    rw [h', subB_bsite, child_thin]
  have e := thin_phase_unique hυ hυ'
  refine ⟨e, funext fun v => Formal.child_injective fun s1 s2 => ?_⟩
  have h1 : g (bsite υ v s1 s2) = (z v).child s1 s2 := by rw [h, subB_bsite]
  have h2 : g (bsite υ' v s1 s2) = (z' v).child s1 s2 := by rw [h', subB_bsite]
  rw [← h1, ← h2, e]

/-- **`app:base-desub`**: for every tiling `g` of `𝕆` there are a unique `υ ∈ {0,1}²` and a unique
tiling `z` of `𝕆` with `g(υ + 2v + ς) = φ(z(v))(ς)`. (`𝕆` tiles: the bases of a tiling of `𝔸`,
`exists_letter_tiling`.) -/
theorem base_desub {g : Plane → Formal} (hg : IsBaseTiling g) :
    ∃! p : (Bool × Bool) × (Plane → Formal), IsBaseTiling p.2 ∧ g = subB p.1 p.2 := by
  obtain ⟨υ, z, hz, hgz⟩ := base_desub_exists hg
  refine ⟨(υ, z), ⟨hz, hgz⟩, fun p hp => ?_⟩
  obtain ⟨e1, e2⟩ := base_desub_unique hp.2 hgz
  exact Prod.ext e1 e2

/-! ## The ruler bits (`tab:witness`, `scf:desub`) -/

/-- **`tab:witness`**, columns: of the cells `(2,1)` (child `(0,1)` of child `(1,0)`) and `(2,3)`
(child `(0,1)` of child `(1,1)`) of `φ²(t)`, both of thin type `d`, exactly one is a red
crossing. -/
theorem witness_col (t : Formal) :
    xor ((t.child true false).child false true).thick.IsRedCrossing
      ((t.child true true).child false true).thick.IsRedCrossing = true := by
  obtain ⟨θ, κ, ψ⟩ := t
  cases θ <;> rfl

/-- **`tab:witness`**, rows: of the cells `(1,2)` (child `(1,0)` of child `(0,1)`) and `(3,2)`
(child `(1,0)` of child `(1,1)`), both of thin type `c`, exactly one is a red crossing. -/
theorem witness_row (t : Formal) :
    xor ((t.child false true).child true false).thick.IsRedCrossing
      ((t.child true true).child true false).thick.IsRedCrossing = true := by
  obtain ⟨θ, κ, ψ⟩ := t
  cases θ <;> rfl

theorem IsLetterTiling.base {f : Plane → Letter} (hf : IsLetterTiling f) :
    IsBaseTiling (fun x => (f x).base) :=
  ⟨fun u => (hf.1 u).1, fun u _ _ => (Letter.matchE_iff.1 (hf.2.1 u trivial trivial)).1,
    fun u _ _ => (Letter.matchN_iff.1 (hf.2.2 u trivial trivial)).1⟩

/-- After `scf:def-ruler`: in a tiling, `χ₁` is constant on columns. -/
theorem IsLetterTiling.b1_col {f : Plane → Letter} (hf : IsLetterTiling f) (x : Plane) :
    (f x).b1 = (f (x.1, 0)).b1 := by
  obtain ⟨i, j⟩ := x
  exact eq_const (q := fun j => (f (i, j)).b1) (fun j => by
    have := (hf.2.2 (i, j) trivial trivial).b1_eq
    rw [Prod.mk_add_mk, add_zero] at this
    exact this.symm) j

/-- After `scf:def-ruler`: in a tiling, `χ₂` is constant on rows. -/
theorem IsLetterTiling.b2_row {f : Plane → Letter} (hf : IsLetterTiling f) (x : Plane) :
    (f x).b2 = (f (0, x.2)).b2 := by
  obtain ⟨i, j⟩ := x
  exact eq_const (q := fun i => (f (i, j)).b2) (fun i => by
    have := (hf.2.1 (i, j) trivial trivial).b2_eq
    rw [Prod.mk_add_mk, add_zero] at this
    exact this.symm) i

/-- Proof of `scf:desub`, (R1): if `υ', w` desubstitute the parents `z` of the bases of `f`, the
column `υ₁ + 2(υ'₁ + 2m₁ + 1)` carries the column bit `1` (one of the witness cells `(2,1)`,
`(2,3)` of `φ²(w(m))` is a red crossing of thin type `d`; (R2) and (R4)). -/
theorem col_bit_witness {f : Plane → Letter} (hf : IsLetterTiling f) {υ υ' : Bool × Bool}
    {z w : Plane → Formal} (hbase : ∀ v s1 s2, (f (bsite υ v s1 s2)).base = (z v).child s1 s2)
    (hz : z = subB υ' w) (m : Plane) (s : Bool) :
    (f (bsite υ (bsite υ' m true s) false false)).b1 = true := by
  have hW : ∀ s', (f (bsite υ (bsite υ' m true s') false true)).base =
      ((w m).child true s').child false true := fun s' => by
    rw [hbase, hz, subB_bsite]
  have hcol : ∀ s', (f (bsite υ (bsite υ' m true s') false true)).b1 =
      (f (bsite υ (bsite υ' m true s) false false)).b1 := fun s' => by
    rw [hf.b1_col, hf.b1_col (bsite υ (bsite υ' m true s) false false)]; rfl
  have hrow : ∀ s', (f (bsite υ (bsite υ' m true s') false true)).b2 = false := fun s' => by
    apply (hf.1 (bsite υ (bsite υ' m true s') false true)).2.2.1
    right; rw [hW, child_thin]; rfl
  have hwit := witness_col (w m)
  cases h1 : (((w m).child true false).child false true).thick.IsRedCrossing
  · have h2 : (((w m).child true true).child false true).thick.IsRedCrossing = true := by
      rw [h1] at hwit; simpa using hwit
    have hne := (hf.1 (bsite υ (bsite υ' m true true) false true)).2.2.2.2 (by rw [hW]; exact h2)
    rw [hrow true] at hne
    rw [← hcol true]
    simpa using hne
  · have hne := (hf.1 (bsite υ (bsite υ' m true false) false true)).2.2.2.2 (by rw [hW]; exact h1)
    rw [hrow false] at hne
    rw [← hcol false]
    simpa using hne

/-- Proof of `scf:desub`, (R2): the row `υ₂ + 2(υ'₂ + 2m₂ + 1)` carries the row bit `1`. -/
theorem row_bit_witness {f : Plane → Letter} (hf : IsLetterTiling f) {υ υ' : Bool × Bool}
    {z w : Plane → Formal} (hbase : ∀ v s1 s2, (f (bsite υ v s1 s2)).base = (z v).child s1 s2)
    (hz : z = subB υ' w) (m : Plane) (s : Bool) :
    (f (bsite υ (bsite υ' m s true) false false)).b2 = true := by
  have hW : ∀ s', (f (bsite υ (bsite υ' m s' true) true false)).base =
      ((w m).child s' true).child true false := fun s' => by
    rw [hbase, hz, subB_bsite]
  have hrw : ∀ s', (f (bsite υ (bsite υ' m s' true) true false)).b2 =
      (f (bsite υ (bsite υ' m s true) false false)).b2 := fun s' => by
    rw [hf.b2_row, hf.b2_row (bsite υ (bsite υ' m s true) false false)]; rfl
  have hcl : ∀ s', (f (bsite υ (bsite υ' m s' true) true false)).b1 = false := fun s' => by
    apply (hf.1 (bsite υ (bsite υ' m s' true) true false)).2.1
    right; rw [hW, child_thin]; rfl
  have hwit := witness_row (w m)
  cases h1 : (((w m).child false true).child true false).thick.IsRedCrossing
  · have h2 : (((w m).child true true).child true false).thick.IsRedCrossing = true := by
      rw [h1] at hwit; simpa using hwit
    have hne := (hf.1 (bsite υ (bsite υ' m true true) true false)).2.2.2.2 (by rw [hW]; exact h2)
    rw [hcl true] at hne
    rw [← hrw true]
    simpa using hne.symm
  · have hne := (hf.1 (bsite υ (bsite υ' m false true) true false)).2.2.2.2 (by rw [hW]; exact h1)
    rw [hcl false] at hne
    rw [← hrw false]
    simpa using hne.symm

/-- **`scf:desub`**, existence: every tiling `f` of `𝔸` is `sub_υ(g)` for some `υ ∈ {0,1}²` and
some tiling `g` of `𝔸`. As printed: the bases by `app:base-desub`; the bits of `g(v)` are the
complements of the bits of `f(υ + 2v)`; (R3), (R4) for `g(v)` from those of `f(υ + 2v)`; (R1),
(R2) from a second base desubstitution and `tab:witness`. -/
theorem desub_exists {f : Plane → Letter} (hf : IsLetterTiling f) :
    ∃ υ g, IsLetterTiling g ∧ f = subAt υ g := by
  obtain ⟨υ, z, hz, hfz⟩ := base_desub_exists hf.base
  have hbase : ∀ v s1 s2, (f (bsite υ v s1 s2)).base = (z v).child s1 s2 := fun v s1 s2 => by
    rw [← subB_bsite υ z v s1 s2, ← hfz]
  obtain ⟨υ', w, -, hzw⟩ := base_desub_exists hz
  obtain ⟨g, hg⟩ : ∃ g : Plane → Letter, ∀ v, g v =
      ⟨z v, !(f (bsite υ v false false)).b1, !(f (bsite υ v false false)).b2⟩ :=
    ⟨_, fun _ => rfl⟩
  have hblock : ∀ v s1 s2, (g v).child s1 s2 = f (bsite υ v s1 s2) := by
    intro v s1 s2
    have e1 := hbase v s1 s2
    have e2 : (f (bsite υ v s1 s2)).b1 =
        if s1 then false else (f (bsite υ v false false)).b1 := by
      have hc : (f (bsite υ v s1 s2)).b1 = (f (bsite υ v s1 false)).b1 := by
        rw [hf.b1_col, hf.b1_col (bsite υ v s1 false)]; rfl
      rw [hc]
      cases s1
      · rw [if_neg Bool.false_ne_true]
      · rw [if_pos rfl]
        apply (hf.1 _).2.1
        right; rw [hbase, child_thin]; rfl
    have e3 : (f (bsite υ v s1 s2)).b2 =
        if s2 then false else (f (bsite υ v false false)).b2 := by
      have hc : (f (bsite υ v s1 s2)).b2 = (f (bsite υ v false s2)).b2 := by
        rw [hf.b2_row, hf.b2_row (bsite υ v false s2)]; rfl
      rw [hc]
      cases s2
      · rw [if_neg Bool.false_ne_true]
      · rw [if_pos rfl]
        apply (hf.1 _).2.2.1
        right; rw [hbase, child_thin]; rfl
    rw [hg]
    generalize f (bsite υ v s1 s2) = x at e1 e2 e3
    obtain ⟨xb, x1, x2⟩ := x
    simp only at e1 e2 e3
    subst e1 e2 e3
    simp [Letter.child]
  have hInA : ∀ v, (g v).InA := by
    intro v
    have hA := hf.1 (bsite υ v false false)
    rw [← hblock v false false] at hA
    obtain ⟨-, -, -, hR3, hR4⟩ := hA
    refine ⟨?_, ?_, ?_, fun hc => ?_, fun hc => ?_⟩
    · rw [hg]; exact hz.1 v
    · -- (R1)
      obtain ⟨m, s1', s2', rfl⟩ := exists_bsite υ' v
      have ht : (z (bsite υ' m s1' s2')).thin = thinPat s1' s2' := by
        rw [hzw, subB_bsite, child_thin]
      rw [hg]
      simp only
      rw [ht]
      intro hth
      cases s1'
      · cases s2' <;> simp [thinPat] at hth
      · rw [col_bit_witness hf hbase hzw m s2']; rfl
    · -- (R2)
      obtain ⟨m, s1', s2', rfl⟩ := exists_bsite υ' v
      have ht : (z (bsite υ' m s1' s2')).thin = thinPat s1' s2' := by
        rw [hzw, subB_bsite, child_thin]
      rw [hg]
      simp only
      rw [ht]
      intro hth
      cases s2'
      · cases s1' <;> simp [thinPat] at hth
      · rw [row_bit_witness hf hbase hzw m s1']; rfl
    · -- (R3)
      have h' : (!(g v).b1) = !(g v).b2 := hR3 hc
      exact Bool.not_inj h'
    · -- (R4)
      have h' : (!(g v).b1) ≠ !(g v).b2 := hR4 hc
      exact fun h => h' (by rw [h])
  have hgt : IsLetterTiling g := by
    refine ⟨hInA, ?_⟩
    have hsub : subst2 Letter.child g = fun x => f (x + (bitZ υ.1, bitZ υ.2)) := by
      funext x
      obtain ⟨v, s1, s2, rfl⟩ := exists_fineSite x
      rw [subst2_fineSite, hblock]; rfl
    have hl : LegalOn Letter.MatchE Letter.MatchN (fine2 Set.univ) (subst2 Letter.child g) := by
      rw [hsub, fine2_univ]
      exact (hf.2.translate _).mono (fun _ _ => trivial)
    exact Letter.legalOn_phi'_iff.1 hl
  refine ⟨υ, g, hgt, ?_⟩
  funext x
  obtain ⟨v, s1, s2, rfl⟩ := exists_bsite υ x
  rw [subAt_bsite, hblock]

/-- **`scf:desub`**, uniqueness: `υ` by `app:thin` (on the bases) and `g` by injectivity of `φ'`
(`app:ruler-sound`(c)). -/
theorem desub_unique {f : Plane → Letter} {υ υ' : Bool × Bool} {g g' : Plane → Letter}
    (h : f = subAt υ g) (h' : f = subAt υ' g') : υ = υ' ∧ g = g' := by
  have hb : (fun x => (f x).base) = subB υ (fun v => (g v).base) := by rw [h]; rfl
  have hb' : (fun x => (f x).base) = subB υ' (fun v => (g' v).base) := by rw [h']; rfl
  have e := (base_desub_unique hb hb').1
  refine ⟨e, funext fun v => Letter.child_injective fun s1 s2 => ?_⟩
  have h1 : f (bsite υ v s1 s2) = (g v).child s1 s2 := by rw [h, subAt_bsite]
  have h2 : f (bsite υ' v s1 s2) = (g' v).child s1 s2 := by rw [h', subAt_bsite]
  rw [← h1, ← h2, e]

/-- **`scf:desub`** (last claim): for every tiling `f` of `𝔸` there are a unique `υ ∈ {0,1}²` and a
unique tiling `g` of `𝔸` with `f(υ + 2v + ς) = φ'(g(v))(ς)` for all `v ∈ ℤ²`, `ς ∈ [0,2)²`. The
other claims of `scf:desub` are `exists_letter_tiling` (`𝔸` tiles), `Letter.child_injective`
(`φ'` injective) and `Letter.legalOn_phi'_iff` (`φ'(w)` legal iff `w` legal). -/
theorem desub {f : Plane → Letter} (hf : IsLetterTiling f) :
    ∃! p : (Bool × Bool) × (Plane → Letter), IsLetterTiling p.2 ∧ f = subAt p.1 p.2 := by
  obtain ⟨υ, g, hg, hfg⟩ := desub_exists hf
  refine ⟨(υ, g), ⟨hg, hfg⟩, fun p hp => ?_⟩
  obtain ⟨e1, e2⟩ := desub_unique hp.2 hfg
  exact Prod.ext e1 e2

end UPD.Scaffold

/-
# Section 3.4: the quarter encoding and the rigidity of `𝔸^q` (`scf:quarter`,
# `prop:quarter-ti`(a) first claim, (b))

New in this project.

* **`scf:quarter`**: every tiling `Y` of `𝔸^q` is `ξ ↦ f^q(ξ - ε)` for a unique `ε ∈ {0,1}²` and
  a unique tiling `f` of `𝔸` (`quarter_exists`, `quarter_unique`); conversely every such map is a
  tiling (`isQTiling_qshift`). The quarter phase `τ(Y) = ε + 2ϖ(f)` (`IsQPhase`, digits
  `ε, υ₀, υ₁, …`), unique (`IsQPhase.unique`); `τ(T_a Y) = τ(Y) + a` (`qphase_shift`); and
  `τ(Y) mod 2^l` is determined by `Y` on `[-ρ_l, ρ_l]²` (`qphase_local`).
* **`prop:quarter-ti`** (a), first claim: for every resolving `τ` there is exactly one tiling of
  `𝔸^q` with quarter phase `τ` (`quarter_ti_a`); (b) rigidity (`quarter_rigid`).
-/
import UndecidablePhaseDiagram.Scaffold.Phase
import UndecidablePhaseDiagram.Scaffold.Quarters

set_option autoImplicit false

namespace UPD.Scaffold

/-- A tiling of `𝔸^q`: a map `ℤ² → 𝔸^q` whose colours match on every edge. -/
def IsQTiling (Y : Plane → Quarter) : Prop := LegalOn Quarter.MatchE Quarter.MatchN Set.univ Y

/-- A tiling of `𝔸` with values in the subtype `𝔸`. -/
def IsATiling (f : Plane → LetterA) : Prop := IsLetterTiling (fun u => (f u).1)

/-- The vector `ε ∈ {0,1}²` as a site. -/
def bvec (ε : Bool × Bool) : Plane := (bitZ ε.1, bitZ ε.2)

/-- `scf:quarter`: the map `ξ ↦ f^q(ξ - ε)`. -/
def qshift (ε : Bool × Bool) (f : Plane → LetterA) : Plane → Quarter :=
  fun ξ => quartering f (ξ - bvec ε)

theorem Quarter.ext' {q q' : Quarter} (h1 : q.quad = q'.quad) (h2 : q.parent = q'.parent) :
    q = q' := by
  cases q; cases q'; simp_all

theorem quad_fineSite (x : Plane) (s1 s2 : Bool) : quad (fineSite x s1 s2) = (s1, s2) := by
  simp only [quad, fineSite, Prod.mk.injEq]
  constructor
  · (set_option backward.isDefEq.respectTransparency false in
      rw [Bool.eq_iff_iff, decide_eq_true_iff])
    cases s1 <;> simp [bitZ]
  · (set_option backward.isDefEq.respectTransparency false in
      rw [Bool.eq_iff_iff, decide_eq_true_iff])
    cases s2 <;> simp [bitZ]

theorem qshift_bsite (ε : Bool × Bool) (f : Plane → LetterA) (x : Plane) (s1 s2 : Bool) :
    qshift ε f (bsite ε x s1 s2) = ⟨(s1, s2), f x⟩ := by
  have e : bsite ε x s1 s2 - bvec ε = fineSite x s1 s2 := by
    simp [bsite, bvec]
  simp only [qshift, e, quartering, quad_fineSite]
  rw [show half (fineSite x s1 s2) = x from fineSite_div x s1 s2]

/-- **`scf:quarter`**, converse: `ξ ↦ f^q(ξ - ε)` is a tiling of `𝔸^q` for every tiling `f`. -/
theorem isQTiling_qshift {f : Plane → LetterA} (hf : IsATiling f) (ε : Bool × Bool) :
    IsQTiling (qshift ε f) := by
  refine (((legalOn_quartering hf).translate (-bvec ε)).mono (fun _ _ => trivial)).congr
    fun u _ => ?_
  show quartering f (u + -bvec ε) = quartering f (u - bvec ε)
  rw [sub_eq_add_neg]

/-- **`scf:quarter`**, existence: every tiling `Y` of `𝔸^q` is `ξ ↦ f^q(ξ - ε)` for some `ε` and
some tiling `f` of `𝔸`. As printed: the quadrants alternate along both axes, the four quarters of
each block `ε + 2x + [0,2)²` have one parent `f(x)`, adjacent blocks have matching parents. -/
theorem quarter_exists {Y : Plane → Quarter} (hY : IsQTiling Y) :
    ∃ ε f, IsATiling f ∧ Y = qshift ε f := by
  have hE : ∀ ξ, (Y (ξ + (1, 0))).quad = (!(Y ξ).quad.1, (Y ξ).quad.2) := fun ξ => by
    have := (Quarter.matchE_iff _ _).1 (hY.1 ξ trivial trivial)
    exact Prod.ext this.1 this.2.1
  have hN : ∀ ξ, (Y (ξ + (0, 1))).quad = ((Y ξ).quad.1, !(Y ξ).quad.2) := fun ξ => by
    have := (Quarter.matchN_iff _ _).1 (hY.2 ξ trivial trivial)
    exact Prod.ext this.2.1 this.1
  have key := eq_of_flips (p := fun ξ => (Y ξ).quad) hE hN
  obtain ⟨ε, hε⟩ : ∃ ε, ε = (Y (0, 0)).quad := ⟨_, rfl⟩
  have hq : ∀ x s1 s2, (Y (bsite ε x s1 s2)).quad = (s1, s2) := by
    intro x s1 s2
    have h1 := key (bsite ε x s1 s2)
    have e1 : (bsite ε x s1 s2).1 = 2 * x.1 + bitZ s1 + bitZ ε.1 := rfl
    have e2 : (bsite ε x s1 s2).2 = 2 * x.2 + bitZ s2 + bitZ ε.2 := rfl
    simp only [e1, e2, par_fineSite, ← hε] at h1
    rw [h1]
    obtain ⟨u1, u2⟩ := ε
    cases u1 <;> cases u2 <;> cases s1 <;> cases s2 <;> rfl
  -- the quarters of a block have one parent
  have pE : ∀ x s2, (Y (bsite ε x true s2)).parent = (Y (bsite ε x false s2)).parent := by
    intro x s2
    have := (Quarter.matchE_iff _ _).1 (hY.1 (bsite ε x false s2) trivial trivial)
    rw [bsite_false_add_e1, hq, hq] at this
    rcases this.2.2 with h | h
    · exact h.2
    · exact absurd h.1 (by simp)
  have pN : ∀ x s1, (Y (bsite ε x s1 true)).parent = (Y (bsite ε x s1 false)).parent := by
    intro x s1
    have := (Quarter.matchN_iff _ _).1 (hY.2 (bsite ε x s1 false) trivial trivial)
    rw [bsite_false_add_e2, hq, hq] at this
    rcases this.2.2 with h | h
    · exact h.2
    · exact absurd h.1 (by simp)
  have hpar : ∀ x s1 s2, (Y (bsite ε x s1 s2)).parent = (Y (bsite ε x false false)).parent := by
    intro x s1 s2
    cases s1 <;> cases s2
    · rfl
    · exact pN x false
    · exact pE x false
    · rw [pN x true, pE x false]
  let f : Plane → LetterA := fun x => (Y (bsite ε x false false)).parent
  have hYf : Y = qshift ε f := by
    funext ξ
    obtain ⟨x, s1, s2, rfl⟩ := exists_bsite ε ξ
    rw [qshift_bsite]
    exact Quarter.ext' (hq x s1 s2) (hpar x s1 s2)
  refine ⟨ε, f, ⟨fun u => (f u).2, fun x _ _ => ?_, fun x _ _ => ?_⟩, hYf⟩
  · have := (Quarter.matchE_iff _ _).1 (hY.1 (bsite ε x true false) trivial trivial)
    rw [bsite_true_add_e1, hq, hq] at this
    rcases this.2.2 with h | h
    · exact absurd h.1 (by simp)
    · have h2 := h.2
      rw [hpar] at h2
      exact h2
  · have := (Quarter.matchN_iff _ _).1 (hY.2 (bsite ε x false true) trivial trivial)
    rw [bsite_true_add_e2, hq, hq] at this
    rcases this.2.2 with h | h
    · exact absurd h.1 (by simp)
    · have h2 := h.2
      rw [hpar] at h2
      exact h2

/-- **`scf:quarter`**, uniqueness of `ε` and `f`. -/
theorem quarter_unique {ε ε' : Bool × Bool} {f f' : Plane → LetterA}
    (h : qshift ε f = qshift ε' f') : ε = ε' ∧ f = f' := by
  have hε : ε = ε' := by
    obtain ⟨x, s1, s2, hx⟩ := exists_bsite ε' (bsite ε 0 false false)
    have h1 := congrFun h (bsite ε 0 false false)
    rw [qshift_bsite] at h1
    rw [hx, qshift_bsite] at h1
    have hq := congrArg Quarter.quad h1
    simp only [Prod.mk.injEq] at hq
    obtain ⟨rfl, rfl⟩ := hq
    obtain ⟨u1, u2⟩ := ε
    obtain ⟨u1', u2'⟩ := ε'
    simp only [bsite, fineSite, Prod.mk_add_mk, Prod.mk.injEq] at hx
    cases u1 <;> cases u2 <;> cases u1' <;> cases u2' <;> simp_all [bitZ] <;> omega
  subst hε
  refine ⟨rfl, funext fun x => ?_⟩
  have h1 := congrFun h (bsite ε x false false)
  rw [qshift_bsite, qshift_bsite] at h1
  exact congrArg Quarter.parent h1

/-! ## The quarter phase -/

/-- `scf:quarter`: `τ` is the quarter phase of `Y`: `Y = (ξ ↦ f^q(ξ - ε))` with `τ = ε + 2ϖ(f)`
(digits `τ_0 = ε`, `τ_{m+1} = υ_m`). -/
def IsQPhase (Y : Plane → Quarter) (τ : ℕ → Bool × Bool) : Prop :=
  ∃ f : Plane → LetterA, IsATiling f ∧ Y = qshift (τ 0) f ∧
    IsPhase (fun u => (f u).1) (fun m => τ (m + 1))

theorem exists_qphase {Y : Plane → Quarter} (hY : IsQTiling Y) : ∃ τ, IsQPhase Y τ := by
  obtain ⟨ε, f, hf, rfl⟩ := quarter_exists hY
  obtain ⟨υ, hυ⟩ := exists_tower_of_tiling hf
  exact ⟨dcons ε υ, f, hf, rfl, hυ⟩

theorem IsQPhase.unique {Y : Plane → Quarter} {τ τ' : ℕ → Bool × Bool} (h : IsQPhase Y τ)
    (h' : IsQPhase Y τ') : τ = τ' := by
  obtain ⟨f, -, hY, hφ⟩ := h
  obtain ⟨f', -, hY', hφ'⟩ := h'
  obtain ⟨e0, rfl⟩ := quarter_unique (hY.symm.trans hY')
  have e := hφ.unique hφ'
  funext m
  cases m with
  | zero => exact e0
  | succ m => exact congrFun e m

/-- The digits of `τ` after the first are those of `ϖ(f)`. -/
theorem wsum_qphase (τ : ℕ → Bool × Bool) (l : ℕ) :
    wsum (col τ) (l + 1) = bitZ (τ 0).1 + 2 * wsum (col fun m => τ (m + 1)) l ∧
      wsum (row τ) (l + 1) = bitZ (τ 0).2 + 2 * wsum (row fun m => τ (m + 1)) l :=
  ⟨rfl, rfl⟩

/-- Proof of `scf:quarter`: with `a + ε = ε' + 2b`, `T_a(ξ ↦ f^q(ξ - ε)) = (ξ ↦ (T_b f)^q(ξ - ε'))`.
-/
theorem shift_qshift (ε : Bool × Bool) (f : Plane → LetterA) (a : Plane) :
    shift a (qshift ε f) = qshift (par (a.1 + bitZ ε.1), par (a.2 + bitZ ε.2))
      (shift ((a.1 + bitZ ε.1) / 2, (a.2 + bitZ ε.2) / 2) f) := by
  funext ξ
  obtain ⟨x1, x2⟩ := ξ
  obtain ⟨a1, a2⟩ := a
  simp only [shift, qshift, quartering, bvec, quad, half, par, Prod.mk_sub_mk,
    bitZ_decide_emod_two]
  congr 1
  · ext <;> simp only <;>
      (set_option backward.isDefEq.respectTransparency false in
        rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff]) <;> omega
  · congr 1
    ext <;> simp only <;> omega

/-- **`scf:quarter`**: `τ(T_a Y) = τ(Y) + a`, as `2^l ∣ (τ(T_a Y) mod 2^l) - (τ(Y) mod 2^l) - a`
for every `l`, coordinatewise. -/
theorem qphase_shift {Y : Plane → Quarter} {τ : ℕ → Bool × Bool} (h : IsQPhase Y τ) (a : Plane)
    {τ' : ℕ → Bool × Bool} (h' : IsQPhase (shift a Y) τ') (l : ℕ) :
    (2 : ℤ) ^ l ∣ wsum (col τ') l - wsum (col τ) l - a.1 ∧
      (2 : ℤ) ^ l ∣ wsum (row τ') l - wsum (row τ) l - a.2 := by
  cases l with
  | zero => simp
  | succ l =>
    obtain ⟨f, hf, rfl, hφ⟩ := h
    rw [shift_qshift] at h'
    obtain ⟨ψ, hψ⟩ := exists_tower_of_tiling (hf.shift
      ((a.1 + bitZ (τ 0).1) / 2, (a.2 + bitZ (τ 0).2) / 2))
    have hT : IsQPhase (qshift (par (a.1 + bitZ (τ 0).1), par (a.2 + bitZ (τ 0).2))
        (shift ((a.1 + bitZ (τ 0).1) / 2, (a.2 + bitZ (τ 0).2) / 2) f))
        (dcons (par (a.1 + bitZ (τ 0).1), par (a.2 + bitZ (τ 0).2)) ψ) :=
      ⟨_, hf.shift _, rfl, hψ⟩
    have e := h'.unique hT
    subst e
    obtain ⟨d1, d2⟩ := phase_shift hf hφ _ hψ l
    obtain ⟨w1, w2⟩ := wsum_qphase τ l
    have w3 : wsum (col (dcons (par (a.1 + bitZ (τ 0).1), par (a.2 + bitZ (τ 0).2)) ψ)) (l + 1) =
        bitZ (par (a.1 + bitZ (τ 0).1)) + 2 * wsum (col ψ) l := rfl
    have w4 : wsum (row (dcons (par (a.1 + bitZ (τ 0).1), par (a.2 + bitZ (τ 0).2)) ψ)) (l + 1) =
        bitZ (par (a.2 + bitZ (τ 0).2)) + 2 * wsum (row ψ) l := rfl
    simp only at d1 d2
    rw [w1, w2, w3, w4, par, par, bitZ_decide_emod_two, bitZ_decide_emod_two, pow_succ']
    constructor
    · obtain ⟨k, hk⟩ := d1
      exact ⟨k, by rw [mul_assoc, ← hk]; omega⟩
    · obtain ⟨k, hk⟩ := d2
      exact ⟨k, by rw [mul_assoc, ← hk]; omega⟩

/-- **`scf:quarter`**, last claim: `τ(Y) mod 2^l` is determined by the restriction of `Y` to
`[-ρ_l, ρ_l]²` (`ε` is read off one quarter; the parents on `[-ρ_{l-1}, ρ_{l-1}]²` off the
blocks; then `scf:phase`(b)). -/
theorem qphase_local {Y Y' : Plane → Quarter} {τ τ' : ℕ → Bool × Bool} (h : IsQPhase Y τ)
    (h' : IsQPhase Y' τ') (l : ℕ)
    (hYY : ∀ x : Plane, |x.1| ≤ rho l → |x.2| ≤ rho l → Y x = Y' x) : ∀ m < l, τ m = τ' m := by
  cases l with
  | zero => intro m hm; omega
  | succ l =>
    obtain ⟨f, hf, rfl, hφ⟩ := h
    obtain ⟨f', hf', rfl, hφ'⟩ := h'
    have hz : ∀ (ε : Bool × Bool) (g : Plane → LetterA), (qshift ε g (0, 0)).quad = ε := by
      intro ε g
      obtain ⟨u1, u2⟩ := ε
      cases u1 <;> cases u2 <;> simp [qshift, quartering, quad, bvec, bitZ]
    -- `ε` from the quarter at `0`
    have h0 : τ 0 = τ' 0 := by
      have e := hYY (0, 0) (by simp) (by simp)
      rw [← hz (τ 0) f, ← hz (τ' 0) f', e]
    -- the parents on `[-ρ_l, ρ_l]²`
    have hpar : ∀ x : Plane, |x.1| ≤ rho l → |x.2| ≤ rho l → (f x).1 = (f' x).1 := by
      intro x hx1 hx2
      have e := hYY (bsite (τ 0) x false false) ?_ ?_
      · rw [qshift_bsite, h0, qshift_bsite] at e
        exact congrArg (fun q : Quarter => q.parent.1) e
      · simp only [bsite, fineSite, Prod.fst_add, rho]
        have := bitZ_nonneg (τ 0).1; have := bitZ_le_one (τ 0).1
        rw [abs_le] at hx1 ⊢; simp only [bitZ, Bool.false_eq_true, ↓reduceIte]
        push_cast; constructor <;> omega
      · simp only [bsite, fineSite, Prod.snd_add, rho]
        have := bitZ_nonneg (τ 0).2; have := bitZ_le_one (τ 0).2
        rw [abs_le] at hx2 ⊢; simp only [bitZ, Bool.false_eq_true, ↓reduceIte]
        push_cast; constructor <;> omega
    have hl := phase_local hφ hφ' l hpar
    intro m hm
    cases m with
    | zero => exact h0
    | succ m => exact hl m (by omega)

/-! ## `prop:quarter-ti` -/

/-- After `scf:quarter`: a quarter phase `τ` is *resolving* if `(τ - ε)/2` is, `ε ≡ τ (mod 2)`
(the digits after the first). -/
def QResolving (τ : ℕ → Bool × Bool) : Prop := Resolving (fun m => τ (m + 1))

/-- **`prop:quarter-ti`(a)**, first claim: for every resolving `τ` there is exactly one tiling of
`𝔸^q` with quarter phase `τ`: `Y_τ(ξ) = f_ϖ^q(ξ - ε)` (`scf:quarter`, `prop:scaffold-ti`(a)). -/
theorem quarter_ti_a {τ : ℕ → Bool × Bool} (hτ : QResolving τ) :
    ∃! Y : Plane → Quarter, IsQTiling Y ∧ IsQPhase Y τ := by
  obtain ⟨g, ⟨hg, hgφ⟩, hguniq⟩ := scaffold_ti_a hτ
  let f : Plane → LetterA := fun u => ⟨g u, hg.1 u⟩
  have hf : IsATiling f := hg
  refine ⟨qshift (τ 0) f, ⟨isQTiling_qshift hf _, f, hf, rfl, hgφ⟩, fun Y hY => ?_⟩
  obtain ⟨-, f', hf', rfl, hφ'⟩ := hY
  have e := hguniq _ ⟨hf', hφ'⟩
  congr 1
  funext u
  exact Subtype.ext (congrFun e u)

/-- `ε` is read off the quadrant of one quarter. -/
theorem eps_eq_of_quad {ε ε' : Bool × Bool} {f f' : Plane → LetterA} {x : Plane}
    (h : (qshift ε f (bsite ε x false false)).quad = (qshift ε' f' (bsite ε x false false)).quad) :
    ε = ε' := by
  obtain ⟨y, s1, s2, hy⟩ := exists_bsite ε' (bsite ε x false false)
  rw [qshift_bsite] at h
  rw [hy, qshift_bsite] at h
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨u1, u2⟩ := ε
  obtain ⟨u1', u2'⟩ := ε'
  simp only [bsite, fineSite, Prod.mk_add_mk, Prod.mk.injEq] at hy
  cases u1 <;> cases u2 <;> cases u1' <;> cases u2' <;> simp_all [bitZ] <;> omega

/-- **`prop:quarter-ti`(b)**: if `Y` is a tiling of `𝔸^q` with resolving phase and `Y'` is a tiling
of `𝔸^q` that agrees with `Y` outside a finite set `D`, then `Y' = Y`. As printed: the checker
phase `ε` is not changed (one quarter outside `D`), the parents form a finite modification of
`f`, and `prop:scaffold-ti`(c). -/
theorem quarter_rigid {Y Y' : Plane → Quarter} (hY' : IsQTiling Y') {τ : ℕ → Bool × Bool}
    (hφ : IsQPhase Y τ) (hτ : QResolving τ) (D : Finset Plane)
    (hD : ∀ ξ, ξ ∉ D → Y' ξ = Y ξ) : Y' = Y := by
  obtain ⟨f, hf, rfl, hfφ⟩ := hφ
  obtain ⟨ε', f', hf', rfl⟩ := quarter_exists hY'
  -- a block far from `D`
  let N : ℤ := ((D.sup fun d : Plane => d.1.natAbs : ℕ) : ℤ) + 1
  have hfar : ∀ s1 s2, bsite (τ 0) (N, 0) s1 s2 ∉ D := by
    intro s1 s2 hmem
    have hle := Finset.le_sup (f := fun d : Plane => d.1.natAbs) hmem
    have hb1 := bitZ_nonneg s1; have hb2 := bitZ_nonneg (τ 0).1
    have hnn : 0 ≤ (bsite (τ 0) (N, 0) s1 s2).1 := by
      simp only [bsite, fineSite, Prod.fst_add, N]; omega
    have habs := Int.natAbs_of_nonneg hnn
    have hle' : (((bsite (τ 0) (N, 0) s1 s2).1.natAbs : ℕ) : ℤ) ≤
        ((D.sup fun d : Plane => d.1.natAbs : ℕ) : ℤ) := by exact_mod_cast hle
    rw [habs] at hle'
    simp only [bsite, fineSite, Prod.fst_add, N] at hle'
    omega
  have hε : τ 0 = ε' := by
    apply eps_eq_of_quad (f := f) (f' := f') (x := (N, 0))
    rw [hD _ (hfar false false)]
  subst hε
  -- the parents agree off the blocks that meet `D`
  let D' : Finset Plane := D.image fun ξ => half (ξ - bvec (τ 0))
  have hD' : ∀ x, x ∉ D' → (f' x).1 = (f x).1 := by
    intro x hx
    have hnot : bsite (τ 0) x false false ∉ D := by
      intro hmem
      apply hx
      refine Finset.mem_image.2 ⟨_, hmem, ?_⟩
      have e : bsite (τ 0) x false false - bvec (τ 0) = fineSite x false false := by
        simp [bsite, bvec]
      rw [e]; exact fineSite_div x false false
    have e := hD _ hnot
    rw [qshift_bsite, qshift_bsite] at e
    exact congrArg (fun q : Quarter => q.parent.1) e
  have hff := scaffold_rigid hf hf' hfφ hτ D' hD'
  have : f' = f := funext fun u => Subtype.ext (congrFun hff u)
  rw [this]

end UPD.Scaffold

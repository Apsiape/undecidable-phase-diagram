/-
# Section 3.3: phases, the coincidence and the rigidity of `𝔸` (`scf:phase`, `scf:coincidence`,
# `prop:scaffold-ti`(a), (c))

New in this project.

* Towers of tilings (Section 3.3, "Applying `scf:desub` repeatedly, every tiling `f` of `𝔸` has a
  unique tower"): `exists_tower_of_tiling`, `tower_unique`. The phase `ϖ(f) ∈ ℤ₂²` is the digit
  sequence `υ` of the tower (decision D9); `IsPhase f υ`.
* **`scf:phase`** (a) `phase_shift`: `ϖ(T_a f) = ϖ(f) + a`, as `2^l ∣ (ϖ(T_a f) mod 2^l) -
  (ϖ(f) mod 2^l) - a` for every `l` (coordinatewise); (b) `phase_local`: the digits of `ϖ(f)` below
  `l` are determined by the restriction of `f` to the box `[-ρ_l, ρ_l]²`, `ρ_l = 2^{l+1} - 2`;
  (c) `exists_phase`: every phase occurs.
  **[choice] (proof side)** (b) is proved directly (the parents of a block are read off the block,
  `app:thin` reads the first digit off one tile) instead of by compactness; the printed
  statement ("there is `ρ_l`") is the same.
* **`scf:coincidence`** (`coincidence`) and `scf:def-resolving` (`Resolving`).
* **`prop:scaffold-ti`** (a) `scaffold_ti_a`: exactly one tiling with a given resolving phase;
  (c) `scaffold_rigid`: a tiling with resolving phase admits no finite modification.
-/
import UndecidablePhaseDiagram.Scaffold.Desub

set_option autoImplicit false

namespace UPD.Scaffold

/-! ## Towers of tilings -/

/-- The phase of a tiling: `υ` is the digit sequence of its tower (`ϖ(f) = Σ 2^m υ_m`). -/
def IsPhase (f : Plane → Letter) (υ : ℕ → Bool × Bool) : Prop :=
  ∃ F : ℕ → Plane → Letter, IsInfTower υ F ∧ F 0 = f

/-- Section 3.3: every tiling of `𝔸` has a tower (`scf:desub`, applied repeatedly). -/
theorem exists_tower_of_tiling {f : Plane → Letter} (hf : IsLetterTiling f) :
    ∃ υ, IsPhase f υ := by
  choose U G hG hfG using fun (g : {g : Plane → Letter // IsLetterTiling g}) => desub_exists g.2
  let seq : ℕ → {g : Plane → Letter // IsLetterTiling g} :=
    fun m => Nat.rec ⟨f, hf⟩ (fun _ s => ⟨G s, hG s⟩) m
  exact ⟨fun m => U (seq m), fun m => (seq m).1,
    ⟨fun m => (seq m).2, fun m => hfG (seq m)⟩, rfl⟩

/-- Section 3.3: the tower of a tiling is unique (`scf:desub`, uniqueness). -/
theorem tower_unique {υ υ' : ℕ → Bool × Bool} {F F' : ℕ → Plane → Letter}
    (hF : IsInfTower υ F) (hF' : IsInfTower υ' F') (h0 : F 0 = F' 0) : υ = υ' ∧ F = F' := by
  have hall : ∀ m, F m = F' m := by
    intro m
    induction m with
    | zero => exact h0
    | succ m ih => exact (desub_unique (hF.rel m) (ih ▸ hF'.rel m)).2
  refine ⟨funext fun m => ?_, funext hall⟩
  exact (desub_unique (hF.rel m) ((hall m) ▸ hF'.rel m)).1

/-- The phase of a tiling is unique. -/
theorem IsPhase.unique {f : Plane → Letter} {υ υ' : ℕ → Bool × Bool} (h : IsPhase f υ)
    (h' : IsPhase f υ') : υ = υ' := by
  obtain ⟨F, hF, rfl⟩ := h
  obtain ⟨F', hF', h0⟩ := h'
  exact (tower_unique hF hF' h0.symm).1

theorem IsInfTower.tail {υ : ℕ → Bool × Bool} {F : ℕ → Plane → Letter} (hF : IsInfTower υ F) :
    IsInfTower (fun m => υ (m + 1)) (fun m => F (m + 1)) :=
  ⟨fun m => hF.tiling (m + 1), fun m => hF.rel (m + 1)⟩

/-- **`scf:phase`(c)**: for every phase there is a tiling of `𝔸` with that phase (`exists_tower`,
the printed compactness argument). -/
theorem exists_phase (υ : ℕ → Bool × Bool) : ∃ f, IsLetterTiling f ∧ IsPhase f υ := by
  obtain ⟨F, hF⟩ := exists_tower υ
  exact ⟨F 0, hF.tiling 0, F, hF, rfl⟩

/-! ## `scf:phase`(b): the phase is local -/

/-- The site `0 = υ + 2v + υ` with `v = -υ`. -/
theorem zero_eq_bsite (u : Bool × Bool) :
    ((0, 0) : Plane) = bsite u (-bitZ u.1, -bitZ u.2) u.1 u.2 := by
  simp only [bsite, fineSite, Prod.mk_add_mk, Prod.mk.injEq]
  constructor <;> ring

/-- The first digit is read off the thin type of `f(0)` (`app:thin`). -/
theorem thin_zero {υ : ℕ → Bool × Bool} {F : ℕ → Plane → Letter} (hF : IsInfTower υ F) :
    (F 0 (0, 0)).base.thin = thinPat (υ 0).1 (υ 0).2 := by
  rw [zero_eq_bsite (υ 0), hF.rel 0, subAt_bsite]
  exact child_thin _ _ _

/-- `ρ_l = 2^{l+1} - 2`: `ρ_0 = 0`, `ρ_{l+1} = 2ρ_l + 2`. -/
def rho : ℕ → ℕ
  | 0 => 0
  | l + 1 => 2 * rho l + 2

/-- **`scf:phase`(b)**: if two tilings agree on `[-ρ_l, ρ_l]²`, their phases agree modulo `2^l`
(their digits below `l` agree). -/
theorem phase_local {f f' : Plane → Letter} {υ υ' : ℕ → Bool × Bool} (h : IsPhase f υ)
    (h' : IsPhase f' υ') (l : ℕ)
    (hff : ∀ x : Plane, |x.1| ≤ rho l → |x.2| ≤ rho l → f x = f' x) : ∀ m < l, υ m = υ' m := by
  induction l generalizing f f' υ υ' with
  | zero => intro m hm; omega
  | succ l ih =>
    obtain ⟨F, hF, rfl⟩ := h
    obtain ⟨F', hF', rfl⟩ := h'
    have h0 : υ 0 = υ' 0 := by
      have e := hff (0, 0) (by simp) (by simp)
      have t1 := thin_zero hF
      have t2 := thin_zero hF'
      rw [e, t2] at t1
      obtain ⟨e1, e2⟩ := thinPat_injective t1
      exact Prod.ext e1.symm e2.symm
    have h1 : ∀ x : Plane, |x.1| ≤ rho l → |x.2| ≤ rho l → F 1 x = F' 1 x := by
      intro x hx1 hx2
      apply Letter.child_injective
      intro s1 s2
      rw [← subAt_bsite (υ 0) (F 1) x s1 s2, ← hF.rel 0, ← subAt_bsite (υ' 0) (F' 1) x s1 s2,
        ← hF'.rel 0, ← h0]
      apply hff
      · simp only [bsite, fineSite, Prod.fst_add, rho]
        have := bitZ_nonneg s1; have := bitZ_le_one s1
        have := bitZ_nonneg (υ 0).1; have := bitZ_le_one (υ 0).1
        rw [abs_le] at hx1 ⊢; push_cast; constructor <;> omega
      · simp only [bsite, fineSite, Prod.snd_add, rho]
        have := bitZ_nonneg s2; have := bitZ_le_one s2
        have := bitZ_nonneg (υ 0).2; have := bitZ_le_one (υ 0).2
        rw [abs_le] at hx2 ⊢; push_cast; constructor <;> omega
    have ih' := ih ⟨fun m => F (m + 1), hF.tail, rfl⟩ ⟨fun m => F' (m + 1), hF'.tail, rfl⟩ h1
    intro m hm
    cases m with
    | zero => exact h0
    | succ m => exact ih' m (by omega)

/-! ## `scf:phase`(a): translations -/

/-- Translates of tilings are tilings (`T_a f = shift a f`, `(T_a f)(x) = f(x - a)`). -/
theorem IsLetterTiling.shift {f : Plane → Letter} (hf : IsLetterTiling f) (a : Plane) :
    IsLetterTiling (shift a f) := by
  refine ⟨fun u => hf.1 _, ?_⟩
  refine ((hf.2.translate (-a)).mono (fun _ _ => trivial)).congr fun u _ => ?_
  show f (u + -a) = f (u - a)
  rw [sub_eq_add_neg]

/-- Proof of `scf:phase`(a): with `u + a = u' + 2b` (`u' ∈ {0,1}²`),
`T_a(sub_u(g)) = sub_{u'}(T_b g)`. -/
theorem shift_subAt (u : Bool × Bool) (g : Plane → Letter) (a : Plane) :
    shift a (subAt u g) = subAt (par (a.1 + bitZ u.1), par (a.2 + bitZ u.2))
      (shift ((a.1 + bitZ u.1) / 2, (a.2 + bitZ u.2) / 2) g) := by
  funext x
  obtain ⟨x1, x2⟩ := x
  obtain ⟨a1, a2⟩ := a
  simp only [shift, subAt, subst2, shiftBy, par, Prod.mk_sub_mk, bitZ_decide_emod_two]
  congr 1
  · congr 1
    ext <;> simp only <;> omega
  · (set_option backward.isDefEq.respectTransparency false in
      rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff]); omega
  · (set_option backward.isDefEq.respectTransparency false in
      rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff]); omega

/-- A digit sequence with a given first digit. -/
def dcons (u : Bool × Bool) (υ : ℕ → Bool × Bool) : ℕ → Bool × Bool
  | 0 => u
  | m + 1 => υ m

/-- A sequence of patterns with a given first one. -/
def fcons (f : Plane → Letter) (F : ℕ → Plane → Letter) : ℕ → Plane → Letter
  | 0 => f
  | m + 1 => F m

theorem phase_shift_aux (l : ℕ) : ∀ f : Plane → Letter, IsLetterTiling f →
    ∀ υ, IsPhase f υ → ∀ (a : Plane) υ', IsPhase (shift a f) υ' →
      (2 : ℤ) ^ l ∣ wsum (col υ') l - wsum (col υ) l - a.1 ∧
        (2 : ℤ) ^ l ∣ wsum (row υ') l - wsum (row υ) l - a.2 := by
  induction l with
  | zero => intros; simp
  | succ l ih =>
    intro f hf υ h a υ' h'
    obtain ⟨F, hF, rfl⟩ := h
    have hsh : shift a (F 0) = subAt (par (a.1 + bitZ (υ 0).1), par (a.2 + bitZ (υ 0).2))
        (shift ((a.1 + bitZ (υ 0).1) / 2, (a.2 + bitZ (υ 0).2) / 2) (F 1)) := by
      rw [hF.rel 0]; exact shift_subAt _ _ _
    obtain ⟨υ'', F'', hF'', h0''⟩ :=
      exists_tower_of_tiling ((hF.tiling 1).shift ((a.1 + bitZ (υ 0).1) / 2,
        (a.2 + bitZ (υ 0).2) / 2))
    have hT : IsInfTower (dcons (par (a.1 + bitZ (υ 0).1), par (a.2 + bitZ (υ 0).2)) υ'')
        (fcons (shift a (F 0)) F'') := by
      refine ⟨fun m => ?_, fun m => ?_⟩
      · cases m with
        | zero => exact (hF.tiling 0).shift a
        | succ m => exact hF''.tiling m
      · cases m with
        | zero => show shift a (F 0) = subAt _ (F'' 0); rw [h0'', hsh]; rfl
        | succ m => exact hF''.rel m
    have e := IsPhase.unique h' ⟨_, hT, rfl⟩
    subst e
    obtain ⟨ih1, ih2⟩ := ih (F 1) (hF.tiling 1) _ ⟨fun m => F (m + 1), hF.tail, rfl⟩ _ υ''
      ⟨F'', hF'', h0''⟩
    have w1 : wsum (col (dcons (par (a.1 + bitZ (υ 0).1), par (a.2 + bitZ (υ 0).2)) υ''))
        (l + 1) = bitZ (par (a.1 + bitZ (υ 0).1)) + 2 * wsum (col υ'') l := rfl
    have w2 : wsum (row (dcons (par (a.1 + bitZ (υ 0).1), par (a.2 + bitZ (υ 0).2)) υ''))
        (l + 1) = bitZ (par (a.2 + bitZ (υ 0).2)) + 2 * wsum (row υ'') l := rfl
    have w3 : wsum (col υ) (l + 1) = bitZ (υ 0).1 + 2 * wsum (col fun m => υ (m + 1)) l := rfl
    have w4 : wsum (row υ) (l + 1) = bitZ (υ 0).2 + 2 * wsum (row fun m => υ (m + 1)) l := rfl
    simp only at ih1 ih2
    rw [w1, w2, w3, w4, par, par, bitZ_decide_emod_two, bitZ_decide_emod_two, pow_succ']
    constructor
    · obtain ⟨k, hk⟩ := ih1
      exact ⟨k, by rw [mul_assoc, ← hk]; omega⟩
    · obtain ⟨k, hk⟩ := ih2
      exact ⟨k, by rw [mul_assoc, ← hk]; omega⟩

/-- **`scf:phase`(a)**: `ϖ(T_a f) = ϖ(f) + a`: for every `l`, `ϖ(T_a f) ≡ ϖ(f) + a (mod 2^l)`,
coordinatewise (truncations `ϖ mod 2^l = wsum`). -/
theorem phase_shift {f : Plane → Letter} (hf : IsLetterTiling f) {υ : ℕ → Bool × Bool}
    (h : IsPhase f υ) (a : Plane) {υ' : ℕ → Bool × Bool} (h' : IsPhase (shift a f) υ') (l : ℕ) :
    (2 : ℤ) ^ l ∣ wsum (col υ') l - wsum (col υ) l - a.1 ∧
      (2 : ℤ) ^ l ∣ wsum (row υ') l - wsum (row υ) l - a.2 :=
  phase_shift_aux l f hf υ h a υ' h'

/-! ## `scf:coincidence` and resolving phases -/

/-- `𝔲 = (b, ∠d, A, 0, 0)`. -/
def uLetter : Letter := ⟨⟨.b, .corner .d, .A⟩, false, false⟩

/-- The digit pair `ς_m(x) = (ς_{m,1}(x), ς_{m,2}(x))` of a site (Section 3.3). -/
def digP (υ : ℕ → Bool × Bool) (x : Plane) (m : ℕ) : Bool × Bool :=
  (dig (col υ) m x.1, dig (row υ) m x.2)

/-- Taking the children `ς_{m-1}, …, ς_0` in turn, from a letter at level `m`. -/
def descend (s : ℕ → Bool × Bool) : ℕ → Letter → Letter
  | 0, P => P
  | m + 1, P => descend s m (P.child (s m).1 (s m).2)

/-- Section 3.3: `f(x)` is obtained from `f_m(x^{(m)})` by taking the children
`ς_{m-1}(x), …, ς_0(x)` in turn. -/
theorem tower_descend {υ : ℕ → Bool × Bool} {F : ℕ → Plane → Letter} {h : ℕ}
    (hF : TowerRel υ F h) (x : Plane) {m : ℕ} (hm : m ≤ h) :
    F 0 x = descend (digP υ x) m (F m (ancP υ m x)) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [ih (by omega), hF.chain (by omega) x]
    rfl

/-- **`scf:coincidence`**: if `ς_m(x) = ς_{m+1}(x) = (1,1)`, then `f_m(x^{(m)}) = 𝔲`, and `f(x)` is
determined by `ς_0(x), …, ς_{m-1}(x)`: it is `𝔲` with these children taken in turn. -/
theorem coincidence {υ : ℕ → Bool × Bool} {F : ℕ → Plane → Letter} (hF : IsInfTower υ F)
    (x : Plane) {m : ℕ} (h1 : digP υ x m = (true, true)) (h2 : digP υ x (m + 1) = (true, true)) :
    F m (ancP υ m x) = uLetter ∧ F 0 x = descend (digP υ x) m uLetter := by
  have hm : F m (ancP υ m x) = uLetter := by
    have c1 := (hF.towerRel (m + 2)).chain (by omega : m < m + 2) x
    have c2 := (hF.towerRel (m + 2)).chain (by omega : m + 1 < m + 2) x
    simp only [digP, Prod.mk.injEq] at h1 h2
    rw [h1.1, h1.2] at c1
    rw [h2.1, h2.2] at c2
    rw [c1, c2]; rfl
  exact ⟨hm, by rw [tower_descend (hF.towerRel m) x le_rfl, hm]⟩

/-- **`scf:def-resolving`**: the phase `ϖ` (digits `υ`) is *resolving* if for every `x` the binary
expansion of `x - ϖ` has two consecutive digits, at positions `m` and `m + 1`, both equal to
`(1,1)`. The binary digits of `x - ϖ` are the `ς_m(x)` (`scf:eq-digits`, `emod_eq_wsum_dig`). -/
def Resolving (υ : ℕ → Bool × Bool) : Prop :=
  ∀ x : Plane, ∃ m, digP υ x m = (true, true) ∧ digP υ x (m + 1) = (true, true)

/-- **`prop:scaffold-ti`(a)**: for every resolving phase there is exactly one tiling of `𝔸` with
that phase (existence `scf:phase`(c), uniqueness `scf:coincidence`). -/
theorem scaffold_ti_a {υ : ℕ → Bool × Bool} (hυ : Resolving υ) :
    ∃! f : Plane → Letter, IsLetterTiling f ∧ IsPhase f υ := by
  obtain ⟨f, hf, hφ⟩ := exists_phase υ
  refine ⟨f, ⟨hf, hφ⟩, fun f' hf' => ?_⟩
  obtain ⟨F, hF, rfl⟩ := hφ
  obtain ⟨F', hF', rfl⟩ := hf'.2
  funext x
  obtain ⟨m, h1, h2⟩ := hυ x
  rw [(coincidence hF x h1 h2).2, (coincidence hF' x h1 h2).2]

/-! ## `prop:scaffold-ti`(c): rigidity -/

theorem bitZ_injective {s t : Bool} (h : bitZ s = bitZ t) : s = t := by
  cases s <;> cases t <;> simp_all [bitZ]

/-- Digit sequences with the same truncations are equal. -/
theorem eq_of_wsum_eq {c c' : ℕ → Bool} (h : ∀ l, wsum c l = wsum c' l) : c = c' := by
  funext m
  have h1 := wsum_succ_top c m
  have h2 := wsum_succ_top c' m
  rw [h, h m] at h1
  have hp : (0 : ℤ) < 2 ^ m := by positivity
  have : bitZ (c m) = bitZ (c' m) := by
    have := h1.symm.trans h2
    have h3 : (2 : ℤ) ^ m * bitZ (c m) = 2 ^ m * bitZ (c' m) := by linarith
    exact mul_left_cancel₀ hp.ne' h3
  exact bitZ_injective this

/-- **`prop:scaffold-ti`(c)**: if `f` is a tiling with resolving phase and `f'` is a tiling that
agrees with `f` outside a finite set `D`, then `f' = f`. As printed: for every `l`, translate `D`
away from `[-ρ_l, ρ_l]²` (`scf:phase`(b), (a)), so the phases agree modulo every `2^l`; then
`prop:scaffold-ti`(a). -/
theorem scaffold_rigid {f f' : Plane → Letter} (hf : IsLetterTiling f) (hf' : IsLetterTiling f')
    {υ : ℕ → Bool × Bool} (hφ : IsPhase f υ) (hυ : Resolving υ) (D : Finset Plane)
    (hD : ∀ x, x ∉ D → f' x = f x) : f' = f := by
  obtain ⟨υ', hφ'⟩ := exists_tower_of_tiling hf'
  have hw : ∀ l, wsum (col υ') l = wsum (col υ) l ∧ wsum (row υ') l = wsum (row υ) l := by
    intro l
    -- a translation that moves `[-ρ_l, ρ_l]²` off `D`
    let N : ℤ := ((D.sup fun d : Plane => d.1.natAbs : ℕ) : ℤ) + rho l + 1
    have hoff : ∀ x : Plane, |x.1| ≤ rho l → x + (N, 0) ∉ D := by
      intro x hx hmem
      have hle := Finset.le_sup (f := fun d : Plane => d.1.natAbs) hmem
      have hnn : 0 ≤ (x + (N, 0)).1 := by
        simp only [Prod.fst_add, N]; rw [abs_le] at hx; omega
      have habs := Int.natAbs_of_nonneg hnn
      have hle' : (((x + (N, 0)).1.natAbs : ℕ) : ℤ) ≤
          ((D.sup fun d : Plane => d.1.natAbs : ℕ) : ℤ) := by exact_mod_cast hle
      rw [habs] at hle'
      simp only [Prod.fst_add, N] at hle'
      rw [abs_le] at hx
      omega
    obtain ⟨ψ, hψ⟩ := exists_tower_of_tiling (hf.shift (-(N, 0)))
    obtain ⟨ψ', hψ'⟩ := exists_tower_of_tiling (hf'.shift (-(N, 0)))
    have hloc := phase_local hψ hψ' l (fun x hx1 _ => by
      simp only [shift, sub_neg_eq_add]
      exact (hD _ (hoff x hx1)).symm)
    have e1 : wsum (col ψ) l = wsum (col ψ') l :=
      wsum_congr fun m hm => by simp only [col]; rw [hloc m hm]
    have e2 : wsum (row ψ) l = wsum (row ψ') l :=
      wsum_congr fun m hm => by simp only [row]; rw [hloc m hm]
    obtain ⟨d1, d2⟩ := phase_shift hf hφ _ hψ l
    obtain ⟨d1', d2'⟩ := phase_shift hf' hφ' _ hψ' l
    have hb1 := wsum_nonneg (col υ) l; have hb2 := wsum_lt (col υ) l
    have hb3 := wsum_nonneg (col υ') l; have hb4 := wsum_lt (col υ') l
    have hb5 := wsum_nonneg (row υ) l; have hb6 := wsum_lt (row υ) l
    have hb7 := wsum_nonneg (row υ') l; have hb8 := wsum_lt (row υ') l
    constructor
    · have hd : (2 : ℤ) ^ l ∣ wsum (col υ') l - wsum (col υ) l := by
        have := dvd_sub d1 d1'
        rw [e1] at this
        have e : wsum (col ψ') l - wsum (col υ) l - (-((N, 0) : Plane)).1 -
            (wsum (col ψ') l - wsum (col υ') l - (-((N, 0) : Plane)).1) =
            wsum (col υ') l - wsum (col υ) l := by ring
        rwa [e] at this
      have := Int.eq_zero_of_abs_lt_dvd hd (by rw [abs_lt]; constructor <;> linarith)
      linarith
    · have hd : (2 : ℤ) ^ l ∣ wsum (row υ') l - wsum (row υ) l := by
        have := dvd_sub d2 d2'
        rw [e2] at this
        have e : wsum (row ψ') l - wsum (row υ) l - (-((N, 0) : Plane)).2 -
            (wsum (row ψ') l - wsum (row υ') l - (-((N, 0) : Plane)).2) =
            wsum (row υ') l - wsum (row υ) l := by ring
        rwa [e] at this
      have := Int.eq_zero_of_abs_lt_dvd hd (by rw [abs_lt]; constructor <;> linarith)
      linarith
  have hυυ : υ' = υ := by
    have h1 := eq_of_wsum_eq fun l => (hw l).1
    have h2 := eq_of_wsum_eq fun l => (hw l).2
    funext m
    exact Prod.ext (congrFun h1 m) (congrFun h2 m)
  subst hυυ
  exact (scaffold_ti_a hυ).unique ⟨hf', hφ'⟩ ⟨hf, hφ⟩

end UPD.Scaffold

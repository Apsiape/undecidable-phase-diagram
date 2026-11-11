/-
# Section 3.5 and Appendix A: frames, free coordinates, owners (`scf:def-frames`, `scf:frames`)

Ported from the forgetting core (`C:/Infanox/fixed-noise-ergodicity-lean`,
`FixedNoiseErgodicity/Family/Frames.lean`; same authors), namespace `FNE.Family` → `UPD.Scaffold`
(`fam:frames` → `scf:frames`, `fam:laminar` → `app:laminar`); the forgetting core's phase `1/3`
is not used here. New here: `scf:frames`(c) (the least and largest free coordinate, and the count
`|𝓕_d(m)| = 2^{d+2} - 2` by the recursion `g_{d+1} = 2g_d` of App. A: `card_free`), (d), (e), the
free coordinates `𝓕_d(m)` and the least free coordinate `r_d(m)`.

* `scf:def-frames`: offsets with `a_{d+1} ≡ a_d (mod 4^{d+1})` (`FrameOffsets`); the paper's
  `a_d ∈ [0, 4^{d+1})`, `a_d ≡ τ_i (mod 4^{d+1})`, for `τ_i` with binary digits `t`, is
  `phaseOffsets t d = Σ_{m < 2d+2} 2^m t_m`, and these satisfy it.
* `scf:frames`(a), (b) (ported), (d), (e) (new).
* `app:laminar`, for any family of integer intervals (ported).
* The owner depth `own(z)` (ported).
-/
import UndecidablePhaseDiagram.Scaffold.Quarters

set_option autoImplicit false

namespace UPD.Scaffold

/-! ## Frame offsets -/

/-- `scf:def-frames`: integers `a_d` with `a_{d+1} ≡ a_d (mod 4^{d+1})`. -/
def FrameOffsets (a : ℕ → ℤ) : Prop := ∀ d, a (d + 1) % 4 ^ (d + 1) = a d % 4 ^ (d + 1)

theorem FrameOffsets.emod {a : ℕ → ℤ} (ha : FrameOffsets a) {e d : ℕ} (h : e ≤ d) :
    a d % 4 ^ (e + 1) = a e % 4 ^ (e + 1) := by
  induction d, h using Nat.le_induction with
  | base => rfl
  | succ d hed ih =>
    rw [← ih, ← Int.emod_emod_of_dvd (a (d + 1)) (pow_dvd_pow 4 (by omega : e + 1 ≤ d + 1)), ha d,
      Int.emod_emod_of_dvd _ (pow_dvd_pow 4 (by omega : e + 1 ≤ d + 1))]

/-- The frame offsets of a tower with phase `(ϖ₀, ϖ₀)`: `a_d = 2 (ϖ₀ mod 2^{2d+1})`. -/
def towerOffsets (c : ℕ → Bool) (d : ℕ) : ℤ := 2 * wsum c (2 * d + 1)

theorem four_pow_eq_two_pow (d : ℕ) : (4 : ℤ) ^ (d + 1) = 2 ^ (2 * d + 1 + 1) := by
  rw [show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_mul]; ring_nf

theorem towerOffsets_spec (c : ℕ → Bool) (d : ℕ) :
    towerOffsets c d % 4 ^ (d + 1) = 2 * wsum c (2 * d + 1) % 4 ^ (d + 1) := rfl

theorem frameOffsets_tower (c : ℕ → Bool) : FrameOffsets (towerOffsets c) := by
  intro d
  simp only [towerOffsets]
  rw [four_pow_eq_two_pow, pow_succ, mul_comm (2 ^ (2 * d + 1)) 2,
    Int.mul_emod_mul_of_pos _ _ (by norm_num : (0 : ℤ) < 2),
    Int.mul_emod_mul_of_pos _ _ (by norm_num : (0 : ℤ) < 2),
    wsum_emod _ (by omega : 2 * d + 1 ≤ 2 * (d + 1) + 1), wsum_emod _ le_rfl]

/-! ## `fam:frames` -/

theorem frameLo_lt_frameHi (a : ℕ → ℤ) (d : ℕ) (m : ℤ) : frameLo a d m < frameHi a d m := by
  have : (1 : ℤ) ≤ 4 ^ d := one_le_pow₀ (by norm_num)
  simp only [frameLo, frameHi]; nlinarith

/-- `scf:frames`(a), first claim: frames of the same depth are disjoint. -/
theorem frame_window_unique {a : ℕ → ℤ} {d : ℕ} {m m' : ℤ} {z : ℤ}
    (h : frameLo a d m ≤ z ∧ z ≤ frameHi a d m) (h' : frameLo a d m' ≤ z ∧ z ≤ frameHi a d m') :
    m = m' := by
  have hp : (0 : ℤ) < 4 ^ d := by positivity
  simp only [frameLo, frameHi] at h h'
  generalize (4 : ℤ) ^ d = p at hp h h'
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have : m + 1 ≤ m' := hlt
    nlinarith
  · have : m' + 1 ≤ m := hlt
    nlinarith

/-- `x ≡ ρ (mod M)` when `M ∣ x - ρ` and `0 ≤ ρ < M`. -/
theorem emod_of_dvd_sub {x ρ M : ℤ} (h : M ∣ x - ρ) (h0 : 0 ≤ ρ) (h1 : ρ < M) : x % M = ρ := by
  obtain ⟨k, hk⟩ := h
  rw [show x = ρ + M * k by linarith, Int.add_mul_emod_self_left, Int.emod_eq_of_lt h0 h1]

/-- `scf:frames`(a), second claim: if `e < d`, no endpoint of a frame of depth `d` lies in a frame
of depth `e` (the endpoints are `≡ a_e + 1` and `≡ a_e (mod 4^{e+1})`). -/
theorem endpoint_not_inFrame {a : ℕ → ℤ} (ha : FrameOffsets a) {e d : ℕ} (hed : e < d) (m : ℤ) :
    ¬ InFrame a e (frameLo a d m) ∧ ¬ InFrame a e (frameHi a d m) := by
  have hdvd : (4 : ℤ) ^ (e + 1) ∣ a d - a e := by
    rw [Int.dvd_iff_emod_eq_zero, Int.sub_emod, ha.emod hed.le, Int.sub_self, Int.zero_emod]
  have hdvd' : (4 : ℤ) ^ (e + 1) ∣ 4 ^ d := pow_dvd_pow 4 hed
  have hq : (4 : ℤ) ≤ 4 ^ (e + 1) := le_self_pow₀ (by norm_num) (by omega)
  have hp : (1 : ℤ) ≤ 4 ^ e := one_le_pow₀ (by norm_num)
  have hpe : (4 : ℤ) ^ (e + 1) = 4 * 4 ^ e := by ring
  have r1 : (frameLo a d m - a e) % 4 ^ (e + 1) = 1 := by
    refine emod_of_dvd_sub ?_ (by norm_num) (by linarith)
    have : frameLo a d m - a e - 1 = (a d - a e) + (4 * m + 1) * 4 ^ d := by
      simp only [frameLo]; ring
    rw [this]; exact dvd_add hdvd (Dvd.dvd.mul_left hdvd' _)
  have r0 : (frameHi a d m - a e) % 4 ^ (e + 1) = 0 := by
    refine emod_of_dvd_sub ?_ (by norm_num) (by linarith)
    have : frameHi a d m - a e - 0 = (a d - a e) + (4 * m + 3) * 4 ^ d := by
      simp only [frameHi]; ring
    rw [this]; exact dvd_add hdvd (Dvd.dvd.mul_left hdvd' _)
  rw [inFrame_iff, inFrame_iff, r1, r0]
  constructor <;> omega

/-- **`scf:frames`(a)**: two frames of different depths `e < d` are disjoint, or the one of depth
`e` lies in the interior of the other. -/
theorem frames_nested {a : ℕ → ℤ} (ha : FrameOffsets a) {e d : ℕ} (hed : e < d) (m m' : ℤ) :
    (frameHi a e m' < frameLo a d m ∨ frameHi a d m < frameLo a e m') ∨
      (frameLo a d m < frameLo a e m' ∧ frameHi a e m' < frameHi a d m) := by
  obtain ⟨h1, h2⟩ := endpoint_not_inFrame ha hed m
  simp only [InFrame, not_exists, not_and, not_le] at h1 h2
  have h1 := h1 m'; have h2 := h2 m'
  have := frameLo_lt_frameHi a e m'; have := frameLo_lt_frameHi a d m
  by_contra hc
  push Not at hc
  omega

/-- **`scf:frames`(b)**: if `e < d`, every frame of depth `d` contains a frame of depth `e`. -/
theorem frames_contain (a : ℕ → ℤ) {e d : ℕ} (hed : e < d) (m : ℤ) :
    ∃ m', frameLo a d m ≤ frameLo a e m' ∧ frameHi a e m' ≤ frameHi a d m := by
  -- a left endpoint `p₀` of depth `e` in `[L, L + 4^{e+1})`, `L = frameLo a d m`
  have hM : (0 : ℤ) < 4 ^ (e + 1) := by positivity
  have hp1 : (1 : ℤ) ≤ 4 ^ e := one_le_pow₀ (by norm_num)
  have hMe : (4 : ℤ) ^ (e + 1) = 4 * 4 ^ e := by ring
  obtain ⟨X, hX⟩ : ∃ X, X = a e + 4 ^ e + 1 - frameLo a d m := ⟨_, rfl⟩
  have hdiv := Int.mul_ediv_add_emod X (4 ^ (e + 1))
  have hnn := Int.emod_nonneg X hM.ne'
  have hlt := Int.emod_lt_of_pos X hM
  have hp0 : IsLeftEnd a e (frameLo a d m + X % 4 ^ (e + 1)) := by
    rw [isLeftEnd_iff]
    refine emod_of_dvd_sub ⟨-(X / 4 ^ (e + 1)), by linarith⟩ (by positivity) (by linarith)
  obtain ⟨m', hm'⟩ := hp0
  refine ⟨m', ?_, ?_⟩
  · linarith
  · have he : frameHi a e m' = frameLo a e m' + 2 * 4 ^ e - 1 := by
      simp only [frameLo, frameHi]; ring
    have hd : frameHi a d m = frameLo a d m + 2 * 4 ^ d - 1 := by
      simp only [frameLo, frameHi]; ring
    have hpow : (4 : ℤ) ^ (e + 1) ≤ 4 ^ d := pow_le_pow_right₀ (by norm_num) hed
    rw [he, hd, ← hm']
    linarith

/-! ## `app:laminar` -/

/-- `app:laminar`, hypothesis: a family `𝒥` of integer intervals `[I.1, I.2]` with at least two
points each, any two distinct members disjoint or one in the interior of the other. -/
def Laminar (J : Set (ℤ × ℤ)) : Prop :=
  (∀ I ∈ J, I.1 < I.2) ∧ ∀ I ∈ J, ∀ I' ∈ J, I ≠ I' →
    (I.2 < I'.1 ∨ I'.2 < I.1) ∨ (I'.1 < I.1 ∧ I.2 < I'.2) ∨ (I.1 < I'.1 ∧ I'.2 < I.2)

/-- The endpoints `E` of the members of `𝒥`. -/
def endpts (J : Set (ℤ × ℤ)) : Set ℤ := {e | ∃ I ∈ J, e = I.1 ∨ e = I.2}

/-- **`app:laminar`** (first claim): every endpoint is an endpoint of exactly one member; so it is
a left or a right endpoint, not both. -/
theorem Laminar.endpoint_unique {J : Set (ℤ × ℤ)} (hJ : Laminar J) {I I' : ℤ × ℤ} (hI : I ∈ J)
    (hI' : I' ∈ J) {e : ℤ} (he : e = I.1 ∨ e = I.2) (he' : e = I'.1 ∨ e = I'.2) : I = I' := by
  by_contra hne
  have h1 := hJ.1 I hI; have h2 := hJ.1 I' hI'
  rcases hJ.2 I hI I' hI' hne with h | h | h <;> omega

/-- **`app:laminar`** (second claim): if `w₁ < w₂` are consecutive elements of `E`, `w₁` a left and
`w₂` a right endpoint, then `[w₁, w₂] ∈ 𝒥`. -/
theorem Laminar.mem_of_consecutive {J : Set (ℤ × ℤ)} (hJ : Laminar J) {I I' : ℤ × ℤ} (hI : I ∈ J)
    (hI' : I' ∈ J) (hlt : I.1 < I'.2) (hcons : ∀ e ∈ endpts J, ¬ (I.1 < e ∧ e < I'.2)) :
    (I.1, I'.2) ∈ J := by
  by_cases hne : I = I'
  · subst hne; exact hI
  · exfalso
    have h1 := hJ.1 I hI; have h2 := hJ.1 I' hI'
    have hI2 := hcons I.2 ⟨I, hI, Or.inr rfl⟩
    have hI'1 := hcons I'.1 ⟨I', hI', Or.inl rfl⟩
    rcases hJ.2 I hI I' hI' hne with h | h | h <;> omega

/-- **`app:laminar`** (third claim): if a member `I` contains no other member, its endpoints are
consecutive in `E`. -/
theorem Laminar.consecutive_of_minimal {J : Set (ℤ × ℤ)} (hJ : Laminar J) {I : ℤ × ℤ} (hI : I ∈ J)
    (hmin : ∀ I' ∈ J, I' ≠ I → ¬ (I.1 ≤ I'.1 ∧ I'.2 ≤ I.2)) :
    ∀ e ∈ endpts J, ¬ (I.1 < e ∧ e < I.2) := by
  rintro e ⟨I', hI', he⟩ ⟨h1, h2⟩
  have hne : I' ≠ I := by rintro rfl; omega
  have := hmin I' hI' hne
  have := hJ.1 I' hI'
  rcases hJ.2 I' hI' I hI hne with h | h | h <;> omega

/-! ## Owner depth (`scf:def-frames`) -/

instance (a : ℕ → ℤ) (d : ℕ) : DecidablePred (InFrame a d) := fun z =>
  decidable_of_iff _ (inFrame_iff a d z).symm

/-- `scf:def-frames`: the *owner depth* `own(z)`: the least `d ≥ 1` such that `z` lies in a frame of depth
`d` (when every integer lies in a frame). -/
noncomputable def own (a : ℕ → ℤ) (h : ∀ z, ∃ d, 1 ≤ d ∧ InFrame a d z) (z : ℤ) : ℕ :=
  Nat.find (h z)

theorem own_spec (a : ℕ → ℤ) (h : ∀ z, ∃ d, 1 ≤ d ∧ InFrame a d z) (z : ℤ) :
    1 ≤ own a h z ∧ InFrame a (own a h z) z :=
  Nat.find_spec (h z)

theorem own_le (a : ℕ → ℤ) (h : ∀ z, ∃ d, 1 ≤ d ∧ InFrame a d z) {z : ℤ} {d : ℕ} (hd : 1 ≤ d)
    (hz : InFrame a d z) : own a h z ≤ d :=
  Nat.find_min' (h z) ⟨hd, hz⟩

/-! ## The offsets of a phase -/

/-- `scf:def-frames`: the offset `a_d ∈ [0, 4^{d+1})` with `a_d ≡ τ_i (mod 4^{d+1})`, for the
2-adic integer `τ_i` with binary digits `t` (decision D9): `a_d = τ_i mod 2^{2d+2}`. -/
def phaseOffsets (t : ℕ → Bool) (d : ℕ) : ℤ := wsum t (2 * d + 2)

theorem four_pow_eq_two_pow' (d : ℕ) : (4 : ℤ) ^ (d + 1) = 2 ^ (2 * d + 2) := by
  rw [show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_mul]; ring_nf

/-- `scf:def-frames`: `a_d ∈ [0, 4^{d+1})`. -/
theorem phaseOffsets_mem (t : ℕ → Bool) (d : ℕ) :
    0 ≤ phaseOffsets t d ∧ phaseOffsets t d < 4 ^ (d + 1) := by
  rw [four_pow_eq_two_pow']
  exact ⟨wsum_nonneg _ _, wsum_lt _ _⟩

theorem frameOffsets_phase (t : ℕ → Bool) : FrameOffsets (phaseOffsets t) := by
  intro d
  simp only [phaseOffsets]
  rw [four_pow_eq_two_pow', wsum_emod _ (by omega : 2 * d + 2 ≤ 2 * (d + 1) + 2),
    Int.emod_eq_of_lt (wsum_nonneg _ _) (wsum_lt _ _)]

/-! ## Free coordinates (`scf:def-frames`) and `scf:frames`(c), (d), (e) -/

/-- `scf:def-frames`: `z` is a *free coordinate* of `I_d(m)`: it lies in the interior of `I_d(m)`
and in no frame of depth `1 ≤ e < d`. -/
def IsFree (a : ℕ → ℤ) (d : ℕ) (m : ℤ) (z : ℤ) : Prop :=
  frameLo a d m < z ∧ z < frameHi a d m ∧ ∀ e, 1 ≤ e → e < d → ¬ InFrame a e z

/-- `scf:frames`(c), (d): `r_d(m) = a_d + (4m+1)4^d + 2`, the left endpoint plus one. -/
def rfree (a : ℕ → ℤ) (d : ℕ) (m : ℤ) : ℤ := frameLo a d m + 1

/-- **`scf:frames`(d)**, first congruence: `r_d(m) ≡ a_d + 4^d + 2 (mod 4^{d+1})`. -/
theorem rfree_emod (a : ℕ → ℤ) (d : ℕ) (m : ℤ) :
    rfree a d m % 4 ^ (d + 1) = (a d + 4 ^ d + 2) % 4 ^ (d + 1) := by
  have e : rfree a d m = a d + 4 ^ d + 2 + 4 ^ (d + 1) * m := by
    simp only [rfree, frameLo, pow_succ]; ring
  rw [e, Int.add_mul_emod_self_left]

/-- **`scf:frames`(d)**, second congruence: for `D > d`, `r_D(m') ≡ a_d + 2 (mod 4^{d+1})`. -/
theorem rfree_emod_of_lt {a : ℕ → ℤ} (ha : FrameOffsets a) {d D : ℕ} (h : d < D) (m' : ℤ) :
    rfree a D m' % 4 ^ (d + 1) = (a d + 2) % 4 ^ (d + 1) := by
  have hdvd : (4 : ℤ) ^ (d + 1) ∣ a D - a d := by
    rw [Int.dvd_iff_emod_eq_zero, Int.sub_emod, ha.emod h.le, Int.sub_self, Int.zero_emod]
  have hdvd' : (4 : ℤ) ^ (d + 1) ∣ (4 * m' + 1) * 4 ^ D :=
    Dvd.dvd.mul_left (pow_dvd_pow 4 h) _
  rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
  apply Int.emod_eq_zero_of_dvd
  have e : rfree a D m' - (a d + 2) = (a D - a d) + (4 * m' + 1) * 4 ^ D := by
    simp only [rfree, frameLo]; ring
  rw [e]; exact dvd_add hdvd hdvd'

theorem rfree_ne_of_lt {a : ℕ → ℤ} (ha : FrameOffsets a) {d D : ℕ} (hlt : d < D) (m m' : ℤ) :
    rfree a d m ≠ rfree a D m' := by
  intro h
  have h1 := rfree_emod a d m
  rw [h, rfree_emod_of_lt ha hlt m'] at h1
  have h2 := Int.emod_eq_emod_iff_emod_sub_eq_zero.1 h1.symm
  rw [show a d + 4 ^ d + 2 - (a d + 2) = 4 ^ d by ring] at h2
  have h3 := Int.le_of_dvd (by positivity) (Int.dvd_of_emod_eq_zero h2)
  have h4 : (4 : ℤ) ^ d < 4 ^ (d + 1) := pow_lt_pow_right₀ (by norm_num) (Nat.lt_succ_self d)
  linarith

/-- **`scf:frames`(d)**, last claim: no integer is of the form `r_d(m)` for two different
depths. -/
theorem rfree_depth_unique {a : ℕ → ℤ} (ha : FrameOffsets a) {d D : ℕ} {m m' : ℤ}
    (h : rfree a d m = rfree a D m') : d = D := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact rfree_ne_of_lt ha hlt m m' h
  · exact rfree_ne_of_lt ha hlt m' m h.symm

/-- **`scf:frames`(c)**, the least free coordinate: `r_d(m)`, the left endpoint plus one, is free
(`d ≥ 1`); it is the least element of `𝓕_d(m)` since every free coordinate exceeds the left
endpoint. -/
theorem isFree_rfree {a : ℕ → ℤ} (ha : FrameOffsets a) {d : ℕ} (hd : 1 ≤ d) (m : ℤ) :
    IsFree a d m (rfree a d m) := by
  have hp : (4 : ℤ) ≤ 4 ^ d := le_self_pow₀ (by norm_num) (by omega)
  refine ⟨by simp [rfree], ?_, fun e he hed => ?_⟩
  · simp only [rfree, frameLo, frameHi]; nlinarith
  · have hM : (0 : ℤ) < 4 ^ (e + 1) := by positivity
    have hpe : (4 : ℤ) ≤ 4 ^ e := le_self_pow₀ (by norm_num) (by omega)
    have r : (rfree a d m - a e) % 4 ^ (e + 1) = 2 := by
      rw [Int.sub_emod, rfree_emod_of_lt ha hed m, ← Int.sub_emod,
        show a e + 2 - a e = 2 by ring]
      exact Int.emod_eq_of_lt (by norm_num) (by rw [pow_succ]; linarith)
    rw [inFrame_iff, r]
    omega

/-- **`scf:frames`(c)**, the largest free coordinate: the right endpoint minus one is free
(`d ≥ 1`). -/
theorem isFree_frameHi_sub_one {a : ℕ → ℤ} (ha : FrameOffsets a) {d : ℕ} (hd : 1 ≤ d) (m : ℤ) :
    IsFree a d m (frameHi a d m - 1) := by
  have hp : (4 : ℤ) ≤ 4 ^ d := le_self_pow₀ (by norm_num) (by omega)
  refine ⟨?_, by linarith, fun e he hed => ?_⟩
  · simp only [frameLo, frameHi]; nlinarith
  · have hM : (0 : ℤ) < 4 ^ (e + 1) := by positivity
    have hpe : (4 : ℤ) ^ (e + 1) = 4 * 4 ^ e := by ring
    have hpe1 : (1 : ℤ) ≤ 4 ^ e := one_le_pow₀ (by norm_num)
    have hdvd : (4 : ℤ) ^ (e + 1) ∣ a d - a e := by
      rw [Int.dvd_iff_emod_eq_zero, Int.sub_emod, ha.emod hed.le, Int.sub_self, Int.zero_emod]
    have hdvd' : (4 : ℤ) ^ (e + 1) ∣ (4 * m + 3) * 4 ^ d :=
      Dvd.dvd.mul_left (pow_dvd_pow 4 hed) _
    have r : (frameHi a d m - 1 - a e) % 4 ^ (e + 1) = 4 ^ (e + 1) - 1 := by
      refine emod_of_dvd_sub ?_ (by linarith) (by linarith)
      have e' : frameHi a d m - 1 - a e - (4 ^ (e + 1) - 1) =
          (a d - a e) + (4 * m + 3) * 4 ^ d - 4 ^ (e + 1) := by
        simp only [frameHi]; ring
      rw [e']
      exact dvd_sub (dvd_add hdvd hdvd') dvd_rfl
    have hpe4 : (4 : ℤ) ≤ 4 ^ e := le_self_pow₀ (by norm_num) (by omega)
    rw [inFrame_iff, r, hpe]
    omega

/-- **`scf:frames`(e)**: if the base-4 digit of `z - τ_i` at position `d ≥ 1` is `2`, that is
`(z - a_d) mod 4^{d+1} ∈ [2·4^d, 3·4^d - 1]`, then `z` lies in the interior of a frame of depth
`d`. -/
theorem interior_of_digit_two (a : ℕ → ℤ) {d : ℕ} (hd : 1 ≤ d) {z : ℤ}
    (h1 : 2 * 4 ^ d ≤ (z - a d) % 4 ^ (d + 1)) (h2 : (z - a d) % 4 ^ (d + 1) < 3 * 4 ^ d) :
    ∃ m, frameLo a d m < z ∧ z < frameHi a d m := by
  have hp : (4 : ℤ) ≤ 4 ^ d := le_self_pow₀ (by norm_num) (by omega)
  have hdiv := Int.mul_ediv_add_emod (z - a d) (4 ^ (d + 1))
  refine ⟨(z - a d) / 4 ^ (d + 1), ?_, ?_⟩ <;> simp only [frameLo, frameHi] <;>
    rw [pow_succ] at hdiv h1 h2 ⊢ <;>
    generalize (z - a d) / (4 ^ d * 4) = q at hdiv ⊢ <;>
    generalize (z - a d) % (4 ^ d * 4) = ρ at hdiv h1 h2 <;>
    nlinarith

/-! ## `scf:frames`(c): the count `|𝓕_d(m)| = 2^{d+2} - 2` (App. A) -/

/-- App. A, proof of `scf:frames`(c): a residue `s` is *allowed* (for depth `d`) if
`s mod 4^{e+1} ∉ [4^e + 1, 3·4^e]` for every `1 ≤ e < d`. -/
def Allowed (d s : ℕ) : Prop :=
  ∀ e, 1 ≤ e → e < d → ¬ (4 ^ e + 1 ≤ s % 4 ^ (e + 1) ∧ s % 4 ^ (e + 1) ≤ 3 * 4 ^ e)

/-- App. A: the residues `0` and `1` are allowed. -/
theorem allowed_of_le_one {d s : ℕ} (hs : s ≤ 1) : Allowed d s := by
  intro e _ _ h
  have h1 : s % 4 ^ (e + 1) ≤ s := Nat.mod_le _ _
  have h2 : 1 ≤ 4 ^ e := Nat.one_le_pow _ _ (by norm_num)
  omega

/-- App. A, proof of `scf:frames`(c): for `s = t·4^d + s'` (`t < 4`, `s' < 4^d`), the conditions
for `e < d` concern `s'`, and the condition for `e = d` is `s ∉ [4^d + 1, 3·4^d]`. -/
theorem allowed_block {d : ℕ} (hd : 1 ≤ d) {t s : ℕ} (ht : t < 4) (hs : s < 4 ^ d) :
    Allowed (d + 1) (t * 4 ^ d + s) ↔
      Allowed d s ∧ ¬ (4 ^ d + 1 ≤ t * 4 ^ d + s ∧ t * 4 ^ d + s ≤ 3 * 4 ^ d) := by
  have hlow : ∀ e, e < d → (t * 4 ^ d + s) % 4 ^ (e + 1) = s % 4 ^ (e + 1) := by
    intro e he
    obtain ⟨k, hk⟩ : 4 ^ (e + 1) ∣ t * 4 ^ d := Dvd.dvd.mul_left (pow_dvd_pow 4 he) t
    rw [hk, Nat.mul_add_mod]
  have htop : (t * 4 ^ d + s) % 4 ^ (d + 1) = t * 4 ^ d + s := by
    apply Nat.mod_eq_of_lt
    rw [pow_succ]; nlinarith
  constructor
  · intro h
    refine ⟨fun e he hed => ?_, ?_⟩
    · rw [← hlow e hed]; exact h e he (by omega)
    · have := h d hd (by omega); rwa [htop] at this
  · rintro ⟨h1, h2⟩ e he hed
    rcases Nat.lt_succ_iff_lt_or_eq.1 hed with hlt | rfl
    · rw [hlow e hlt]; exact h1 e he hlt
    · rw [htop]; exact h2


/-- The indicator `[P]` as a natural number. -/
def ind (P : Prop) [Decidable P] : ℕ := if P then 1 else 0

open Classical in
/-- App. A, proof of `scf:frames`(c): `g_d = 2^{d+1}` allowed residues in `[0, 4^d)` (`g_1 = 4`,
`g_{d+1} = 2 g_d`). -/
theorem sum_allowed {d : ℕ} (hd : 1 ≤ d) :
    ∑ s ∈ Finset.range (4 ^ d), ind (Allowed d s) = 2 ^ (d + 1) := by
  induction d, hd using Nat.le_induction with
  | base =>
    have : ∀ s, ind (Allowed 1 s) = 1 := fun s => by
      simp only [ind, if_pos (show Allowed 1 s from fun e he hed => by omega)]
    simp [this]
  | succ d hd ih =>
    set N := 4 ^ d with hN
    have hN1 : 1 ≤ N := Nat.one_le_pow _ _ (by norm_num)
    have e4 : 4 ^ (d + 1) = N + N + N + N := by rw [pow_succ]; ring
    rw [e4, Finset.sum_range_add, Finset.sum_range_add, Finset.sum_range_add]
    have b0 : ∀ s ∈ Finset.range N, ind (Allowed (d + 1) s) = ind (Allowed d s) := by
      intro s hs
      have hs' := Finset.mem_range.1 hs
      have h := allowed_block hd (t := 0) (by norm_num) hs'
      simp only [zero_mul, zero_add] at h
      have hn : ¬ (4 ^ d + 1 ≤ s ∧ s ≤ 3 * 4 ^ d) := by omega
      simp only [ind, h, hn, not_false_eq_true, and_true]
    have b1 : ∀ s ∈ Finset.range N, ind (Allowed (d + 1) (N + s)) = ind (s = 0) := by
      intro s hs
      have hs' := Finset.mem_range.1 hs
      have h := allowed_block hd (t := 1) (by norm_num) hs'
      rw [one_mul, ← hN] at h
      simp only [ind, h]
      by_cases h0 : s = 0
      · subst h0; simp [allowed_of_le_one (d := d) (zero_le_one)]
      · simp only [h0, if_false]; rw [if_neg]; omega
    have b2 : ∀ s ∈ Finset.range N, ind (Allowed (d + 1) (N + N + s)) = 0 := by
      intro s hs
      have hs' := Finset.mem_range.1 hs
      have h := allowed_block hd (t := 2) (by norm_num) hs'
      rw [show 2 * 4 ^ d = N + N by rw [← hN]; ring] at h
      simp only [ind, h]; rw [if_neg]; omega
    have b3 : ∀ s ∈ Finset.range N,
        ind (Allowed (d + 1) (N + N + N + s)) = ind (Allowed d s ∧ s ≠ 0) := by
      intro s hs
      have hs' := Finset.mem_range.1 hs
      have h := allowed_block hd (t := 3) (by norm_num) hs'
      rw [show 3 * 4 ^ d = N + N + N by rw [← hN]; ring] at h
      simp only [ind, h]
      by_cases ha : Allowed d s <;> by_cases h0 : s = 0 <;> simp [ha, h0] <;> omega
    rw [Finset.sum_congr rfl b0, Finset.sum_congr rfl b1, Finset.sum_congr rfl b2,
      Finset.sum_congr rfl b3]
    have hsplit : ∀ s ∈ Finset.range N,
        ind (Allowed d s) = ind (Allowed d s ∧ s ≠ 0) + ind (s = 0) := by
      intro s _
      by_cases h0 : s = 0
      · subst h0; simp [ind, allowed_of_le_one (d := d) (zero_le_one)]
      · simp [ind, h0]
    rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib] at ih
    have h1 : ∑ s ∈ Finset.range N, ind (s = 0) = 1 := by
      simp [ind, Finset.sum_ite_eq', Finset.mem_range]; omega
    rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, h1, Finset.sum_const_zero]
    rw [h1] at ih
    rw [pow_succ 2 (d + 1)]
    omega

/-- App. A, proof of `scf:frames`(c): `z = r_d(m) + n` (with `n + 2 < 2·4^d`, so that `z` lies in
the interior of `I_d(m)`) is free iff the residue `(z - a_d) mod 4^d = (n + 2) mod 4^d` is
allowed. -/
theorem isFree_iff_allowed {a : ℕ → ℤ} (ha : FrameOffsets a) {d : ℕ} (m : ℤ) {n : ℕ}
    (hn : n + 2 < 2 * 4 ^ d) :
    IsFree a d m (rfree a d m + n) ↔ Allowed d ((n + 2) % 4 ^ d) := by
  have hlo : frameLo a d m < rfree a d m + n := by simp only [rfree]; omega
  have hhi : rfree a d m + n < frameHi a d m := by
    have hn' : ((n : ℤ) + 2) < 2 * 4 ^ d := by exact_mod_cast hn
    simp only [rfree, frameLo, frameHi]; nlinarith
  have key : ∀ e, 1 ≤ e → e < d → (InFrame a e (rfree a d m + n) ↔
      4 ^ e + 1 ≤ (n + 2) % 4 ^ d % 4 ^ (e + 1) ∧ (n + 2) % 4 ^ d % 4 ^ (e + 1) ≤ 3 * 4 ^ e) := by
    intro e _ hed
    rw [inFrame_iff, Nat.mod_mod_of_dvd _ (pow_dvd_pow 4 hed)]
    have hdvd : (4 : ℤ) ^ (e + 1) ∣ (a d - a e) + (4 * m + 1) * 4 ^ d := by
      refine dvd_add ?_ (Dvd.dvd.mul_left (pow_dvd_pow 4 hed) _)
      rw [Int.dvd_iff_emod_eq_zero, Int.sub_emod, ha.emod hed.le, Int.sub_self, Int.zero_emod]
    obtain ⟨k, hk⟩ := hdvd
    have e1 : rfree a d m + n - a e = ((n + 2 : ℕ) : ℤ) + 4 ^ (e + 1) * k := by
      rw [← hk]; simp only [rfree, frameLo]; push_cast; ring
    have hr : (rfree a d m + n - a e) % 4 ^ (e + 1) = (((n + 2) % 4 ^ (e + 1) : ℕ) : ℤ) := by
      rw [e1, Int.add_mul_emod_self_left]; push_cast; rfl
    rw [hr]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> (try exact_mod_cast h1) <;>
      exact_mod_cast h2
  simp only [IsFree, Allowed, hlo, hhi, true_and]
  exact forall_congr' fun e => imp_congr_right fun he => imp_congr_right fun hed =>
    not_congr (key e he hed)

open Classical in
/-- **`scf:frames`(c)**, the count: `|𝓕_d(m)| = N_d = 2^{d+2} - 2` (`d ≥ 1`). As printed in App. A:
writing `z = a_d + 4m·4^d + t·4^d + s'`, `z ∈ \mathring I_d(m)` exactly when `t = 1` and `s' ≥ 2`
or `t = 2`; the residues `0` and `1` are allowed, so the count is `(g_d - 2) + g_d`. -/
theorem card_free {a : ℕ → ℤ} (ha : FrameOffsets a) {d : ℕ} (hd : 1 ≤ d) (m : ℤ) :
    Set.ncard {z | IsFree a d m z} = 2 ^ (d + 2) - 2 := by
  set N := 4 ^ d with hN
  have hN4 : 4 ≤ N := by rw [hN]; exact le_self_pow₀ (by norm_num) (by omega)
  let S : Finset ℕ := (Finset.range (2 * N - 2)).filter (fun n => Allowed d ((n + 2) % N))
  have hset : {z | IsFree a d m z} = ↑(S.image (fun n : ℕ => rfree a d m + n)) := by
    ext z
    simp only [Set.mem_setOf_eq, Finset.coe_image, Finset.coe_filter, Set.mem_image,
      Finset.mem_range, S]
    constructor
    · intro hz
      have h1 := hz.1; have h2 := hz.2.1
      have hge : 0 ≤ z - rfree a d m := by simp only [rfree]; omega
      have hz' : rfree a d m + ((z - rfree a d m).toNat : ℤ) = z := by
        rw [Int.toNat_of_nonneg hge]; ring
      have hlt : (z - rfree a d m).toNat + 2 < 2 * N := by
        have : z - rfree a d m + 2 < 2 * (N : ℤ) := by
          rw [hN]; push_cast
          simp only [rfree, frameLo, frameHi] at h2 ⊢; nlinarith
        omega
      refine ⟨(z - rfree a d m).toNat, ⟨by omega, ?_⟩, hz'⟩
      rw [← isFree_iff_allowed ha m hlt, hz']; exact hz
    · rintro ⟨n, ⟨hn, hA⟩, rfl⟩
      exact (isFree_iff_allowed ha m (by omega)).2 hA
  rw [hset, Set.ncard_coe_finset, Finset.card_image_of_injective _ (fun x y h => by simpa using h),
    Finset.card_filter]
  change ∑ n ∈ Finset.range (2 * N - 2), ind (Allowed d ((n + 2) % N)) = _
  have hall := sum_allowed hd
  rw [← hN, show N = 2 + (N - 2) by omega, Finset.sum_range_add] at hall
  have h01 : ∑ n ∈ Finset.range 2, ind (Allowed d n) = 2 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
    simp only [ind, if_pos (allowed_of_le_one (d := d) (zero_le_one)),
      if_pos (allowed_of_le_one (d := d) (le_refl 1))]
  rw [h01] at hall
  rw [show 2 * N - 2 = (N - 2) + N by omega, Finset.sum_range_add]
  have hA : ∀ n ∈ Finset.range (N - 2), ind (Allowed d ((n + 2) % N)) = ind (Allowed d (2 + n)) := by
    intro n hn
    rw [Nat.mod_eq_of_lt (by simp at hn; omega), add_comm]
  have hB : ∀ n ∈ Finset.range N, ind (Allowed d ((N - 2 + n + 2) % N)) = ind (Allowed d n) := by
    intro n hn
    rw [show N - 2 + n + 2 = n + N by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by simpa using hn)]
  rw [Finset.sum_congr rfl hA, Finset.sum_congr rfl hB, sum_allowed hd]
  rw [show 2 ^ (d + 2) = 2 * 2 ^ (d + 1) by ring]
  omega

end UPD.Scaffold

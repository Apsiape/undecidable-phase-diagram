/-
# Section 5.2: the computation on a grid (`bg:grid`)

New in this project.

* Binary arithmetic (the counter and the adder of (C1), (C3)): `carry a b c j` is the carry into
  position `j` when `a`, `b` and a carry-in `c ≤ 1` are added; `carry_succ` (the carry chain
  `c_{j+1} = maj(a_j, b_j, c_j)`) and `testBit_add` (the sum digit `a_j ⊕ b_j ⊕ c_j`). The counter
  adds `0` with carry-in `1`, the adder adds `3 = [j ≤ 1]` with carry-in `0`.
* `kc s`: the cell record of a site value (an arbitrary record when it is `∘`); `cellAt` is
  `𝔨(i, j)`, the cell record at `ξ(i, j)`. `rules`: at `ξ(i, j)` the record exists and satisfies
  (C0)–(C9).
* Channels (`chanH`, `chanV`, and `chanH_some`, `chanV_some` with (C0)): by `bg:grids`(a) and
  (K1), (K2), the east colour of `ξ(i, j)` is the west colour of `ξ(i + 1, j)` and the north colour
  of `ξ(i, j)` is the south colour of `ξ(i, j + 1)`.
* **`bg:grid`**: (a) `grid_a` (`ct(i, j)` is the binary digit of `i` at position `j`,
  `rc(i, j) = min(j, 80)`); (b) `grid_b` (`hot(i, j) = [j = d + 2]`); (c) `grid_c`
  (`t_C(i, j) = c_i(j)`); (d) `grid_d` (`rdy(i, j) = ρ_d`, `g^±(i, j) = ρ_d 𝗆^±(c_{N-1}(j))`).
  Also the carries (`grid_cy`, `grid_ay`), the adder sum (`grid_sm`) and the neighbours of the
  tableau (`grid_tS`, `grid_tN`).
-/
import UndecidablePhaseDiagram.Background.Grids
import Mathlib.Data.Nat.Bitwise

set_option autoImplicit false

namespace UPD.BG

open UPD.Scaffold

/-! ## Binary arithmetic -/

/-- The carry into position `j` when `a`, `b` and a carry-in `c` are added. -/
def carry (a b c j : ℕ) : Bool := decide (2 ^ j ≤ a % 2 ^ j + b % 2 ^ j + c)

theorem carry_zero (a b c : ℕ) : carry a b c 0 = decide (1 ≤ c) := by
  simp [carry, Nat.mod_one]

theorem split_two_pow (a j : ℕ) : ∃ x A, A < 2 ^ j ∧ a = A + 2 ^ j * x :=
  ⟨a / 2 ^ j, a % 2 ^ j, Nat.mod_lt _ (Nat.two_pow_pos j), (Nat.mod_add_div a _).symm⟩

theorem mod_split {P x A : ℕ} (hA : A < P) : (A + P * x) % P = A := by
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hA]

theorem div_split {P x A : ℕ} (hP : 0 < P) (hA : A < P) : (A + P * x) / P = x := by
  rw [Nat.add_mul_div_left _ _ hP, Nat.div_eq_of_lt hA, zero_add]

/-- The carry chain of a ripple-carry adder: `c_{j+1} = maj(a_j, b_j, c_j)`. -/
theorem carry_succ (a b c j : ℕ) (hc : c ≤ 1) :
    carry a b c (j + 1) = SiteVal.maj (a.testBit j) (b.testBit j) (carry a b c j) := by
  have hP := Nat.two_pow_pos j
  obtain ⟨x, A, hA, rfl⟩ := split_two_pow a j
  obtain ⟨y, B, hB, rfl⟩ := split_two_pow b j
  simp only [carry, Nat.testBit_eq_decide_div_mod_eq, SiteVal.maj, Nat.mod_pow_succ]
  rw [mod_split hA, mod_split hB, div_split hP hA, div_split hP hB, pow_succ]
  have hx := Nat.mod_lt x (by norm_num : 0 < 2)
  have hy := Nat.mod_lt y (by norm_num : 0 < 2)
  generalize 2 ^ j = P at *
  generalize x % 2 = u at *
  generalize y % 2 = v at *
  rw [Bool.eq_iff_iff]
  interval_cases u <;> interval_cases v <;> simp <;> omega

/-- The sum digit of a ripple-carry adder: `(a + b + c)_j = a_j ⊕ b_j ⊕ c_j`. -/
theorem testBit_add (a b c j : ℕ) (hc : c ≤ 1) :
    (a + b + c).testBit j = xor (xor (a.testBit j) (b.testBit j)) (carry a b c j) := by
  have hP := Nat.two_pow_pos j
  obtain ⟨x, A, hA, rfl⟩ := split_two_pow a j
  obtain ⟨y, B, hB, rfl⟩ := split_two_pow b j
  simp only [carry, Nat.testBit_eq_decide_div_mod_eq]
  rw [mod_split hA, mod_split hB, div_split hP hA, div_split hP hB,
    show A + 2 ^ j * x + (B + 2 ^ j * y) + c = (A + B + c) + 2 ^ j * (x + y) by ring,
    Nat.add_mul_div_left _ _ hP]
  have hq : (A + B + c) / 2 ^ j = if 2 ^ j ≤ A + B + c then 1 else 0 := by
    split_ifs with h
    · exact Nat.div_eq_of_lt_le (by omega) (by omega)
    · exact Nat.div_eq_of_lt (by omega)
  rw [hq]
  by_cases hp : 2 ^ j ≤ A + B + c <;> simp [hp] <;>
    rcases Nat.mod_two_eq_zero_or_one x with h1 | h1 <;>
    rcases Nat.mod_two_eq_zero_or_one y with h2 | h2 <;> simp [h1, h2] <;> omega

/-- The binary digits of `3`: `[j ≤ 1]`. -/
theorem testBit_three (j : ℕ) : Nat.testBit 3 j = decide (j ≤ 1) := by
  rcases j with _ | _ | j
  · decide
  · decide
  · rw [Nat.testBit_eq_false_of_lt]
    · simp
    · have : 4 ≤ 2 ^ (j + 1 + 1) :=
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (j + 1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega

/-- Descending induction on `[0, N)`. -/
theorem desc_ind {N : ℕ} {P : ℕ → Prop} (hlast : P (N - 1)) (hstep : ∀ i, i + 1 < N → P (i + 1) → P i)
    {i : ℕ} (hi : i < N) : P i := by
  have key : ∀ t, t < N → P (N - 1 - t) := by
    intro t
    induction t with
    | zero => intro _; simpa using hlast
    | succ t ih =>
      intro ht
      have := hstep (N - 1 - (t + 1)) (by omega) (by rw [show N - 1 - (t + 1) + 1 = N - 1 - t by omega]; exact ih (by omega))
      exact this
  have := key (N - 1 - i) (by omega)
  rwa [show N - 1 - (N - 1 - i) = i by omega] at this

/-! ## Cell records at the sites of a grid -/

variable {U : Machine}

theorem lastCol {d : ℕ} : MachineM.Nd d - 1 < MachineM.Nd d := by
  have := MachineM.two_le_Nd d; omega

instance (d : ℕ) : Decidable (MachineM.ready U d) := by
  unfold MachineM.ready; infer_instance

instance : Inhabited (CellRec U) :=
  ⟨⟨false, false, false, false, false, false, false, false, false, 0, none, none,
    initM U false false, fun _ => false, fun _ => false⟩⟩

/-- The cell record `𝔨` of a site value (the default record when `𝔨 = ∘`). -/
def kc (s : SiteVal U) : CellRec U := s.k.getD default

/-- `𝔨(i, j)`, the cell record at `ξ(i, j)` of `G_d(m₁, m₂)`. -/
noncomputable def cellAt (ω : Config (SiteVal U)) (τ : ℕ → Bool × Bool) (d : ℕ) (m1 m2 : ℤ)
    (i j : ℕ) : CellRec U :=
  kc (ω (gsite τ d m1 m2 i j))

namespace Setting

variable {ω : Config (SiteVal U)} {τ : ℕ → Bool × Bool} (hs : Setting ω τ)
variable {d : ℕ} (hd : 1 ≤ d) (m1 m2 : ℤ)
include hs hd

/-- At `ξ(i, j)` the cell record is `𝔨(i, j)` and satisfies (C0)–(C9) (by (K3), the site being
active). -/
theorem rules {i j : ℕ} (hi : i < MachineM.Nd d) (hj : j < MachineM.Nd d) :
    (ω (gsite τ d m1 m2 i j)).k = some (cellAt ω τ d m1 m2 i j) ∧
    (ω (gsite τ d m1 m2 i j)).C0 ∧ (ω (gsite τ d m1 m2 i j)).C1 (cellAt ω τ d m1 m2 i j) ∧
    (ω (gsite τ d m1 m2 i j)).C2 (cellAt ω τ d m1 m2 i j) ∧
    (ω (gsite τ d m1 m2 i j)).C3 (cellAt ω τ d m1 m2 i j) ∧
    (ω (gsite τ d m1 m2 i j)).C4 (cellAt ω τ d m1 m2 i j) ∧
    (ω (gsite τ d m1 m2 i j)).C5 (cellAt ω τ d m1 m2 i j) ∧
    (ω (gsite τ d m1 m2 i j)).C6 (cellAt ω τ d m1 m2 i j) ∧
    (ω (gsite τ d m1 m2 i j)).C7 (cellAt ω τ d m1 m2 i j) ∧
    (ω (gsite τ d m1 m2 i j)).C8 (cellAt ω τ d m1 m2 i j) ∧
    (ω (gsite τ d m1 m2 i j)).C9 (cellAt ω τ d m1 m2 i j) := by
  have hact := hs.active_of_free (ξ := gsite τ d m1 m2 i j) hd
    (zeta_free (frameOffsets_phase _) hd m1 hi) (zeta_free (frameOffsets_phase _) hd m2 hj)
  obtain ⟨k, hk, h⟩ := (hs.K3 _).2 hact
  have e : cellAt ω τ d m1 m2 i j = k := by simp only [cellAt, kc, hk, Option.getD_some]
  rw [e]
  exact ⟨hk, h⟩

/-- Channels (rows): the east colour of `ξ(i, j)` is the west colour of `ξ(i + 1, j)`. -/
theorem chanH {i j : ℕ} (hi : i + 1 < MachineM.Nd d) (hj : j < MachineM.Nd d) :
    (ω (gsite τ d m1 m2 i j)).lE = (ω (gsite τ d m1 m2 (i + 1) j)).lW := by
  have ha1 : FrameOffsets (a1 τ) := frameOffsets_phase _
  simp only [gsite]
  exact chain (f := fun z => (ω (z, zeta (a2 τ) d m2 j)).lE)
    (g := fun z => (ω (z, zeta (a2 τ) d m2 j)).lW) (fun z => hs.lE_eq z _)
    ((zeta_lt_iff ha1 hd m1 (by omega) hi).2 (by omega))
    (fun z h1 h2 => (hs.K1 _).2 (hs.grids_a_h hd m1 m2 hi hj h1 h2))

/-- Channels (columns): the north colour of `ξ(i, j)` is the south colour of `ξ(i, j + 1)`. -/
theorem chanV {i j : ℕ} (hi : i < MachineM.Nd d) (hj : j + 1 < MachineM.Nd d) :
    (ω (gsite τ d m1 m2 i j)).lN = (ω (gsite τ d m1 m2 i (j + 1))).lS := by
  have ha2 : FrameOffsets (a2 τ) := frameOffsets_phase _
  simp only [gsite]
  exact chain (f := fun z => (ω (zeta (a1 τ) d m1 i, z)).lN)
    (g := fun z => (ω (zeta (a1 τ) d m1 i, z)).lS) (fun z => hs.lN_eq _ z)
    ((zeta_lt_iff ha2 hd m2 (by omega) hj).2 (by omega))
    (fun z h1 h2 => (hs.K2 _).2 (hs.grids_a_v hd m1 m2 hi hj h1 h2))

/-- The colour on a row channel is not `∘` ((C0), `f_E = 0` west of the last column). -/
theorem chanH_some {i j : ℕ} (hi : i + 1 < MachineM.Nd d) (hj : j < MachineM.Nd d) :
    ∃ l, (ω (gsite τ d m1 m2 i j)).lE = some l ∧ (ω (gsite τ d m1 m2 (i + 1) j)).lW = some l := by
  obtain ⟨-, c0, -⟩ := hs.rules hd m1 m2 (show i < MachineM.Nd d by omega) hj
  obtain ⟨-, fE, -, -⟩ := hs.grids_c hd m1 m2 (show i < MachineM.Nd d by omega) hj
  have hne : (ω (gsite τ d m1 m2 i j)).lE ≠ none := by
    intro h; have := c0.2.1.1 h; rw [fE] at this; simp at this; omega
  obtain ⟨l, hl⟩ := Option.ne_none_iff_exists'.1 hne
  exact ⟨l, hl, by rw [← hs.chanH hd m1 m2 hi hj]; exact hl⟩

/-- The colour on a column channel is not `∘` ((C0), `f_N = 0` below the last row). -/
theorem chanV_some {i j : ℕ} (hi : i < MachineM.Nd d) (hj : j + 1 < MachineM.Nd d) :
    ∃ l, (ω (gsite τ d m1 m2 i j)).lN = some l ∧ (ω (gsite τ d m1 m2 i (j + 1))).lS = some l := by
  obtain ⟨-, c0, -⟩ := hs.rules hd m1 m2 hi (show j < MachineM.Nd d by omega)
  obtain ⟨-, -, -, fN⟩ := hs.grids_c hd m1 m2 hi (show j < MachineM.Nd d by omega)
  have hne : (ω (gsite τ d m1 m2 i j)).lN ≠ none := by
    intro h; have := c0.2.2.2.1 h; rw [fN] at this; simp at this; omega
  obtain ⟨l, hl⟩ := Option.ne_none_iff_exists'.1 hne
  exact ⟨l, hl, by rw [← hs.chanV hd m1 m2 hi hj]; exact hl⟩

/-! ## `bg:grid`(a): the counter and the row counter -/

/-- **`bg:grid`(a)**, second claim: `rc(i, j) = min(j, 80)` (C2). -/
theorem grid_rc {i j : ℕ} (hi : i < MachineM.Nd d) (hj : j < MachineM.Nd d) :
    (cellAt ω τ d m1 m2 i j).rc.val = min j 80 := by
  induction j with
  | zero =>
    obtain ⟨-, -, -, c2, -⟩ := hs.rules hd m1 m2 hi hj
    obtain ⟨-, -, fS, -⟩ := hs.grids_c hd m1 m2 hi hj
    rw [c2.1 (by rw [fS]; rfl)]; rfl
  | succ j ih =>
    obtain ⟨l, hl1, hl2⟩ := hs.chanV_some hd m1 m2 hi hj
    obtain ⟨-, -, -, c2, -⟩ := hs.rules hd m1 m2 hi hj
    obtain ⟨-, -, -, c2', -⟩ := hs.rules hd m1 m2 hi (show j < MachineM.Nd d by omega)
    obtain ⟨-, -, fS, -⟩ := hs.grids_c hd m1 m2 hi hj
    have e1 := c2.2.1 (by rw [fS]; simp) l hl2
    have e2 := c2'.2.2 l hl1
    rw [e1, e2, ih (by omega)]
    omega

/-- The counter column `i + 1` carries the carries of `i + 1 = i + 0 + 1` (C1). -/
theorem grid_ct_cy {i : ℕ} (hi : i < MachineM.Nd d) :
    ∀ j, j < MachineM.Nd d → (cellAt ω τ d m1 m2 i j).ct = Nat.testBit i j ∧
      (cellAt ω τ d m1 m2 i j).cy = (if i = 0 then false else carry (i - 1) 0 1 j) := by
  induction i with
  | zero =>
    intro j hj
    obtain ⟨-, -, c1, -⟩ := hs.rules hd m1 m2 hi hj
    obtain ⟨fW, -, -, -⟩ := hs.grids_c hd m1 m2 hi hj
    obtain ⟨-, hct, hcy⟩ := c1.1 (by rw [fW]; rfl)
    simp [hct, hcy]
  | succ i ih =>
    have hi' : i < MachineM.Nd d := by omega
    have ih' := ih hi'
    have hctIn : ∀ j, j < MachineM.Nd d →
        (cellAt ω τ d m1 m2 (i + 1) j).ctIn = Nat.testBit i j := by
      intro j hj
      obtain ⟨l, hl1, hl2⟩ := hs.chanH_some hd m1 m2 hi hj
      obtain ⟨-, -, c1, -⟩ := hs.rules hd m1 m2 hi hj
      obtain ⟨-, -, c1', -⟩ := hs.rules hd m1 m2 hi' hj
      obtain ⟨fW, -, -, -⟩ := hs.grids_c hd m1 m2 hi hj
      rw [(c1.2.1 (by rw [fW]; simp)).1 l hl2, c1'.2.2.1 l hl1, (ih' j hj).1]
    have hcyc : ∀ j, j < MachineM.Nd d → (cellAt ω τ d m1 m2 (i + 1) j).cy = carry i 0 1 j := by
      intro j hj
      induction j with
      | zero =>
        obtain ⟨-, -, c1, -⟩ := hs.rules hd m1 m2 hi hj
        obtain ⟨fW, -, fS, -⟩ := hs.grids_c hd m1 m2 hi hj
        rw [(c1.2.1 (by rw [fW]; simp)).2.1 (by rw [fS]; rfl), carry_zero]; rfl
      | succ j ihj =>
        have hj' : j < MachineM.Nd d := by omega
        obtain ⟨l, hl1, hl2⟩ := hs.chanV_some hd m1 m2 hi hj
        obtain ⟨-, -, c1, -⟩ := hs.rules hd m1 m2 hi hj
        obtain ⟨-, -, c1', -⟩ := hs.rules hd m1 m2 hi hj'
        obtain ⟨fW, -, fS, -⟩ := hs.grids_c hd m1 m2 hi hj
        have e1 := (c1.2.1 (by rw [fW]; simp)).2.2.1 (by rw [fS]; simp) l hl2
        have e2 := c1'.2.2.2 l hl1
        rw [e1, e2, carry_succ _ _ _ _ le_rfl, ihj hj', hctIn j hj', Nat.zero_testBit]
        simp [SiteVal.maj]
    intro j hj
    obtain ⟨-, -, c1, -⟩ := hs.rules hd m1 m2 hi hj
    obtain ⟨fW, -, -, -⟩ := hs.grids_c hd m1 m2 hi hj
    refine ⟨?_, by simp [hcyc j hj]⟩
    have hadd := testBit_add i 0 1 j le_rfl
    simp only [Nat.add_zero, Nat.zero_testBit, Bool.xor_false] at hadd
    rw [(c1.2.1 (by rw [fW]; simp)).2.2.2, hctIn j hj, hcyc j hj, hadd]

/-- **`bg:grid`(a)**: `ct(i, j)` is the binary digit of `i` at position `j`, and
`rc(i, j) = min(j, 80)`. -/
theorem grid_a {i j : ℕ} (hi : i < MachineM.Nd d) (hj : j < MachineM.Nd d) :
    (cellAt ω τ d m1 m2 i j).ct = Nat.testBit i j ∧ (cellAt ω τ d m1 m2 i j).rc.val = min j 80 :=
  ⟨(hs.grid_ct_cy hd m1 m2 hi j hj).1, hs.grid_rc hd m1 m2 hi hj⟩

/-- The carries of the counter: `cy(i, j)` is `0` in column `0` and the carry into position `j` of
`(i - 1) + 1` otherwise. -/
theorem grid_cy {i j : ℕ} (hi : i < MachineM.Nd d) (hj : j < MachineM.Nd d) :
    (cellAt ω τ d m1 m2 i j).cy = (if i = 0 then false else carry (i - 1) 0 1 j) :=
  (hs.grid_ct_cy hd m1 m2 hi j hj).2

/-! ## `bg:grid`(b): the adder and the one-hot marker -/

/-- The carries of the adder in the last column: `ay(N-1, j)` is the carry into position `j` of
`(N - 1) + 3` (C3). -/
theorem grid_ay {j : ℕ} (hj : j < MachineM.Nd d) :
    (cellAt ω τ d m1 m2 (MachineM.Nd d - 1) j).ay = carry (MachineM.Nd d - 1) 3 0 j := by
  have hi := lastCol (d := d)
  induction j with
  | zero =>
    obtain ⟨-, -, -, -, c3, -⟩ := hs.rules hd m1 m2 hi hj
    obtain ⟨-, fE, fS, -⟩ := hs.grids_c hd m1 m2 hi hj
    rw [(c3.2 (by rw [fE]; simp)).1 (by rw [fS]; rfl), carry_zero]; rfl
  | succ j ih =>
    have hj' : j < MachineM.Nd d := by omega
    obtain ⟨l, hl1, hl2⟩ := hs.chanV_some hd m1 m2 hi hj
    obtain ⟨-, -, -, -, c3, -⟩ := hs.rules hd m1 m2 hi hj
    obtain ⟨-, -, -, -, c3', -⟩ := hs.rules hd m1 m2 hi hj'
    obtain ⟨-, fE, fS, -⟩ := hs.grids_c hd m1 m2 hi hj
    obtain ⟨-, fE', -, -⟩ := hs.grids_c hd m1 m2 hi hj'
    have e1 := (c3.2 (by rw [fE]; simp)).2.1 (by rw [fS]; simp) l hl2
    have e2 := (c3'.2 (by rw [fE']; simp)).2.2.2 l hl1
    rw [e1, e2, ih hj', carry_succ _ _ _ _ (by norm_num), testBit_three,
      (hs.grid_a hd m1 m2 hi hj').1, (hs.grid_a hd m1 m2 hi hj').2]
    rw [show decide (min j 80 ≤ 1) = decide (j ≤ 1) from decide_eq_decide.2 (by omega)]

/-- The adder sum in the last column: `sm(N-1, j)` is the digit of `(N - 1) + 3 = 2^{d+2}` at
position `j`, that is `[j = d + 2]`. -/
theorem grid_sm {j : ℕ} (hj : j < MachineM.Nd d) :
    (cellAt ω τ d m1 m2 (MachineM.Nd d - 1) j).sm = decide (j = d + 2) := by
  have hi := lastCol (d := d)
  obtain ⟨-, -, -, -, c3, -⟩ := hs.rules hd m1 m2 hi hj
  obtain ⟨-, fE, -, -⟩ := hs.grids_c hd m1 m2 hi hj
  rw [(c3.2 (by rw [fE]; simp)).2.2.1, hs.grid_ay hd m1 m2 hj, (hs.grid_a hd m1 m2 hi hj).1,
    (hs.grid_a hd m1 m2 hi hj).2]
  have e : decide (min j 80 ≤ 1) = Nat.testBit 3 j := by
    rw [testBit_three]; exact decide_eq_decide.2 (by omega)
  rw [e, ← testBit_add _ _ _ _ (by norm_num)]
  have h2 : MachineM.Nd d - 1 + 3 + 0 = 2 ^ (d + 2) := by
    have := MachineM.two_le_Nd d; unfold MachineM.Nd at *; omega
  rw [h2, Nat.testBit_two_pow]
  exact decide_eq_decide.2 eq_comm

/-- **`bg:grid`(b)**: `hot(i, j) = [j = d + 2]` (C3, C4: computed in the last column, copied west
along each logical row). -/
theorem grid_b {i j : ℕ} (hi : i < MachineM.Nd d) (hj : j < MachineM.Nd d) :
    (cellAt ω τ d m1 m2 i j).hot = decide (j = d + 2) := by
  refine desc_ind (P := fun i => (cellAt ω τ d m1 m2 i j).hot = decide (j = d + 2)) ?_ ?_ hi
  · obtain ⟨-, -, -, -, -, c4, -⟩ := hs.rules hd m1 m2 lastCol hj
    obtain ⟨-, fE, -, -⟩ := hs.grids_c hd m1 m2 lastCol hj
    rw [c4.1 (by rw [fE]; simp), hs.grid_sm hd m1 m2 hj]
  · intro i hi1 ih
    obtain ⟨l, hl1, hl2⟩ := hs.chanH_some hd m1 m2 hi1 hj
    obtain ⟨-, -, -, -, -, c4, -⟩ := hs.rules hd m1 m2 (show i < MachineM.Nd d by omega) hj
    obtain ⟨-, -, -, -, -, c4', -⟩ := hs.rules hd m1 m2 hi1 hj
    obtain ⟨-, fE, -, -⟩ := hs.grids_c hd m1 m2 (show i < MachineM.Nd d by omega) hj
    rw [c4.2.1 (by rw [fE]; simp; omega) l hl1, c4'.2.2 l hl2, ih]

/-! ## `bg:grid`(c): the tableau -/

/-- The south neighbour in the tableau: `t_S(i, j + 1) = t_C(i, j)` (C5). -/
theorem grid_tS {i j : ℕ} (hi : i < MachineM.Nd d) (hj : j + 1 < MachineM.Nd d) :
    (cellAt ω τ d m1 m2 i (j + 1)).tS = some (cellAt ω τ d m1 m2 i j).tC ∧
      (cellAt ω τ d m1 m2 i j).tN = some (cellAt ω τ d m1 m2 i (j + 1)).tC := by
  obtain ⟨l, hl1, hl2⟩ := hs.chanV_some hd m1 m2 hi hj
  obtain ⟨-, -, -, -, -, -, c5, -⟩ := hs.rules hd m1 m2 hi hj
  obtain ⟨-, -, -, -, -, -, c5', -⟩ := hs.rules hd m1 m2 hi (show j < MachineM.Nd d by omega)
  obtain ⟨-, -, fS, -⟩ := hs.grids_c hd m1 m2 hi hj
  obtain ⟨-, -, -, fN⟩ := hs.grids_c hd m1 m2 hi (show j < MachineM.Nd d by omega)
  obtain ⟨e1, e2⟩ := c5.2.1 (by rw [fS]; simp) l hl2
  obtain ⟨e3, e4⟩ := c5'.2.2.2.1 (by rw [fN]; simp; omega) l hl1
  exact ⟨by rw [e1, e3], by rw [e4, e2]⟩

/-- The ends of the tableau: `t_S(i, 0) = ⊥` and `t_N(i, N - 1) = ⊥` (C5). -/
theorem grid_tS_zero {i : ℕ} (hi : i < MachineM.Nd d) :
    (cellAt ω τ d m1 m2 i 0).tS = none ∧ (cellAt ω τ d m1 m2 i (MachineM.Nd d - 1)).tN = none := by
  have h0 : 0 < MachineM.Nd d := by have := MachineM.two_le_Nd d; omega
  obtain ⟨-, -, -, -, -, -, c5, -⟩ := hs.rules hd m1 m2 hi h0
  obtain ⟨-, -, -, -, -, -, c5', -⟩ := hs.rules hd m1 m2 hi lastCol
  obtain ⟨-, -, fS, -⟩ := hs.grids_c hd m1 m2 hi h0
  obtain ⟨-, -, -, fN⟩ := hs.grids_c hd m1 m2 hi lastCol
  exact ⟨c5.1 (by rw [fS]; rfl), c5'.2.2.1 (by rw [fN]; simp)⟩

/-- **`bg:grid`(c)**: `t_C(i, j) = c_i(j)`, the run of `M` (`mach:def-run`). -/
theorem grid_c {i j : ℕ} (hi : i < MachineM.Nd d) (hj : j < MachineM.Nd d) :
    (cellAt ω τ d m1 m2 i j).tC = MachineM.runM U d i ⟨j, hj⟩ := by
  induction i generalizing j with
  | zero =>
    obtain ⟨-, -, -, -, -, -, c5, -⟩ := hs.rules hd m1 m2 hi hj
    obtain ⟨fW, -, fS, -⟩ := hs.grids_c hd m1 m2 hi hj
    rw [c5.2.2.2.2.1 (by rw [fW]; rfl), hs.grid_b hd m1 m2 hi hj, fS]
    rfl
  | succ i ih =>
    have hi' : i < MachineM.Nd d := by omega
    obtain ⟨l, hl1, hl2⟩ := hs.chanH_some hd m1 m2 hi hj
    obtain ⟨-, -, -, -, -, -, c5, -⟩ := hs.rules hd m1 m2 hi hj
    obtain ⟨-, -, -, -, -, -, c5', -⟩ := hs.rules hd m1 m2 hi' hj
    obtain ⟨fW, -, -, -⟩ := hs.grids_c hd m1 m2 hi hj
    rw [c5.2.2.2.2.2.1 (by rw [fW]; simp) l hl2, c5'.2.2.2.2.2.2 l hl1,
      MachineM.runM, Function.iterate_succ_apply', ← MachineM.runM]
    simp only [MachineM.nextRow]
    congr 1
    · rcases j with _ | j
      · simp [(hs.grid_tS_zero hd m1 m2 hi').1]
      · rw [(hs.grid_tS hd m1 m2 hi' hj).1, ih hi' (by omega)]
        simp
    · exact ih hi' hj
    · by_cases hj1 : j + 1 < MachineM.Nd d
      · rw [(hs.grid_tS hd m1 m2 hi' hj1).2, ih hi' hj1, dif_pos hj1]
      · have e : j = MachineM.Nd d - 1 := by omega
        subst e
        rw [(hs.grid_tS_zero hd m1 m2 hi').2, dif_neg hj1]

/-! ## `bg:grid`(d): readiness and masks -/

/-- **`bg:grid`(d)**, first claim: `rdy(i, j) = ρ_d` (C6: read at `(N-1, 0)`, copied north along
the last column and west along each row). -/
theorem grid_rdy {i j : ℕ} (hi : i < MachineM.Nd d) (hj : j < MachineM.Nd d) :
    (cellAt ω τ d m1 m2 i j).rdy = decide (MachineM.ready U d) := by
  have hlast : ∀ j, j < MachineM.Nd d →
      (cellAt ω τ d m1 m2 (MachineM.Nd d - 1) j).rdy = decide (MachineM.ready U d) := by
    intro j hj
    induction j with
    | zero =>
      obtain ⟨-, -, -, -, -, -, -, c6, -⟩ := hs.rules hd m1 m2 lastCol hj
      obtain ⟨-, fE, fS, -⟩ := hs.grids_c hd m1 m2 lastCol hj
      rw [(c6.1 (by rw [fE]; simp)).1 (by rw [fS]; rfl), hs.grid_c hd m1 m2 lastCol hj]
      rfl
    | succ j ih =>
      have hj' : j < MachineM.Nd d := by omega
      obtain ⟨l, hl1, hl2⟩ := hs.chanV_some hd m1 m2 lastCol hj
      obtain ⟨-, -, -, -, -, -, -, c6, -⟩ := hs.rules hd m1 m2 lastCol hj
      obtain ⟨-, -, -, -, -, -, -, c6', -⟩ := hs.rules hd m1 m2 lastCol hj'
      obtain ⟨-, fE, fS, -⟩ := hs.grids_c hd m1 m2 lastCol hj
      obtain ⟨-, fE', -, -⟩ := hs.grids_c hd m1 m2 lastCol hj'
      rw [(c6.1 (by rw [fE]; simp)).2.1 (by rw [fS]; simp) l hl2,
        (c6'.1 (by rw [fE']; simp)).2.2 l hl1, ih hj']
  refine desc_ind (P := fun i => (cellAt ω τ d m1 m2 i j).rdy = decide (MachineM.ready U d))
    (hlast j hj) ?_ hi
  intro i hi1 ih
  obtain ⟨l, hl1, hl2⟩ := hs.chanH_some hd m1 m2 hi1 hj
  obtain ⟨-, -, -, -, -, -, -, c6, -⟩ := hs.rules hd m1 m2 (show i < MachineM.Nd d by omega) hj
  obtain ⟨-, -, -, -, -, -, -, c6', -⟩ := hs.rules hd m1 m2 hi1 hj
  obtain ⟨-, fE, -, -⟩ := hs.grids_c hd m1 m2 (show i < MachineM.Nd d by omega) hj
  rw [(c6.2.1 (by rw [fE]; simp; omega)).1 l hl1, c6'.2.2 l hl2, ih]

/-- **`bg:grid`(d)**: `rdy(i, j) = ρ_d` and `g^±(i, j) = ρ_d 𝗆^±(c_{N-1}(j))` (C6, C7). -/
theorem grid_d {i j : ℕ} (hi : i < MachineM.Nd d) (hj : j < MachineM.Nd d) :
    (cellAt ω τ d m1 m2 i j).rdy = decide (MachineM.ready U d) ∧
    (cellAt ω τ d m1 m2 i j).gm =
      (decide (MachineM.ready U d) && maskMinus U (MachineM.runM U d (MachineM.Nd d - 1) ⟨j, hj⟩)) ∧
    (cellAt ω τ d m1 m2 i j).gp =
      (decide (MachineM.ready U d) && maskPlus U (MachineM.runM U d (MachineM.Nd d - 1) ⟨j, hj⟩)) := by
  refine ⟨hs.grid_rdy hd m1 m2 hi hj, ?_⟩
  refine desc_ind (P := fun i => (cellAt ω τ d m1 m2 i j).gm =
      (decide (MachineM.ready U d) && maskMinus U (MachineM.runM U d (MachineM.Nd d - 1) ⟨j, hj⟩)) ∧
    (cellAt ω τ d m1 m2 i j).gp =
      (decide (MachineM.ready U d) && maskPlus U (MachineM.runM U d (MachineM.Nd d - 1) ⟨j, hj⟩)))
    ?_ ?_ hi
  · obtain ⟨-, -, -, -, -, -, -, -, c7, -⟩ := hs.rules hd m1 m2 lastCol hj
    obtain ⟨-, fE, -, -⟩ := hs.grids_c hd m1 m2 lastCol hj
    obtain ⟨e1, e2⟩ := c7.1 (by rw [fE]; simp)
    rw [e1, e2, hs.grid_rdy hd m1 m2 lastCol hj, hs.grid_c hd m1 m2 lastCol hj]
    exact ⟨rfl, rfl⟩
  · intro i hi1 ih
    obtain ⟨l, hl1, hl2⟩ := hs.chanH_some hd m1 m2 hi1 hj
    obtain ⟨-, -, -, -, -, -, -, -, c7, -⟩ := hs.rules hd m1 m2 (show i < MachineM.Nd d by omega) hj
    obtain ⟨-, -, -, -, -, -, -, -, c7', -⟩ := hs.rules hd m1 m2 hi1 hj
    obtain ⟨-, fE, -, -⟩ := hs.grids_c hd m1 m2 (show i < MachineM.Nd d by omega) hj
    obtain ⟨e1, e2⟩ := c7.2.1 (by rw [fE]; simp; omega) l hl1
    obtain ⟨e3, e4⟩ := c7'.2.2 l hl2
    rw [e1, e2, e3, e4]
    exact ih

end Setting

end UPD.BG

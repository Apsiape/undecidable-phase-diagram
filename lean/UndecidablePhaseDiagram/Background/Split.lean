/-
# Section 4.7: background and payload (`int:sub-split`)

New in this project. "The payload coordinates of a site are its spin `σ`, its four wire values,
the components `x` and `y` of its cell record, and the components `x` of `ℓ^S` and `ℓ^N`. All
other fields and components form the background of the site. A background configuration is a map
from `ℤ²` to background values; for a configuration `ω` we write `ω = (𝔟, p)`."

* `BgVal U`: the background value of a site (`VColB`: a vertical colour without `x`; `CellRecB`:
  a cell record without `x`, `y`); `bgPart`.
* `PayVal`: the payload value of a site; the components `x`, `y` of an absent record (`𝔨 = ∘`) and
  `x` of an absent colour (`ℓ = ∘`) are read as `0` (`payPart`). `merge b p` puts them together;
  `merge_split`, `bgPart_merge`, `payPart_merge` (for `Compatible b p`: the components that the
  background leaves absent are `0`), so `splitEquiv : SiteVal U ≃ {(b, p) | Compatible b p}`.
* `bgOf ω`, `payOf ω`: the background and payload configurations; `bgOf_shift`.
* Matching splits into a background part and a payload part (`cE_eq_cW_iff`, `cN_eq_cS_iff`): the
  wire values, and the `x` components of vertical colours, are the payload of the colours.
-/
import UndecidablePhaseDiagram.Background.Computation

set_option autoImplicit false

namespace UPD.BG

open UPD.Scaffold

variable {U : Machine}

/-! ## Background and payload values -/

section Values

variable (U)

/-- A non-empty vertical logical colour without its payload component `x`:
`(cy, ay, rc, rdy, tb)`. -/
structure VColB where
  /-- `cy` -/
  cy : Bool
  /-- `ay` -/
  ay : Bool
  /-- `rc` -/
  rc : Fin 81
  /-- `rdy` -/
  rdy : Bool
  /-- `tb` -/
  tb : CellM U × CellM U
  deriving DecidableEq

/-- A cell record without its payload components `x`, `y`. -/
structure CellRecB where
  /-- `ct_in` -/
  ctIn : Bool
  /-- `ct` -/
  ct : Bool
  /-- `cy` -/
  cy : Bool
  /-- `ay` -/
  ay : Bool
  /-- `sm` -/
  sm : Bool
  /-- `hot` -/
  hot : Bool
  /-- `rdy` -/
  rdy : Bool
  /-- `g⁻` -/
  gm : Bool
  /-- `g⁺` -/
  gp : Bool
  /-- `rc` -/
  rc : Fin 81
  /-- `t_S` -/
  tS : Option (CellM U)
  /-- `t_N` -/
  tN : Option (CellM U)
  /-- `t_C` -/
  tC : CellM U
  deriving DecidableEq

/-- `int:sub-split`: the background value of a site: every field and component except the spin,
the wire values, the components `x`, `y` of the cell record and `x` of `ℓ^S`, `ℓ^N`. -/
structure BgVal where
  /-- (F1) -/
  q : Quarter
  /-- (F2) -/
  oW : LR × LR
  /-- (F2) -/
  oE : LR × LR
  /-- (F2) -/
  oS : BT × BT
  /-- (F2) -/
  oN : BT × BT
  /-- (F3) -/
  eW : Option (Ev × Ev)
  /-- (F3) -/
  eE : Option (Ev × Ev)
  /-- (F3) -/
  eS : Option (Ev × Ev)
  /-- (F3) -/
  eN : Option (Ev × Ev)
  /-- (F4), horizontal colours (no payload component) -/
  lW : Option (HCol U)
  /-- (F4) -/
  lE : Option (HCol U)
  /-- (F4), vertical colours without `x` -/
  lS : Option (VColB U)
  /-- (F4) -/
  lN : Option (VColB U)
  /-- (F5) without `x`, `y` -/
  k : Option (CellRecB U)
  /-- (F6) -/
  rowM : Bool
  /-- (F6) -/
  colM : Bool
  deriving DecidableEq

end Values

/-- `int:sub-split`: the payload value of a site: the spin, the four wire values, the components
`x`, `y` of the cell record and `x` of `ℓ^S`, `ℓ^N` (read as `0` when the record or the colour is
`∘`). -/
structure PayVal where
  /-- (F7) -/
  spin : Spin
  /-- (F8) -/
  wW : Option Spin
  /-- (F8) -/
  wE : Option Spin
  /-- (F8) -/
  wS : Option Spin
  /-- (F8) -/
  wN : Option Spin
  /-- `x` of the cell record -/
  kx : Fin 4 → Bool
  /-- `y` of the cell record -/
  ky : Fin 4 → Bool
  /-- `x` of `ℓ^S` -/
  lSx : Fin 4 → Bool
  /-- `x` of `ℓ^N` -/
  lNx : Fin 4 → Bool

/-- The background part of a vertical colour. -/
def _root_.UPD.VCol.bg (l : VCol U) : VColB U := ⟨l.cy, l.ay, l.rc, l.rdy, l.tb⟩

/-- A vertical colour from its background part and `x`. -/
def VColB.withX (l : VColB U) (x : Fin 4 → Bool) : VCol U := ⟨l.cy, l.ay, l.rc, l.rdy, l.tb, x⟩

/-- The background part of a cell record. -/
def _root_.UPD.CellRec.bg (c : CellRec U) : CellRecB U :=
  ⟨c.ctIn, c.ct, c.cy, c.ay, c.sm, c.hot, c.rdy, c.gm, c.gp, c.rc, c.tS, c.tN, c.tC⟩

/-- A cell record from its background part and `x`, `y`. -/
def CellRecB.withXY (c : CellRecB U) (x y : Fin 4 → Bool) : CellRec U :=
  ⟨c.ctIn, c.ct, c.cy, c.ay, c.sm, c.hot, c.rdy, c.gm, c.gp, c.rc, c.tS, c.tN, c.tC, x, y⟩

theorem _root_.UPD.VCol.withX_bg (l : VCol U) : l.bg.withX l.x = l := rfl

theorem VColB.bg_withX (l : VColB U) (x : Fin 4 → Bool) : (l.withX x).bg = l := rfl

theorem _root_.UPD.CellRec.withXY_bg (c : CellRec U) : c.bg.withXY c.x c.y = c := rfl

theorem CellRecB.bg_withXY (c : CellRecB U) (x y : Fin 4 → Bool) : (c.withXY x y).bg = c := rfl

/-- `int:sub-split`: the background value of a site value. -/
def bgPart (s : SiteVal U) : BgVal U :=
  ⟨s.q, s.oW, s.oE, s.oS, s.oN, s.eW, s.eE, s.eS, s.eN, s.lW, s.lE, s.lS.map VCol.bg,
    s.lN.map VCol.bg, s.k.map CellRec.bg, s.rowM, s.colM⟩

/-- The `x` component of a vertical colour, `0` for `∘`. -/
def xOf (l : Option (VCol U)) : Fin 4 → Bool := (l.map VCol.x).getD fun _ => false

/-- `int:sub-split`: the payload value of a site value. -/
def payPart (s : SiteVal U) : PayVal :=
  ⟨s.spin, s.wW, s.wE, s.wS, s.wN, (s.k.map CellRec.x).getD fun _ => false,
    (s.k.map CellRec.y).getD fun _ => false, xOf s.lS, xOf s.lN⟩

/-- `ω = (𝔟, p)`: the site value with background `b` and payload `p`. -/
def merge (b : BgVal U) (p : PayVal) : SiteVal U :=
  ⟨b.q, b.oW, b.oE, b.oS, b.oN, b.eW, b.eE, b.eS, b.eN, b.lW, b.lE,
    b.lS.map fun l => l.withX p.lSx, b.lN.map fun l => l.withX p.lNx,
    b.k.map fun c => c.withXY p.kx p.ky, b.rowM, b.colM, p.spin, p.wW, p.wE, p.wS, p.wN⟩

/-- The payload components that the background leaves absent are `0`. -/
def Compatible (b : BgVal U) (p : PayVal) : Prop :=
  (b.k = none → p.kx = (fun _ => false) ∧ p.ky = fun _ => false) ∧
    (b.lS = none → p.lSx = fun _ => false) ∧ (b.lN = none → p.lNx = fun _ => false)

theorem merge_split (s : SiteVal U) : merge (bgPart s) (payPart s) = s := by
  obtain ⟨q, oW, oE, oS, oN, eW, eE, eS, eN, lW, lE, lS, lN, k, rM, cM, sp, wW, wE, wS, wN⟩ := s
  simp only [merge, bgPart, payPart, Option.map_map, xOf]
  congr 1
  · cases lS <;> rfl
  · cases lN <;> rfl
  · cases k <;> rfl

theorem bgPart_merge (b : BgVal U) (p : PayVal) : bgPart (merge b p) = b := by
  obtain ⟨q, oW, oE, oS, oN, eW, eE, eS, eN, lW, lE, lS, lN, k, rM, cM⟩ := b
  simp only [merge, bgPart, Option.map_map]
  congr 1
  · cases lS <;> rfl
  · cases lN <;> rfl
  · cases k <;> rfl

theorem compatible_split (s : SiteVal U) : Compatible (bgPart s) (payPart s) := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · simp only [bgPart, Option.map_eq_none_iff] at h
    simp [payPart, h]
  · simp only [bgPart, Option.map_eq_none_iff] at h
    simp [payPart, xOf, h]
  · simp only [bgPart, Option.map_eq_none_iff] at h
    simp [payPart, xOf, h]

theorem payPart_merge {b : BgVal U} {p : PayVal} (h : Compatible b p) :
    payPart (merge b p) = p := by
  obtain ⟨sp, wW, wE, wS, wN, kx, ky, lSx, lNx⟩ := p
  obtain ⟨hk, hS, hN⟩ := h
  dsimp only at hk hS hN
  simp only [payPart, merge, xOf, Option.map_map]
  congr 1
  · rcases hb : b.k with _ | c
    · simp [(hk hb).1]
    · rfl
  · rcases hb : b.k with _ | c
    · simp [(hk hb).2]
    · rfl
  · rcases hb : b.lS with _ | l
    · simp [hS hb]
    · rfl
  · rcases hb : b.lN with _ | l
    · simp [hN hb]
    · rfl

/-- `int:sub-split`: a site value is the same as a background value and a compatible payload
value. -/
def splitEquiv : SiteVal U ≃ {bp : BgVal U × PayVal // Compatible bp.1 bp.2} where
  toFun s := ⟨(bgPart s, payPart s), compatible_split s⟩
  invFun bp := merge bp.1.1 bp.1.2
  left_inv s := merge_split s
  right_inv bp := by
    obtain ⟨⟨b, p⟩, h⟩ := bp
    ext
    · exact bgPart_merge b p
    · exact payPart_merge h

/-! ## Configurations -/

/-- `int:sub-split`: the background configuration `𝔟` of `ω`. -/
def bgOf (ω : Config (SiteVal U)) : Plane → BgVal U := fun ξ => bgPart (ω ξ)

/-- `int:sub-split`: the payload configuration `p` of `ω`. -/
def payOf (ω : Config (SiteVal U)) : Plane → PayVal := fun ξ => payPart (ω ξ)

theorem merge_bgOf_payOf (ω : Config (SiteVal U)) : (fun ξ => merge (bgOf ω ξ) (payOf ω ξ)) = ω :=
  funext fun ξ => merge_split (ω ξ)

/-- The background of a translate is the translate of the background. -/
theorem bgOf_shift (a : Plane) (ω : Config (SiteVal U)) : bgOf (shift a ω) = shift a (bgOf ω) :=
  rfl

/-! ## Colours: background and payload parts -/

/-- The background part of the east colour `c_E`: all but the wire value. -/
def BgVal.cE (b : BgVal U) :
    QColH × (LR × LR) × Option (Ev × Ev) × Option (HCol U) × Bool :=
  (b.q.colE, b.oE, b.eE, b.lE, b.rowM)

/-- The background part of the west colour `c_W`. -/
def BgVal.cW (b : BgVal U) :
    QColH × (LR × LR) × Option (Ev × Ev) × Option (HCol U) × Bool :=
  (b.q.colW, b.oW, b.eW, b.lW, b.rowM)

/-- The background part of the north colour `c_N`: all but the wire value and the `x` of `ℓ^N`. -/
def BgVal.cN (b : BgVal U) :
    QColV × (BT × BT) × Option (Ev × Ev) × Option (VColB U) × Bool :=
  (b.q.colN, b.oN, b.eN, b.lN, b.colM)

/-- The background part of the south colour `c_S`. -/
def BgVal.cS (b : BgVal U) :
    QColV × (BT × BT) × Option (Ev × Ev) × Option (VColB U) × Bool :=
  (b.q.colS, b.oS, b.eS, b.lS, b.colM)

/-- Horizontal matching is matching of the background parts and of the wire values. -/
theorem cE_eq_cW_iff (s t : SiteVal U) :
    s.cE = t.cW ↔ (bgPart s).cE = (bgPart t).cW ∧ s.wE = t.wW := by
  simp only [SiteVal.cE, SiteVal.cW, BgVal.cE, BgVal.cW, bgPart, Prod.mk.injEq]
  tauto

theorem option_vcol_eq_iff (l l' : Option (VCol U)) :
    l = l' ↔ l.map VCol.bg = l'.map VCol.bg ∧ xOf l = xOf l' := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    rcases l with _ | l <;> rcases l' with _ | l'
    · rfl
    · simp at h1
    · simp at h1
    · simp only [Option.map_some, Option.some.injEq, xOf, Option.getD_some] at h1 h2
      rw [← VCol.withX_bg l, ← VCol.withX_bg l', h1, h2]

/-- Vertical matching is matching of the background parts, of the wire values and of the `x`
components of the vertical colours. -/
theorem cN_eq_cS_iff (s t : SiteVal U) :
    s.cN = t.cS ↔ (bgPart s).cN = (bgPart t).cS ∧ s.wN = t.wS ∧ xOf s.lN = xOf t.lS := by
  simp only [SiteVal.cN, SiteVal.cS, BgVal.cN, BgVal.cS, bgPart, Prod.mk.injEq,
    option_vcol_eq_iff s.lN t.lS]
  tauto

end UPD.BG

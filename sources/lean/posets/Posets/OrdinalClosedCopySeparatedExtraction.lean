import Posets.OrdinalClosedCopySeparatedGeometry
import Posets.OrdinalClosedCopyHeightLoss

/-! Extract actual coordinate geometry from uniform order bounds on a closed
core.  No regularity assumption on the initial cardinal is used. -/

noncomputable section
open Set Topology Order
universe u
namespace Posets
open ThesisCommon

theorem ordinalSeparatedBandCoreGeometry_of_uniform_order_bound
    {F : Set Ordinal.{u}} {θ β upper a b : Ordinal.{u}}
    (hθ : θ ∈ ordinalTowerLevel θ upper)
    (hθbound : θ ≤ Ordinal.omega0 ^ upper * β)
    (hF : IsCompact F) (hFθ : F ⊆ Iic θ)
    (hb : b ≠ 0) (habs : 1 + b = b) (hab : a + b ≤ upper)
    (hlarge : Ordinal.lift.{u+1} (Ordinal.omega0 ^ (a + b) * Order.succ β) <
      Ordinal.type (· < · : F → _ → Prop)) :
    Nonempty (OrdinalSeparatedBandCoreGeometry F θ upper a b) := by
  have hrpos : 0 < a + b :=
    (Ordinal.pos_iff_ne_zero.mpr hb).trans_le (Ordinal.le_add_left b a)
  obtain ⟨y, hyo, hyrank⟩ := ordinalTower_exists_high_upper_cell_uniform
    (ne_of_gt (hrpos.trans_le hab)) hrpos.ne' hθ hθbound hF hFθ hlarge
  exact ordinalSeparatedBandCoreGeometry_of_isolated_upper_cell
    hθ y hyo hF hFθ hb habs hab hyrank

theorem ordinalSeparatedBandCoreGeometry_of_height_loss
    {c : Cardinal.{u}} (hc : Cardinal.aleph0 ≤ c) (n m : ℕ)
    {upper a b : Ordinal.{u}}
    (hscaleUpper : Ordinal.omega0 ^ upper = c.ord ^ (n + 2 : Ordinal))
    (hscaleLower : Ordinal.omega0 ^ (a + b) = c.ord ^ (n + 1 : Ordinal))
    (hb : b ≠ 0) (habs : 1 + b = b) (hab : a + b ≤ upper)
    (F : Set Ordinal.{u}) (hF : IsCompact F)
    (hFθ : F ⊆ Iic (c.ord ^ (n + 2 : Ordinal) * c.ord ^ (m : Ordinal)))
    (hfull : Ordinal.lift.{u+1} (c.ord ^ (n + 2 : Ordinal) * c.ord ^ (m : Ordinal)) ≤
      Ordinal.type (· < · : F → _ → Prop)) :
    Nonempty (OrdinalSeparatedBandCoreGeometry F
      (c.ord ^ (n + 2 : Ordinal) * c.ord ^ (m : Ordinal)) upper a b) := by
  have hω : Ordinal.omega0 ≤ c.ord := by
    simpa only [Cardinal.ord_aleph0] using Cardinal.ord_le_ord.mpr hc
  have hpos : 0 < c.ord := Ordinal.omega0_pos.trans_le hω
  have hrpos : 0 < a + b :=
    (Ordinal.pos_iff_ne_zero.mpr hb).trans_le (Ordinal.le_add_left b a)
  obtain ⟨y, hyo, hyrank⟩ := ordinalTower_exists_high_upper_cell_height_loss hc n m
    (ne_of_gt (hrpos.trans_le hab)) hrpos.ne' hscaleUpper hscaleLower F hF hFθ hfull
  have hθ : c.ord ^ (n + 2 : Ordinal) * c.ord ^ (m : Ordinal) ∈
      ordinalTowerLevel (c.ord ^ (n + 2 : Ordinal) * c.ord ^ (m : Ordinal)) upper := by
    rw [← hscaleUpper]
    exact ordinalTowerLevel_contains_power_grid _ upper
      (Ordinal.opow_ne_zero _ hpos.ne') le_rfl
  exact ordinalSeparatedBandCoreGeometry_of_isolated_upper_cell
    hθ y hyo hF hFθ hb habs hab hyrank

end Posets

import Posets.OrdinalClosedCopyUniformUpperFiber
import Posets.OrdinalClosedCopyInitialPowers

/-! Losing one finite exponent gives upper-cell extraction for every
uncountable initial ordinal, including singular initial ordinals. -/

noncomputable section
open Set Topology Order
universe u
namespace Posets
open ThesisCommon

theorem ordinal_initial_packet_threshold_lt
    {c : Cardinal.{u}} (hc : Cardinal.aleph0 ≤ c) {δ : Ordinal.{u}}
    (hδ : 0 < δ) (m : ℕ) :
    δ * Order.succ (c.ord ^ (m : Ordinal)) < δ * (c.ord * c.ord ^ (m : Ordinal)) := by
  have hω : Ordinal.omega0 ≤ c.ord := by
    simpa only [Cardinal.ord_aleph0] using Cardinal.ord_le_ord.mpr hc
  have h2 : (2 : Ordinal.{u}) < c.ord := (Ordinal.nat_lt_omega0 2).trans_le hω
  have hp : 0 < c.ord ^ (m : Ordinal) :=
    Ordinal.opow_pos _ (Ordinal.omega0_pos.trans_le hω)
  have hle : δ ≤ δ * c.ord ^ (m : Ordinal) := Ordinal.le_mul_left δ hp
  have he : c.ord * c.ord ^ (m : Ordinal) = c.ord ^ (m : Ordinal) * c.ord := by
    rw [← Ordinal.opow_one_add, Ordinal.one_add_natCast]
    exact Ordinal.opow_succ _ _
  calc
    δ * Order.succ (c.ord ^ (m : Ordinal)) = δ * c.ord ^ (m : Ordinal) + δ :=
      Ordinal.mul_succ _ _
    _ ≤ δ * c.ord ^ (m : Ordinal) + δ * c.ord ^ (m : Ordinal) :=
      add_le_add_left hle _
    _ = (δ * c.ord ^ (m : Ordinal)) * 2 := by
      rw [← Ordinal.succ_one, Ordinal.mul_succ, mul_one]
    _ < (δ * c.ord ^ (m : Ordinal)) * c.ord := mul_lt_mul_of_pos_left h2 (mul_pos hδ hp)
    _ = δ * (c.ord * c.ord ^ (m : Ordinal)) := by rw [he, mul_assoc]

theorem ordinalTower_exists_high_upper_cell_height_loss
    {c : Cardinal.{u}} (hc : Cardinal.aleph0 ≤ c) (n m : ℕ)
    {upperRank retainedRank : Ordinal.{u}}
    (hupper : upperRank ≠ 0) (hretained : retainedRank ≠ 0)
    (hscaleUpper : Ordinal.omega0 ^ upperRank = c.ord ^ (n + 2 : Ordinal))
    (hscaleLower : Ordinal.omega0 ^ retainedRank = c.ord ^ (n + 1 : Ordinal))
    (F : Set Ordinal.{u}) (hF : IsCompact F)
    (hFθ : F ⊆ Iic (c.ord ^ (n + 2 : Ordinal) * c.ord ^ (m : Ordinal)))
    (hfull : Ordinal.lift.{u+1} (c.ord ^ (n + 2 : Ordinal) * c.ord ^ (m : Ordinal)) ≤
      Ordinal.type (· < · : F → _ → Prop)) :
    ∃ y : ordinalTowerLevel
        (c.ord ^ (n + 2 : Ordinal) * c.ord ^ (m : Ordinal)) upperRank,
      IsOpen ({y} : Set (ordinalTowerLevel
        (c.ord ^ (n + 2 : Ordinal) * c.ord ^ (m : Ordinal)) upperRank)) ∧
      (ordinalDerived (F ∩ {x | ordinalCeiling (ordinalTowerLevel
        (c.ord ^ (n + 2 : Ordinal) * c.ord ^ (m : Ordinal)) upperRank) x = y.val}) retainedRank).Nonempty := by
  have hω : Ordinal.omega0 ≤ c.ord := by
    simpa only [Cardinal.ord_aleph0] using Cardinal.ord_le_ord.mpr hc
  have hpos : 0 < c.ord := Ordinal.omega0_pos.trans_le hω
  have hθ : c.ord ^ (n + 2 : Ordinal) * c.ord ^ (m : Ordinal) ∈
      ordinalTowerLevel (c.ord ^ (n + 2 : Ordinal) * c.ord ^ (m : Ordinal)) upperRank := by
    rw [← hscaleUpper]
    exact ordinalTowerLevel_contains_power_grid _ upperRank
      (Ordinal.opow_ne_zero _ hpos.ne') le_rfl
  apply ordinalTower_exists_high_upper_cell_uniform hupper hretained hθ
    (by rw [hscaleUpper]) hF hFθ
  rw [hscaleLower]
  apply (Ordinal.lift_lt.mpr ?_).trans_le hfull
  have ht := ordinal_initial_packet_threshold_lt hc (Ordinal.opow_pos (n + 1 : Ordinal) hpos) m
  have he : c.ord ^ (n + 1 : Ordinal) * c.ord = c.ord ^ (n + 2 : Ordinal) := by
    rw [show (2 : Ordinal.{u}) = 1 + 1 from
      ((Ordinal.add_one_eq_succ 1).trans Ordinal.succ_one).symm,
      ← add_assoc, Ordinal.add_one_eq_succ]
    exact (Ordinal.opow_succ c.ord (n + 1 : Ordinal)).symm
  simpa only [← mul_assoc, he] using ht

end Posets

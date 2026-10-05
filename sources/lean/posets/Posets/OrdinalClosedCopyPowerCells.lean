import Posets.OrdinalClosedCopyUpperCell

/-! Concrete finite-power upper-cell extraction.  A full-order core in
δ·κ^(m+1) contains a full-order core in one clopen δ-cell. -/

noncomputable section
open Set Topology Order
universe u
namespace Posets
open ThesisCommon

theorem ordinal_regular_packet_threshold_lt
    {c : Cardinal.{u}} (hc : c.IsRegular) {δ : Ordinal.{u}}
    (hδ : 0 < δ) (m : ℕ) :
    δ * Order.succ (c.ord ^ (m : Ordinal)) < δ * (c.ord * c.ord ^ (m : Ordinal)) := by
  have hω : Ordinal.omega0 ≤ c.ord := by
    simpa only [Cardinal.ord_aleph0] using Cardinal.ord_le_ord.mpr hc.aleph0_le
  have h2 : (2 : Ordinal.{u}) < c.ord := (Ordinal.nat_lt_omega0 2).trans_le hω
  have hp : 0 < c.ord ^ (m : Ordinal) := Ordinal.opow_pos _ hc.ord_pos
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

theorem ordinalTower_exists_high_upper_cell_finite_power
    {c : Cardinal.{u}} (hc : c.IsRegular) (n m : ℕ) {a : Ordinal.{u}}
    (ha : a ≠ 0) (hscale : Ordinal.omega0 ^ a = c.ord ^ (n + 1 : Ordinal))
    (F : Set Ordinal.{u}) (hF : IsCompact F)
    (hFθ : F ⊆ Iic (c.ord ^ (n + 1 : Ordinal) * (c.ord * c.ord ^ (m : Ordinal))))
    (hfull : Ordinal.lift.{u+1}
        (c.ord ^ (n + 1 : Ordinal) * (c.ord * c.ord ^ (m : Ordinal))) ≤
      Ordinal.type (· < · : F → _ → Prop)) :
    ∃ y : ordinalTowerLevel
        (c.ord ^ (n + 1 : Ordinal) * (c.ord * c.ord ^ (m : Ordinal))) a,
      IsOpen ({y} : Set (ordinalTowerLevel
        (c.ord ^ (n + 1 : Ordinal) * (c.ord * c.ord ^ (m : Ordinal))) a)) ∧
      (ordinalDerived (F ∩ {x | ordinalCeiling (ordinalTowerLevel
        (c.ord ^ (n + 1 : Ordinal) * (c.ord * c.ord ^ (m : Ordinal))) a) x = y.val}) a).Nonempty := by
  have hθ : c.ord ^ (n + 1 : Ordinal) * (c.ord * c.ord ^ (m : Ordinal)) ∈
      ordinalTowerLevel (c.ord ^ (n + 1 : Ordinal) * (c.ord * c.ord ^ (m : Ordinal))) a := by
    rw [← hscale]
    exact ordinalTowerLevel_contains_power_grid _ a
      (mul_ne_zero hc.ord_pos.ne' (Ordinal.opow_ne_zero _ hc.ord_pos.ne')) le_rfl
  apply ordinalTower_exists_high_upper_cell hc n ha hscale hθ le_rfl hF hFθ
  exact (Ordinal.lift_lt.mpr (ordinal_regular_packet_threshold_lt hc
    (Ordinal.opow_pos _ hc.ord_pos) m)).trans_le hfull

theorem ordinalTower_exists_high_top_cell
    {F : Set Ordinal.{u}} {a : Ordinal.{u}} (ha : a ≠ 0)
    (hrank : (ordinalDerived F a).Nonempty) :
    ∃ y : ordinalTowerLevel (Ordinal.omega0 ^ a) a,
      IsOpen ({y} : Set (ordinalTowerLevel (Ordinal.omega0 ^ a) a)) ∧
      (ordinalDerived (F ∩ {x | ordinalCeiling
        (ordinalTowerLevel (Ordinal.omega0 ^ a) a) x = y.val}) a).Nonempty := by
  have hA : ordinalTowerLevel (Ordinal.omega0 ^ a) a = {Ordinal.omega0 ^ a} :=
    ordinalDerived_Iic_power_self ha
  have hmem : Ordinal.omega0 ^ a ∈ ordinalTowerLevel (Ordinal.omega0 ^ a) a := by
    rw [hA]
    exact mem_singleton _
  let y : ordinalTowerLevel (Ordinal.omega0 ^ a) a := ⟨_, hmem⟩
  have ho : ({y} : Set (ordinalTowerLevel (Ordinal.omega0 ^ a) a)) = univ := by
    ext z
    simp only [mem_singleton_iff, mem_univ, iff_true]
    apply Subtype.ext
    exact mem_singleton_iff.mp (hA ▸ z.property)
  refine ⟨y, ho ▸ isOpen_univ, ?_⟩
  have hc (x : Ordinal.{u}) : ordinalCeiling
      (ordinalTowerLevel (Ordinal.omega0 ^ a) a) x = y.val := by
    exact mem_singleton_iff.mp (hA ▸ ordinalCeiling_mem
      (ordinalTowerLevel_isCompact _ _) ⟨_, hmem⟩ x)
  have he : F ∩ {x | ordinalCeiling (ordinalTowerLevel (Ordinal.omega0 ^ a) a) x = y.val} = F := by
    ext x
    simp only [mem_inter_iff, mem_setOf_eq, hc x, and_true]
  rwa [he]

end Posets

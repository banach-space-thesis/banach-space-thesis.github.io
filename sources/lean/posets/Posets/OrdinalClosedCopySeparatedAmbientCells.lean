import Posets.OrdinalClosedCopySeparatedAmbientGeometry
import Posets.OrdinalAmbientCoreBandsRestriction

/-! The ambient coordinate is constant on each original lower ceiling
cell, with no inverse chosen outside the actual outer block. -/

noncomputable section
open Set Topology
universe u v
namespace Posets
open ThesisCommon

variable {F : Set Ordinal.{u}} {θ upper a b : Ordinal.{u}}
variable (G : OrdinalSeparatedBandCoreGeometry F θ upper a b)
variable {K : Type v} [TopologicalSpace K] [T2Space K]
variable (e : Iic θ → K) (he : IsOpenEmbedding e)

include he in
omit [T2Space K] in
theorem ordinalSeparatedBandAmbientSet_mem_iff (x : Iic θ) :
    e x ∈ ordinalSeparatedBandAmbientSet G e ↔ x.val ∈ G.H := by
  constructor
  · rintro ⟨y, hy, hxy⟩
    exact he.injective hxy ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem ordinalSeparatedBandAmbientCoordinate_constant_on_ceilingCellAt
    (x y : ordinalSeparatedBandAmbientSet G e)
    (hy : y.val ∈ ordinalAmbientCeilingCellAt e a x.val) :
    ordinalSeparatedBandAmbientCoordinate G e he x = ordinalSeparatedBandAmbientCoordinate G e he y := by
  let r := (ordinalSeparatedBandAmbientHomeomorph G e he).symm
  let sx : Iic θ := ⟨(r x).val, ordinalSeparatedBandCoreGeometry_cell_subset G (r x).property⟩
  let sy : Iic θ := ⟨(r y).val, ordinalSeparatedBandCoreGeometry_cell_subset G (r y).property⟩
  have hsx : e sx = x.val := ordinalSeparatedBandAmbientHomeomorph_symm_apply_val G e he x
  have hsy : e sy = y.val := ordinalSeparatedBandAmbientHomeomorph_symm_apply_val G e he y
  obtain ⟨w, hw, t, ht, hty⟩ := hy
  have hwx : w = sx := he.injective (hw.trans hsx.symm)
  have hty' : t = sy := he.injective (hty.trans hsy.symm)
  subst w
  subst t
  change ordinalCeiling (ordinalTowerLevel θ a) sy.val =
    ordinalCeiling (ordinalTowerLevel θ a) sx.val at ht
  exact G.coordinate_constant (r x) (r y) ht.symm

end Posets


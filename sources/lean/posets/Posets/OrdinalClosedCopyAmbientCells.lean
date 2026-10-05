import Posets.OrdinalClosedCopyAmbientGeometry
import Posets.OrdinalAmbientCoreBandsRestriction

/-! The ambient coordinate is constant on each original lower ceiling
cell, with no inverse chosen outside the actual outer block. -/

noncomputable section
open Set Topology
universe u v
namespace Posets
open ThesisCommon

variable {F : Set Ordinal.{u}} {θ a b : Ordinal.{u}}
variable (G : OrdinalBandCoreGeometry F θ a b)
variable {K : Type v} [TopologicalSpace K] [T2Space K]
variable (e : Iic θ → K) (he : IsOpenEmbedding e)

include he in
omit [T2Space K] in
theorem ordinalBandAmbientSet_mem_iff (x : Iic θ) :
    e x ∈ ordinalBandAmbientSet G e ↔ x.val ∈ G.H := by
  constructor
  · rintro ⟨y, hy, hxy⟩
    exact he.injective hxy ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem ordinalBandAmbientCoordinate_constant_on_ceilingCellAt
    (x y : ordinalBandAmbientSet G e)
    (hy : y.val ∈ ordinalAmbientCeilingCellAt e a x.val) :
    ordinalBandAmbientCoordinate G e he x = ordinalBandAmbientCoordinate G e he y := by
  let r := (ordinalBandAmbientHomeomorph G e he).symm
  let sx : Iic θ := ⟨(r x).val, ordinalBandCoreGeometry_cell_subset G (r x).property⟩
  let sy : Iic θ := ⟨(r y).val, ordinalBandCoreGeometry_cell_subset G (r y).property⟩
  have hsx : e sx = x.val := ordinalBandAmbientHomeomorph_symm_apply_val G e he x
  have hsy : e sy = y.val := ordinalBandAmbientHomeomorph_symm_apply_val G e he y
  obtain ⟨w, hw, t, ht, hty⟩ := hy
  have hwx : w = sx := he.injective (hw.trans hsx.symm)
  have hty' : t = sy := he.injective (hty.trans hsy.symm)
  subst w
  subst t
  change ordinalCeiling (ordinalTowerLevel θ a) sy.val =
    ordinalCeiling (ordinalTowerLevel θ a) sx.val at ht
  exact G.coordinate_constant (r x) (r y) ht.symm

end Posets

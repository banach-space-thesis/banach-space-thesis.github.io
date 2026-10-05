import Posets.OrdinalClosedCopyBandGeometry
import Posets.CountableOrdinalPFPBandCells

/-! The selected geometric cell is exactly the original upper band cell
through any of its leaves.  Original lower band cells stay inside it and
the actual coordinate map is constant on each of them. -/

noncomputable section
open Set Topology
universe u
namespace Posets
open ThesisCommon

theorem ordinalBandCoreGeometry_upper_cell_eq
    {F : Set Ordinal.{u}} {θ a b γ : Ordinal.{u}}
    (G : OrdinalBandCoreGeometry F θ a b)
    (p : OrdinalTowerNode θ γ) (β : Iic γ) (hβ : β.val = a + b)
    (hp : p.point.val ∈ G.H) :
    (Subtype.val '' p.bandCell β : Set Ordinal.{u}) = G.H := by
  have hp' : ordinalCeiling (ordinalTowerLevel θ (a+b)) p.point.val = G.upperPoint.val := by
    rw [G.cell_eq] at hp
    exact hp.2
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [G.cell_eq]
    refine ⟨z.property, ?_⟩
    change ordinalCeiling (ordinalTowerLevel θ β.val) z.val =
      ordinalCeiling (ordinalTowerLevel θ β.val) p.point.val at hz
    rw [hβ] at hz
    exact hz.trans hp'
  · intro hx
    rw [G.cell_eq] at hx
    refine ⟨⟨x, hx.1⟩, ?_, rfl⟩
    change ordinalCeiling (ordinalTowerLevel θ β.val) x =
      ordinalCeiling (ordinalTowerLevel θ β.val) p.point.val
    rw [hβ]
    exact hx.2.trans hp'.symm

theorem ordinalBandCoreGeometry_lower_cell_subset
    {F : Set Ordinal.{u}} {θ a b γ : Ordinal.{u}}
    (G : OrdinalBandCoreGeometry F θ a b) (hθ : θ ∈ ordinalTowerLevel θ γ)
    (p : OrdinalTowerNode θ γ) (β δ : Iic γ)
    (hβ : β.val = a) (hδ : δ.val = a+b) (hp : p.point.val ∈ G.H) :
    (Subtype.val '' p.bandCell β : Set Ordinal.{u}) ⊆ G.H := by
  rw [← ordinalBandCoreGeometry_upper_cell_eq G p δ hδ hp]
  apply image_mono
  apply p.bandCell_monotone hθ
  change β.val ≤ δ.val
  rw [hβ, hδ]
  exact Ordinal.le_add_right _ _

theorem ordinalBandCoreGeometry_coordinate_constant_on_bandCell
    {F : Set Ordinal.{u}} {θ a b γ : Ordinal.{u}}
    (G : OrdinalBandCoreGeometry F θ a b)
    (p : OrdinalTowerNode θ γ) (β : Iic γ) (hβ : β.val = a)
    (x y : G.H)
    (hx : x.val ∈ (Subtype.val '' p.bandCell β : Set Ordinal.{u}))
    (hy : y.val ∈ (Subtype.val '' p.bandCell β : Set Ordinal.{u})) :
    G.p x = G.p y := by
  have hcell (z : G.H) (hz : z.val ∈ (Subtype.val '' p.bandCell β : Set Ordinal.{u})) :
      ordinalCeiling (ordinalTowerLevel θ a) z.val =
        ordinalCeiling (ordinalTowerLevel θ a) p.point.val := by
    obtain ⟨w, hw, he⟩ := hz
    rw [← he]
    change ordinalCeiling (ordinalTowerLevel θ β.val) w.val =
      ordinalCeiling (ordinalTowerLevel θ β.val) p.point.val at hw
    simpa only [hβ] using hw
  exact G.coordinate_constant x y ((hcell x hx).trans (hcell y hy).symm)

end Posets

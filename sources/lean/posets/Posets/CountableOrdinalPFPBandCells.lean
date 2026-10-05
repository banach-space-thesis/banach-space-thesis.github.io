import Posets.CountableOrdinalPFPAncestors
import Posets.CountableOrdinalPFPBands

/-! Ceiling fibers at prescribed band levels. Their definitions do not need
a rank assumption; their clopen and compact properties are used only for
nodes whose original rank is below the prescribed level. -/

noncomputable section
open Set Topology Order
universe u
namespace Posets
open ThesisCommon
namespace OrdinalTowerNode
variable {θ γ : Ordinal.{u}}

def bandCell (p : OrdinalTowerNode θ γ) (β : Iic γ) : Set (Iic θ) :=
  ordinalTowerCell θ (ordinalTowerLevel θ β) (ordinalCeiling (ordinalTowerLevel θ β) p.point)

theorem bandCell_eq_ancestor (hθ : θ ∈ ordinalTowerLevel θ γ)
    (p : OrdinalTowerNode θ γ) (β : Iic γ) (hpβ : p.level.val ≤ β.val) :
    p.bandCell β = (p.ancestor hθ β hpβ β.property).cell := rfl

theorem bandCell_isClopen (hθ : θ ∈ ordinalTowerLevel θ γ)
    (p : OrdinalTowerNode θ γ) (β : Iic γ) (hpβ : p.level.val ≤ β.val) :
    IsClopen (p.bandCell β) := (p.ancestor hθ β hpβ β.property).cell_isClopen

theorem bandCell_isCompact (hθ : θ ∈ ordinalTowerLevel θ γ)
    (p : OrdinalTowerNode θ γ) (β : Iic γ) (hpβ : p.level.val ≤ β.val) :
    IsCompact (p.bandCell β) := (p.ancestor hθ β hpβ β.property).cell_isCompact

theorem point_mem_bandCell (hθ : θ ∈ ordinalTowerLevel θ γ)
    (p : OrdinalTowerNode θ γ) (β : Iic γ) (hpβ : p.level.val ≤ β.val) :
    p.point ∈ p.bandCell β := p.cell_subset_ancestor hθ β hpβ β.property p.point_mem_cell

theorem bandCell_monotone (hθ : θ ∈ ordinalTowerLevel θ γ)
    (p : OrdinalTowerNode θ γ) : Monotone p.bandCell := by
  intro β δ hβδ z hz
  change ordinalCeiling (ordinalTowerLevel θ β) z.val =
    ordinalCeiling (ordinalTowerLevel θ β) p.point.val at hz
  change ordinalCeiling (ordinalTowerLevel θ δ) z.val =
    ordinalCeiling (ordinalTowerLevel θ δ) p.point.val
  have hc (x : Iic θ) := ordinalCeiling_comp_of_subset
    (ordinalTowerLevel_isCompact θ β) (ordinalTowerLevel_isCompact θ δ)
    (ordinalTowerLevel_antitone θ hβδ)
    ⟨θ, ordinalTowerLevel_antitone θ δ.property hθ⟩
    (x.property.trans (le_csSup (ordinalTowerLevel_isCompact θ δ).bddAbove
      (ordinalTowerLevel_antitone θ δ.property hθ)))
  rw [← hc z, hz, hc p.point]

theorem bandCell_eq_of_point_mem
    (p q : OrdinalTowerNode θ γ) (hp : p.point ∈ q.cell) :
    p.bandCell q.level = q.cell := by
  change ordinalCeiling (ordinalTowerLevel θ q.level.val) p.point.val = q.point.val at hp
  change ordinalTowerCell θ (ordinalTowerLevel θ q.level.val)
    (ordinalCeiling (ordinalTowerLevel θ q.level.val) p.point.val) = q.cell
  rw [hp]
  rfl

theorem bandCell_subset_of_point_mem (hθ : θ ∈ ordinalTowerLevel θ γ)
    (p q : OrdinalTowerNode θ γ) (β : Iic γ) (hβq : β.val ≤ q.level.val)
    (hp : p.point ∈ q.cell) : p.bandCell β ⊆ q.cell := by
  rw [← p.bandCell_eq_of_point_mem q hp]
  exact p.bandCell_monotone hθ hβq

end OrdinalTowerNode
end Posets

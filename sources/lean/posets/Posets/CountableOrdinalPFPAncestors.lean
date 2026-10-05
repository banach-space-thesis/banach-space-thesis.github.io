import Posets.CountableOrdinalPFPCanonicalNodes

/-! Every isolated node has a canonical ancestor at every higher level.
The ceiling coherence proves actual cell containment, including limit levels. -/

noncomputable section
open Set Topology Order
universe u
namespace Posets
open ThesisCommon

theorem ordinalCeiling_isolated_of_subset {A B : Set Ordinal.{u}}
    (hA : IsCompact A) (hne : A.Nonempty) (hAB : A ⊆ B)
    (p : B) (hp : IsOpen ({p} : Set B)) (hbound : p.val ≤ sSup A) :
    IsOpen ({⟨ordinalCeiling A p.val, ordinalCeiling_mem hA hne p.val⟩} : Set A) := by
  by_cases hpA : p.val ∈ A
  · let inc : A → B := fun a => ⟨a.val, hAB a.property⟩
    have hi : Continuous inc := continuous_subtype_val.subtype_mk _
    have heq : inc ⁻¹' {p} =
        {⟨ordinalCeiling A p.val, ordinalCeiling_mem hA hne p.val⟩} := by
      ext a
      simp only [mem_preimage, mem_singleton_iff, Subtype.ext_iff,
        ordinalCeiling_eq_of_mem hpA]
      rfl
    rw [← heq]
    exact hp.preimage hi
  · have hlt : p.val < ordinalCeiling A p.val := by
      apply lt_of_le_of_ne (le_ordinalCeiling hA hne hbound)
      intro h
      exact hpA (h ▸ ordinalCeiling_mem hA hne p.val)
    have heq : ordinalCeiling A (succ p.val) = ordinalCeiling A p.val := by
      apply le_antisymm
      · exact ordinalCeiling_le_of_mem (ordinalCeiling_mem hA hne p.val)
          (succ_le_iff.mpr hlt)
      · exact ordinalCeiling_mono hA hne (le_succ _)
    have ho := ordinalCeiling_isolated_of_isOpen_Ici hA hne
      ((succ_le_iff.mpr hlt).trans
        (le_csSup hA.bddAbove (ordinalCeiling_mem hA hne p.val)))
      (show IsOpen (Ici (succ p.val)) from by rw [Order.Ici_succ]; exact isOpen_Ioi)
    simpa only [heq] using ho

namespace OrdinalTowerNode
variable {θ γ : Ordinal.{u}}

def ancestor (hθ : θ ∈ ordinalTowerLevel θ γ) (p : OrdinalTowerNode θ γ)
    (β : Ordinal.{u}) (hpβ : p.level.val ≤ β) (hβγ : β ≤ γ) : OrdinalTowerNode θ γ where
  level := ⟨β, hβγ⟩
  point := ⟨ordinalCeiling (ordinalTowerLevel θ β) p.point.val,
    ordinalCeiling_le_of_mem (ordinalTowerLevel_antitone θ hβγ hθ) p.point.property⟩
  mem_level := ordinalCeiling_mem (ordinalTowerLevel_isCompact θ β)
    ⟨θ, ordinalTowerLevel_antitone θ hβγ hθ⟩ p.point.val
  isolated := ordinalCeiling_isolated_of_subset (ordinalTowerLevel_isCompact θ β)
    ⟨θ, ordinalTowerLevel_antitone θ hβγ hθ⟩ (ordinalTowerLevel_antitone θ hpβ)
    ⟨p.point.val, p.mem_level⟩ p.isolated
    (p.point.property.trans (le_csSup (ordinalTowerLevel_isCompact θ β).bddAbove
      (ordinalTowerLevel_antitone θ hβγ hθ)))

theorem cell_subset_ancestor (hθ : θ ∈ ordinalTowerLevel θ γ)
    (p : OrdinalTowerNode θ γ) (β : Ordinal.{u}) (hpβ : p.level.val ≤ β) (hβγ : β ≤ γ) :
    p.cell ⊆ (p.ancestor hθ β hpβ hβγ).cell := by
  intro z hz
  change ordinalCeiling (ordinalTowerLevel θ p.level.val) z.val = p.point.val at hz
  change ordinalCeiling (ordinalTowerLevel θ β) z.val =
    ordinalCeiling (ordinalTowerLevel θ β) p.point.val
  rw [← ordinalCeiling_comp_of_subset (ordinalTowerLevel_isCompact θ p.level)
    (ordinalTowerLevel_isCompact θ β) (ordinalTowerLevel_antitone θ hpβ)
    ⟨θ, ordinalTowerLevel_antitone θ hβγ hθ⟩
    (z.property.trans (le_csSup (ordinalTowerLevel_isCompact θ β).bddAbove
      (ordinalTowerLevel_antitone θ hβγ hθ))), hz]

theorem ancestor_cell_eq_of_mem (hθ : θ ∈ ordinalTowerLevel θ γ)
    (p q : OrdinalTowerNode θ γ) (hpq : p.level.val ≤ q.level.val)
    (hp : p.point ∈ q.cell) :
    (p.ancestor hθ q.level hpq q.level.property).cell = q.cell := by
  change ordinalCeiling (ordinalTowerLevel θ q.level.val) p.point.val = q.point.val at hp
  change ordinalTowerCell θ (ordinalTowerLevel θ q.level.val)
    (ordinalCeiling (ordinalTowerLevel θ q.level.val) p.point.val) =
      ordinalTowerCell θ (ordinalTowerLevel θ q.level.val) q.point.val
  rw [hp]

end OrdinalTowerNode
end Posets

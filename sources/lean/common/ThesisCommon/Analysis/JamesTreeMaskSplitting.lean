import ThesisCommon.Analysis.JamesTreeBranchTailMasks
import ThesisCommon.Analysis.JamesTreeLevelDecomposition

/-! A branch lying in a low-level head and one selected descendant cone
has its actual projection bounded by the two corresponding projections. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜] {p : BanachExponent} {S : JamesTreeSegmentFamily}

theorem jamesTreeMask_norm_le_of_cover
    (hS : ∀ N, JamesTreeMaskClosed S (dyadicInitialLevels N))
    (A L C : Set DyadicTreeNode)
    (hA : JamesTreeMaskClosed S A) (hL : JamesTreeMaskClosed S L)
    (hC : JamesTreeMaskClosed S C) (hLt : JamesTreeMaskClosed S Lᶜ)
    (hc : A ⊆ L ∪ C) (x : SegmentJamesTreeSpace 𝕜 p S) :
    ‖jamesTreeMask A hA x‖ ≤ ‖jamesTreeMask L hL x‖ + ‖jamesTreeMask C hC x‖ := by
  have hAt := jamesTreeMaskClosed_inter hA hLt
  have he : jamesTreeMask A hA x =
      jamesTreeMask A hA (jamesTreeMask L hL x) +
      jamesTreeMask (A ∩ Lᶜ) hAt (jamesTreeMask C hC x) := by
    apply jamesTreeCoordinate_ext hS
    intro t
    simp only [map_add, jamesTreeCoordinate_mask]
    by_cases ha : t ∈ A <;> by_cases hl : t ∈ L
    · have hat : t ∉ A ∩ Lᶜ := fun h => h.2 hl
      simp only [if_pos ha, if_pos hl, if_neg hat, add_zero]
    · have htC := (hc ha).resolve_left hl
      have hat : t ∈ A ∩ Lᶜ := ⟨ha,hl⟩
      simp only [if_pos ha, if_neg hl, if_pos htC, if_pos hat, zero_add]
    · have hat : t ∉ A ∩ Lᶜ := fun h => ha h.1
      simp only [if_neg ha, if_neg hat, add_zero]
    · have hat : t ∉ A ∩ Lᶜ := fun h => ha h.1
      simp only [if_neg ha, if_neg hat, add_zero]
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add (jamesTreeMask_norm_le A hA _)
    (jamesTreeMask_norm_le (A ∩ Lᶜ) hAt _))

end ThesisCommon

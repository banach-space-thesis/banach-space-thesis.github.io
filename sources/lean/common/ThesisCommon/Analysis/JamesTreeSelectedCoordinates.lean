import ThesisCommon.Analysis.JamesTreeSelectedCompletion
import ThesisCommon.Analysis.JamesTreeCoordinates

/-! All-vector coordinate identities for the selected-subtree maps. The
readback sums over the actual connecting cells, including their gap nodes. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜] {p : BanachExponent} {S : JamesTreeSegmentFamily}

theorem jamesTreeCoordinate_selectedRead (e : DyadicSubtreeEmbedding)
    (hS : JamesTreeSelectedClosure S e) (s : DyadicTreeNode)
    (x : SegmentJamesTreeSpace 𝕜 p S) :
    jamesTreeCoordinate s (jamesTreeSelectedRead e hS x) =
      ∑ t ∈ dyadicSelectedCell e s, jamesTreeCoordinate t x := by
  refine (jamesTreeDenseEmbedding_denseRange 𝕜 p S).induction_on x ?_ ?_
  · exact isClosed_eq
      ((jamesTreeCoordinate s).continuous.comp (jamesTreeSelectedRead e hS).continuous)
      (continuous_finset_sum _ (fun t _ => (jamesTreeCoordinate t).continuous))
  · intro a
    simp only [jamesTreeSelectedRead_dense, jamesTreeCoordinate_dense]
    exact JamesTreePreSpace.selectedReadLinear_apply e a s

@[simp] theorem jamesTreeCoordinate_selectedInsert_image (e : DyadicSubtreeEmbedding)
    (hS : JamesTreeSelectedClosure S e) (s : DyadicTreeNode)
    (x : SegmentJamesTreeSpace 𝕜 p S) :
    jamesTreeCoordinate (e s) (jamesTreeSelectedInsert e hS x) = jamesTreeCoordinate s x := by
  refine (jamesTreeDenseEmbedding_denseRange 𝕜 p S).induction_on x ?_ ?_
  · exact isClosed_eq
      ((jamesTreeCoordinate (e s)).continuous.comp (jamesTreeSelectedInsert e hS).continuous)
      (jamesTreeCoordinate s).continuous
  · intro a
    simp only [jamesTreeSelectedInsert_dense, jamesTreeCoordinate_dense,
      JamesTreePreSpace.selectedInsert_apply, JamesTreePreSpace.selectedInsertLinear_apply_image]

theorem jamesTreeCoordinate_selectedInsert_of_not_mem (e : DyadicSubtreeEmbedding)
    (hS : JamesTreeSelectedClosure S e) (t : DyadicTreeNode) (ht : t ∉ Set.range e)
    (x : SegmentJamesTreeSpace 𝕜 p S) :
    jamesTreeCoordinate t (jamesTreeSelectedInsert e hS x) = 0 := by
  refine (jamesTreeDenseEmbedding_denseRange 𝕜 p S).induction_on x ?_ ?_
  · exact isClosed_eq
      ((jamesTreeCoordinate t).continuous.comp (jamesTreeSelectedInsert e hS).continuous)
      continuous_const
  · intro a
    simp only [jamesTreeSelectedInsert_dense, jamesTreeCoordinate_dense,
      JamesTreePreSpace.selectedInsert_apply]
    exact JamesTreePreSpace.selectedInsertLinear_apply_of_not_mem e t a ht

@[simp] theorem jamesTreeSelectedInsert_unit (e : DyadicSubtreeEmbedding)
    (hS : JamesTreeSelectedClosure S e) (s : DyadicTreeNode) :
    jamesTreeSelectedInsert (𝕜 := 𝕜) (p := p) e hS (jamesTreeUnit s) =
      jamesTreeUnit (e s) := by
  rw [jamesTreeUnit, jamesTreeSelectedInsert_dense, jamesTreeUnit]
  apply congrArg (jamesTreeDenseEmbedding 𝕜 p S)
  exact Finsupp.mapDomain_single

theorem jamesTreeCoordinate_selectedProjection_image (e : DyadicSubtreeEmbedding)
    (hS : JamesTreeSelectedClosure S e) (s : DyadicTreeNode)
    (x : SegmentJamesTreeSpace 𝕜 p S) :
    jamesTreeCoordinate (e s) (jamesTreeSelectedProjection e hS x) =
      ∑ t ∈ dyadicSelectedCell e s, jamesTreeCoordinate t x := by
  rw [jamesTreeSelectedProjection, ContinuousLinearMap.comp_apply,
    jamesTreeCoordinate_selectedInsert_image, jamesTreeCoordinate_selectedRead]

theorem jamesTreeCoordinate_selectedProjection_of_not_mem (e : DyadicSubtreeEmbedding)
    (hS : JamesTreeSelectedClosure S e) (t : DyadicTreeNode) (ht : t ∉ Set.range e)
    (x : SegmentJamesTreeSpace 𝕜 p S) :
    jamesTreeCoordinate t (jamesTreeSelectedProjection e hS x) = 0 :=
  jamesTreeCoordinate_selectedInsert_of_not_mem e hS t ht (jamesTreeSelectedRead e hS x)

end ThesisCommon

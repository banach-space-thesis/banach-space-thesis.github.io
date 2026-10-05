import ThesisCommon.Analysis.JamesTreeDelayedCompletion
import ThesisCommon.Analysis.JamesTreeCoordinates

/-! All-vector coordinate identities for the selected-subtree maps. The
readback sums over the actual connecting cells, including their gap nodes. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜] {p : BanachExponent} {S : JamesTreeSegmentFamily}

theorem jamesTreeCoordinate_delayedRead (e : DyadicDelayedFork)
    (hS : JamesTreeDelayedForkClosure S e) (s : DyadicTreeNode)
    (x : SegmentJamesTreeSpace 𝕜 p S) :
    jamesTreeCoordinate s (jamesTreeDelayedRead e hS x) =
      ∑ t ∈ dyadicRootedCell e.fork s, jamesTreeCoordinate t x := by
  refine (jamesTreeDenseEmbedding_denseRange 𝕜 p S).induction_on x ?_ ?_
  · exact isClosed_eq
      ((jamesTreeCoordinate s).continuous.comp (jamesTreeDelayedRead e hS).continuous)
      (continuous_finset_sum _ (fun t _ => (jamesTreeCoordinate t).continuous))
  · intro a
    simp only [jamesTreeDelayedRead_dense, jamesTreeCoordinate_dense]
    exact JamesTreePreSpace.delayedReadLinear_apply e a s

@[simp] theorem jamesTreeCoordinate_delayedInsert_image (e : DyadicDelayedFork)
    (hS : JamesTreeDelayedForkClosure S e) (s : DyadicTreeNode)
    (x : SegmentJamesTreeSpace 𝕜 p S) :
    jamesTreeCoordinate (e.node s) (jamesTreeDelayedInsert e hS x) = jamesTreeCoordinate s x := by
  refine (jamesTreeDenseEmbedding_denseRange 𝕜 p S).induction_on x ?_ ?_
  · exact isClosed_eq
      ((jamesTreeCoordinate (e.node s)).continuous.comp (jamesTreeDelayedInsert e hS).continuous)
      (jamesTreeCoordinate s).continuous
  · intro a
    simp only [jamesTreeDelayedInsert_dense, jamesTreeCoordinate_dense,
      JamesTreePreSpace.delayedInsert_apply, JamesTreePreSpace.delayedInsertLinear_apply_image]

theorem jamesTreeCoordinate_delayedInsert_of_not_mem (e : DyadicDelayedFork)
    (hS : JamesTreeDelayedForkClosure S e) (t : DyadicTreeNode) (ht : t ∉ Set.range e.node)
    (x : SegmentJamesTreeSpace 𝕜 p S) :
    jamesTreeCoordinate t (jamesTreeDelayedInsert e hS x) = 0 := by
  refine (jamesTreeDenseEmbedding_denseRange 𝕜 p S).induction_on x ?_ ?_
  · exact isClosed_eq
      ((jamesTreeCoordinate t).continuous.comp (jamesTreeDelayedInsert e hS).continuous)
      continuous_const
  · intro a
    simp only [jamesTreeDelayedInsert_dense, jamesTreeCoordinate_dense,
      JamesTreePreSpace.delayedInsert_apply]
    exact JamesTreePreSpace.delayedInsertLinear_apply_of_not_mem e t a ht

@[simp] theorem jamesTreeDelayedInsert_unit (e : DyadicDelayedFork)
    (hS : JamesTreeDelayedForkClosure S e) (s : DyadicTreeNode) :
    jamesTreeDelayedInsert (𝕜 := 𝕜) (p := p) e hS (jamesTreeUnit s) =
      jamesTreeUnit (e.node s) := by
  rw [jamesTreeUnit, jamesTreeDelayedInsert_dense, jamesTreeUnit]
  apply congrArg (jamesTreeDenseEmbedding 𝕜 p S)
  exact Finsupp.mapDomain_single

theorem jamesTreeCoordinate_delayedProjection_image (e : DyadicDelayedFork)
    (hS : JamesTreeDelayedForkClosure S e) (s : DyadicTreeNode)
    (x : SegmentJamesTreeSpace 𝕜 p S) :
    jamesTreeCoordinate (e.node s) (jamesTreeDelayedProjection e hS x) =
      ∑ t ∈ dyadicRootedCell e.fork s, jamesTreeCoordinate t x := by
  rw [jamesTreeDelayedProjection, ContinuousLinearMap.comp_apply,
    jamesTreeCoordinate_delayedInsert_image, jamesTreeCoordinate_delayedRead]

theorem jamesTreeCoordinate_delayedProjection_of_not_mem (e : DyadicDelayedFork)
    (hS : JamesTreeDelayedForkClosure S e) (t : DyadicTreeNode) (ht : t ∉ Set.range e.node)
    (x : SegmentJamesTreeSpace 𝕜 p S) :
    jamesTreeCoordinate t (jamesTreeDelayedProjection e hS x) = 0 :=
  jamesTreeCoordinate_delayedInsert_of_not_mem e hS t ht (jamesTreeDelayedRead e hS x)

end ThesisCommon

import ThesisCommon.Analysis.JamesTreeMasks

/-! Actual bounded coordinates and normalized unit vectors on the completed
tree spaces. Both segment conventions are retained as explicit parameters. -/
noncomputable section
namespace ThesisCommon
attribute [local instance] Classical.propDecidable
variable {𝕜 : Type*} [RCLike 𝕜] {p : BanachExponent} {S : JamesTreeSegmentFamily}

def jamesTreeCoordinate (t : DyadicTreeNode) : SegmentJamesTreeSpace 𝕜 p S →L[𝕜] 𝕜 :=
  (JamesTreePreSpace.coordinate t).extend
    (jamesTreeDenseEmbedding 𝕜 p S).toContinuousLinearMap
    (jamesTreeDenseEmbedding_denseRange 𝕜 p S)
    (jamesTreeDenseEmbedding 𝕜 p S).isometry.isUniformInducing

@[simp] theorem jamesTreeCoordinate_dense (t : DyadicTreeNode)
    (a : JamesTreePreSpace 𝕜 p S) :
    jamesTreeCoordinate t (jamesTreeDenseEmbedding 𝕜 p S a) = a t :=
  ContinuousLinearMap.extend_eq _ _ _ _ a

def jamesTreeUnit (t : DyadicTreeNode) : SegmentJamesTreeSpace 𝕜 p S :=
  jamesTreeDenseEmbedding 𝕜 p S (JamesTreePreSpace.single t 1)

@[simp] theorem norm_jamesTreeUnit (t : DyadicTreeNode) :
    ‖jamesTreeUnit (𝕜 := 𝕜) (p := p) (S := S) t‖ = 1 := by
  simp only [jamesTreeUnit, jamesTreeDenseEmbedding_norm, JamesTreePreSpace.norm_single,
    norm_one]

@[simp] theorem jamesTreeCoordinate_unit (t u : DyadicTreeNode) :
    jamesTreeCoordinate (𝕜 := 𝕜) (p := p) (S := S) t (jamesTreeUnit u) =
      if t = u then 1 else 0 := by
  simp only [jamesTreeUnit, jamesTreeCoordinate_dense, JamesTreePreSpace.single_apply]
  by_cases h : t = u <;> simp [h, eq_comm]

theorem jamesTreeCoordinate_norm_le (t : DyadicTreeNode) (x : SegmentJamesTreeSpace 𝕜 p S) :
    ‖jamesTreeCoordinate t x‖ ≤ ‖x‖ := by
  refine (jamesTreeDenseEmbedding_denseRange 𝕜 p S).induction_on x ?_ ?_
  · exact isClosed_le (jamesTreeCoordinate t).continuous.norm continuous_norm
  · intro a
    rw [jamesTreeCoordinate_dense, jamesTreeDenseEmbedding_norm]
    exact JamesTreePreSpace.norm_apply_le a t

theorem norm_jamesTreeCoordinate (t : DyadicTreeNode) :
    ‖jamesTreeCoordinate (𝕜 := 𝕜) (p := p) (S := S) t‖ = 1 := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    simpa only [one_mul] using jamesTreeCoordinate_norm_le t x
  · have h := (jamesTreeCoordinate (𝕜 := 𝕜) (p := p) (S := S) t).le_opNorm
      (jamesTreeUnit t)
    simpa only [jamesTreeCoordinate_unit, ite_true, norm_one, norm_jamesTreeUnit,
      mul_one] using h

theorem jamesTreeCoordinate_mask (A : Set DyadicTreeNode) (hA : JamesTreeMaskClosed S A)
    (t : DyadicTreeNode) (x : SegmentJamesTreeSpace 𝕜 p S) :
    jamesTreeCoordinate t (jamesTreeMask A hA x) =
      if t ∈ A then jamesTreeCoordinate t x else 0 := by
  classical
  refine (jamesTreeDenseEmbedding_denseRange 𝕜 p S).induction_on x ?_ ?_
  · apply isClosed_eq ((jamesTreeCoordinate t).continuous.comp (jamesTreeMask A hA).continuous)
    by_cases ht : t ∈ A
    · simpa only [if_pos ht] using (jamesTreeCoordinate (𝕜 := 𝕜) (p := p) (S := S) t).continuous
    · simpa only [if_neg ht] using (continuous_const : Continuous (fun _ : SegmentJamesTreeSpace 𝕜 p S => (0 : 𝕜)))
  · intro a
    simp only [jamesTreeMask_dense, jamesTreeCoordinate_dense, JamesTreePreSpace.mask_apply]

end ThesisCommon

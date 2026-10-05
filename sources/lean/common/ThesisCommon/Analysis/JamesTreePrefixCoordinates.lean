import ThesisCommon.Analysis.JamesTreeConcretePrefixes

/-! Exact finite-coordinate action of the completed prefix projection. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜] {p : BanachExponent} {S : JamesTreeSegmentFamily}

theorem JamesTreePreSpace.prefixInsert_read_apply (u t : DyadicTreeNode)
    (a : JamesTreePreSpace 𝕜 p S) :
    JamesTreePreSpace.prefixInsertLinear u (JamesTreePreSpace.prefixReadLinear u a) t =
      if u.IsPrefix t then a t else 0 := by
  classical
  by_cases h : u.IsPrefix t
  · rw [if_pos h]
    obtain ⟨s, rfl⟩ := h
    rw [JamesTreePreSpace.prefixInsertLinear_apply_image, JamesTreePreSpace.prefixReadLinear_apply]
  · rw [if_neg h]
    exact JamesTreePreSpace.prefixInsertLinear_apply_of_not_prefix u t _ h

@[simp] theorem jamesTreePrefixProjection_dense (u : DyadicTreeNode)
    (hS : JamesTreePrefixClosure S u) (a : JamesTreePreSpace 𝕜 p S) :
    jamesTreePrefixProjection u hS (jamesTreeDenseEmbedding 𝕜 p S a) =
      jamesTreeDenseEmbedding 𝕜 p S
        (JamesTreePreSpace.prefixInsertLinear u (JamesTreePreSpace.prefixReadLinear u a)) := by
  simp only [jamesTreePrefixProjection, ContinuousLinearMap.comp_apply,
    jamesTreePrefixRead_dense, jamesTreePrefixInsert_dense,
    JamesTreePreSpace.prefixRead_apply, JamesTreePreSpace.prefixInsert_apply]

end ThesisCommon

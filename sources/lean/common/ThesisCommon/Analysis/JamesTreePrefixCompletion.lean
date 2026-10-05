import ThesisCommon.Analysis.JamesTreePrefixPreSpace
import Mathlib.Analysis.Normed.Operator.Completeness

/-! Actual prefix-subtree maps on the completed segment spaces. They extend
the finite-coordinate insertion and reading, are contractions, and have an
exact retraction identity. Their composition is a norm-one projection. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜] {p : BanachExponent} {S : JamesTreeSegmentFamily}

def jamesTreePrefixInsert (u : DyadicTreeNode) (hS : JamesTreePrefixClosure S u) :
    SegmentJamesTreeSpace 𝕜 p S →L[𝕜] SegmentJamesTreeSpace 𝕜 p S :=
  ((jamesTreeDenseEmbedding 𝕜 p S).toContinuousLinearMap.comp
    (JamesTreePreSpace.prefixInsert u hS)).extend
      (jamesTreeDenseEmbedding 𝕜 p S).toContinuousLinearMap
      (jamesTreeDenseEmbedding_denseRange 𝕜 p S)
      (jamesTreeDenseEmbedding 𝕜 p S).isometry.isUniformInducing

def jamesTreePrefixRead (u : DyadicTreeNode) (hS : JamesTreePrefixClosure S u) :
    SegmentJamesTreeSpace 𝕜 p S →L[𝕜] SegmentJamesTreeSpace 𝕜 p S :=
  ((jamesTreeDenseEmbedding 𝕜 p S).toContinuousLinearMap.comp
    (JamesTreePreSpace.prefixRead u hS.forward)).extend
      (jamesTreeDenseEmbedding 𝕜 p S).toContinuousLinearMap
      (jamesTreeDenseEmbedding_denseRange 𝕜 p S)
      (jamesTreeDenseEmbedding 𝕜 p S).isometry.isUniformInducing

@[simp] theorem jamesTreePrefixInsert_dense (u : DyadicTreeNode)
    (hS : JamesTreePrefixClosure S u) (a : JamesTreePreSpace 𝕜 p S) :
    jamesTreePrefixInsert u hS (jamesTreeDenseEmbedding 𝕜 p S a) =
      jamesTreeDenseEmbedding 𝕜 p S (JamesTreePreSpace.prefixInsert u hS a) :=
  ContinuousLinearMap.extend_eq _ _ _ _ a

@[simp] theorem jamesTreePrefixRead_dense (u : DyadicTreeNode)
    (hS : JamesTreePrefixClosure S u) (a : JamesTreePreSpace 𝕜 p S) :
    jamesTreePrefixRead u hS (jamesTreeDenseEmbedding 𝕜 p S a) =
      jamesTreeDenseEmbedding 𝕜 p S (JamesTreePreSpace.prefixRead u hS.forward a) :=
  ContinuousLinearMap.extend_eq _ _ _ _ a

theorem jamesTreePrefixInsert_norm_le (u : DyadicTreeNode) (hS : JamesTreePrefixClosure S u)
    (x : SegmentJamesTreeSpace 𝕜 p S) : ‖jamesTreePrefixInsert u hS x‖ ≤ ‖x‖ := by
  refine (jamesTreeDenseEmbedding_denseRange 𝕜 p S).induction_on x ?_ ?_
  · exact isClosed_le (jamesTreePrefixInsert u hS).continuous.norm continuous_norm
  · intro a
    rw [jamesTreePrefixInsert_dense, jamesTreeDenseEmbedding_norm, jamesTreeDenseEmbedding_norm]
    exact JamesTreePreSpace.prefixInsertLinear_norm_le u hS a

theorem jamesTreePrefixRead_norm_le (u : DyadicTreeNode) (hS : JamesTreePrefixClosure S u)
    (x : SegmentJamesTreeSpace 𝕜 p S) : ‖jamesTreePrefixRead u hS x‖ ≤ ‖x‖ := by
  refine (jamesTreeDenseEmbedding_denseRange 𝕜 p S).induction_on x ?_ ?_
  · exact isClosed_le (jamesTreePrefixRead u hS).continuous.norm continuous_norm
  · intro a
    rw [jamesTreePrefixRead_dense, jamesTreeDenseEmbedding_norm, jamesTreeDenseEmbedding_norm]
    exact JamesTreePreSpace.prefixReadLinear_norm_le u hS.forward a

theorem norm_jamesTreePrefixInsert_le (u : DyadicTreeNode) (hS : JamesTreePrefixClosure S u) :
    ‖jamesTreePrefixInsert (𝕜 := 𝕜) (p := p) u hS‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa only [one_mul] using jamesTreePrefixInsert_norm_le u hS x

theorem norm_jamesTreePrefixRead_le (u : DyadicTreeNode) (hS : JamesTreePrefixClosure S u) :
    ‖jamesTreePrefixRead (𝕜 := 𝕜) (p := p) u hS‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa only [one_mul] using jamesTreePrefixRead_norm_le u hS x

@[simp] theorem jamesTreePrefixRead_insert (u : DyadicTreeNode)
    (hS : JamesTreePrefixClosure S u) (x : SegmentJamesTreeSpace 𝕜 p S) :
    jamesTreePrefixRead u hS (jamesTreePrefixInsert u hS x) = x := by
  refine (jamesTreeDenseEmbedding_denseRange 𝕜 p S).induction_on x ?_ ?_
  · exact isClosed_eq
      ((jamesTreePrefixRead u hS).continuous.comp (jamesTreePrefixInsert u hS).continuous)
      continuous_id
  · intro a
    rw [jamesTreePrefixInsert_dense, jamesTreePrefixRead_dense]
    apply congrArg (jamesTreeDenseEmbedding 𝕜 p S)
    exact DFunLike.congr_fun (JamesTreePreSpace.prefixRead_comp_insert u hS) a

theorem jamesTreePrefixRead_comp_insert (u : DyadicTreeNode)
    (hS : JamesTreePrefixClosure S u) :
    (jamesTreePrefixRead (𝕜 := 𝕜) (p := p) u hS).comp (jamesTreePrefixInsert u hS) =
      ContinuousLinearMap.id 𝕜 _ :=
  ContinuousLinearMap.ext (jamesTreePrefixRead_insert u hS)

theorem jamesTreePrefixInsert_norm (u : DyadicTreeNode)
    (hS : JamesTreePrefixClosure S u) (x : SegmentJamesTreeSpace 𝕜 p S) :
    ‖jamesTreePrefixInsert u hS x‖ = ‖x‖ := by
  apply le_antisymm (jamesTreePrefixInsert_norm_le u hS x)
  simpa only [jamesTreePrefixRead_insert] using
    jamesTreePrefixRead_norm_le u hS (jamesTreePrefixInsert u hS x)

def jamesTreePrefixIsometry (u : DyadicTreeNode) (hS : JamesTreePrefixClosure S u) :
    SegmentJamesTreeSpace 𝕜 p S →ₗᵢ[𝕜] SegmentJamesTreeSpace 𝕜 p S :=
  { (jamesTreePrefixInsert u hS).toLinearMap with norm_map' := jamesTreePrefixInsert_norm u hS }

def jamesTreePrefixProjection (u : DyadicTreeNode) (hS : JamesTreePrefixClosure S u) :
    SegmentJamesTreeSpace 𝕜 p S →L[𝕜] SegmentJamesTreeSpace 𝕜 p S :=
  (jamesTreePrefixInsert u hS).comp (jamesTreePrefixRead u hS)

@[simp] theorem jamesTreePrefixProjection_insert (u : DyadicTreeNode)
    (hS : JamesTreePrefixClosure S u) (x : SegmentJamesTreeSpace 𝕜 p S) :
    jamesTreePrefixProjection u hS (jamesTreePrefixInsert u hS x) =
      jamesTreePrefixInsert u hS x := by
  simp only [jamesTreePrefixProjection, ContinuousLinearMap.comp_apply, jamesTreePrefixRead_insert]

theorem jamesTreePrefixProjection_idempotent (u : DyadicTreeNode)
    (hS : JamesTreePrefixClosure S u) :
    (jamesTreePrefixProjection (𝕜 := 𝕜) (p := p) u hS).comp
      (jamesTreePrefixProjection u hS) = jamesTreePrefixProjection u hS := by
  ext x
  exact jamesTreePrefixProjection_insert u hS (jamesTreePrefixRead u hS x)

theorem norm_jamesTreePrefixProjection_le (u : DyadicTreeNode)
    (hS : JamesTreePrefixClosure S u) :
    ‖jamesTreePrefixProjection (𝕜 := 𝕜) (p := p) u hS‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  exact (jamesTreePrefixInsert_norm_le u hS (jamesTreePrefixRead u hS x)).trans
    (by simpa only [one_mul] using jamesTreePrefixRead_norm_le u hS x)

theorem jamesTreePrefix_norms (u : DyadicTreeNode) (hS : JamesTreePrefixClosure S u) :
    ‖jamesTreePrefixInsert (𝕜 := 𝕜) (p := p) u hS‖ = 1 ∧
    ‖jamesTreePrefixRead (𝕜 := 𝕜) (p := p) u hS‖ = 1 ∧
    ‖jamesTreePrefixProjection (𝕜 := 𝕜) (p := p) u hS‖ = 1 := by
  let x : SegmentJamesTreeSpace 𝕜 p S :=
    jamesTreeDenseEmbedding 𝕜 p S (JamesTreePreSpace.single [] 1)
  have hx : ‖x‖ = 1 := by simp [x]
  have hix : ‖jamesTreePrefixInsert u hS x‖ = 1 := by rw [jamesTreePrefixInsert_norm, hx]
  have lower (T : SegmentJamesTreeSpace 𝕜 p S →L[𝕜] SegmentJamesTreeSpace 𝕜 p S)
      (y : SegmentJamesTreeSpace 𝕜 p S) (hy : ‖y‖ = 1) (hTy : ‖T y‖ = 1) : 1 ≤ ‖T‖ := by
    simpa only [hy, hTy, mul_one] using T.le_opNorm y
  refine ⟨le_antisymm (norm_jamesTreePrefixInsert_le u hS) (lower _ x hx hix),
    le_antisymm (norm_jamesTreePrefixRead_le u hS) ?_,
    le_antisymm (norm_jamesTreePrefixProjection_le u hS) ?_⟩
  · exact lower _ _ hix (by rw [jamesTreePrefixRead_insert, hx])
  · exact lower _ _ hix (by rw [jamesTreePrefixProjection_insert, hix])

theorem jamesTreePrefixProjection_range (u : DyadicTreeNode)
    (hS : JamesTreePrefixClosure S u) :
    LinearMap.range (jamesTreePrefixProjection (𝕜 := 𝕜) (p := p) u hS).toLinearMap =
      LinearMap.range (jamesTreePrefixInsert (𝕜 := 𝕜) (p := p) u hS).toLinearMap := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨jamesTreePrefixRead u hS x, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨jamesTreePrefixInsert u hS x, jamesTreePrefixProjection_insert u hS x⟩

end ThesisCommon

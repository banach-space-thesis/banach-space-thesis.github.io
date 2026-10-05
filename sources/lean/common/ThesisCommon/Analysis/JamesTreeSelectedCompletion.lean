import ThesisCommon.Analysis.JamesTreeSelectedPreSpace
import Mathlib.Analysis.Normed.Operator.Completeness

/-! Actual selected-subtree maps on the completed segment spaces. They extend
the finite-coordinate insertion and reading, are contractions, and have an
exact retraction identity. Their composition is a norm-one projection. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜] {p : BanachExponent} {S : JamesTreeSegmentFamily}

def jamesTreeSelectedInsert (e : DyadicSubtreeEmbedding) (hS : JamesTreeSelectedClosure S e) :
    SegmentJamesTreeSpace 𝕜 p S →L[𝕜] SegmentJamesTreeSpace 𝕜 p S :=
  ((jamesTreeDenseEmbedding 𝕜 p S).toContinuousLinearMap.comp
    (JamesTreePreSpace.selectedInsert e hS)).extend
      (jamesTreeDenseEmbedding 𝕜 p S).toContinuousLinearMap
      (jamesTreeDenseEmbedding_denseRange 𝕜 p S)
      (jamesTreeDenseEmbedding 𝕜 p S).isometry.isUniformInducing

def jamesTreeSelectedRead (e : DyadicSubtreeEmbedding) (hS : JamesTreeSelectedClosure S e) :
    SegmentJamesTreeSpace 𝕜 p S →L[𝕜] SegmentJamesTreeSpace 𝕜 p S :=
  ((jamesTreeDenseEmbedding 𝕜 p S).toContinuousLinearMap.comp
    (JamesTreePreSpace.selectedRead e hS.cells)).extend
      (jamesTreeDenseEmbedding 𝕜 p S).toContinuousLinearMap
      (jamesTreeDenseEmbedding_denseRange 𝕜 p S)
      (jamesTreeDenseEmbedding 𝕜 p S).isometry.isUniformInducing

@[simp] theorem jamesTreeSelectedInsert_dense (e : DyadicSubtreeEmbedding)
    (hS : JamesTreeSelectedClosure S e) (a : JamesTreePreSpace 𝕜 p S) :
    jamesTreeSelectedInsert e hS (jamesTreeDenseEmbedding 𝕜 p S a) =
      jamesTreeDenseEmbedding 𝕜 p S (JamesTreePreSpace.selectedInsert e hS a) :=
  ContinuousLinearMap.extend_eq _ _ _ _ a

@[simp] theorem jamesTreeSelectedRead_dense (e : DyadicSubtreeEmbedding)
    (hS : JamesTreeSelectedClosure S e) (a : JamesTreePreSpace 𝕜 p S) :
    jamesTreeSelectedRead e hS (jamesTreeDenseEmbedding 𝕜 p S a) =
      jamesTreeDenseEmbedding 𝕜 p S (JamesTreePreSpace.selectedRead e hS.cells a) :=
  ContinuousLinearMap.extend_eq _ _ _ _ a

theorem jamesTreeSelectedInsert_norm_le (e : DyadicSubtreeEmbedding) (hS : JamesTreeSelectedClosure S e)
    (x : SegmentJamesTreeSpace 𝕜 p S) : ‖jamesTreeSelectedInsert e hS x‖ ≤ ‖x‖ := by
  refine (jamesTreeDenseEmbedding_denseRange 𝕜 p S).induction_on x ?_ ?_
  · exact isClosed_le (jamesTreeSelectedInsert e hS).continuous.norm continuous_norm
  · intro a
    rw [jamesTreeSelectedInsert_dense, jamesTreeDenseEmbedding_norm, jamesTreeDenseEmbedding_norm]
    exact JamesTreePreSpace.selectedInsertLinear_norm_le e hS a

theorem jamesTreeSelectedRead_norm_le (e : DyadicSubtreeEmbedding) (hS : JamesTreeSelectedClosure S e)
    (x : SegmentJamesTreeSpace 𝕜 p S) : ‖jamesTreeSelectedRead e hS x‖ ≤ ‖x‖ := by
  refine (jamesTreeDenseEmbedding_denseRange 𝕜 p S).induction_on x ?_ ?_
  · exact isClosed_le (jamesTreeSelectedRead e hS).continuous.norm continuous_norm
  · intro a
    rw [jamesTreeSelectedRead_dense, jamesTreeDenseEmbedding_norm, jamesTreeDenseEmbedding_norm]
    exact JamesTreePreSpace.selectedReadLinear_norm_le e hS.cells a

theorem norm_jamesTreeSelectedInsert_le (e : DyadicSubtreeEmbedding) (hS : JamesTreeSelectedClosure S e) :
    ‖jamesTreeSelectedInsert (𝕜 := 𝕜) (p := p) e hS‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa only [one_mul] using jamesTreeSelectedInsert_norm_le e hS x

theorem norm_jamesTreeSelectedRead_le (e : DyadicSubtreeEmbedding) (hS : JamesTreeSelectedClosure S e) :
    ‖jamesTreeSelectedRead (𝕜 := 𝕜) (p := p) e hS‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa only [one_mul] using jamesTreeSelectedRead_norm_le e hS x

@[simp] theorem jamesTreeSelectedRead_insert (e : DyadicSubtreeEmbedding)
    (hS : JamesTreeSelectedClosure S e) (x : SegmentJamesTreeSpace 𝕜 p S) :
    jamesTreeSelectedRead e hS (jamesTreeSelectedInsert e hS x) = x := by
  refine (jamesTreeDenseEmbedding_denseRange 𝕜 p S).induction_on x ?_ ?_
  · exact isClosed_eq
      ((jamesTreeSelectedRead e hS).continuous.comp (jamesTreeSelectedInsert e hS).continuous)
      continuous_id
  · intro a
    rw [jamesTreeSelectedInsert_dense, jamesTreeSelectedRead_dense]
    apply congrArg (jamesTreeDenseEmbedding 𝕜 p S)
    exact DFunLike.congr_fun (JamesTreePreSpace.selectedRead_comp_insert e hS) a

theorem jamesTreeSelectedRead_comp_insert (e : DyadicSubtreeEmbedding)
    (hS : JamesTreeSelectedClosure S e) :
    (jamesTreeSelectedRead (𝕜 := 𝕜) (p := p) e hS).comp (jamesTreeSelectedInsert e hS) =
      ContinuousLinearMap.id 𝕜 _ :=
  ContinuousLinearMap.ext (jamesTreeSelectedRead_insert e hS)

theorem jamesTreeSelectedInsert_norm (e : DyadicSubtreeEmbedding)
    (hS : JamesTreeSelectedClosure S e) (x : SegmentJamesTreeSpace 𝕜 p S) :
    ‖jamesTreeSelectedInsert e hS x‖ = ‖x‖ := by
  apply le_antisymm (jamesTreeSelectedInsert_norm_le e hS x)
  simpa only [jamesTreeSelectedRead_insert] using
    jamesTreeSelectedRead_norm_le e hS (jamesTreeSelectedInsert e hS x)

def jamesTreeSelectedIsometry (e : DyadicSubtreeEmbedding) (hS : JamesTreeSelectedClosure S e) :
    SegmentJamesTreeSpace 𝕜 p S →ₗᵢ[𝕜] SegmentJamesTreeSpace 𝕜 p S :=
  { (jamesTreeSelectedInsert e hS).toLinearMap with norm_map' := jamesTreeSelectedInsert_norm e hS }

def jamesTreeSelectedProjection (e : DyadicSubtreeEmbedding) (hS : JamesTreeSelectedClosure S e) :
    SegmentJamesTreeSpace 𝕜 p S →L[𝕜] SegmentJamesTreeSpace 𝕜 p S :=
  (jamesTreeSelectedInsert e hS).comp (jamesTreeSelectedRead e hS)

@[simp] theorem jamesTreeSelectedProjection_insert (e : DyadicSubtreeEmbedding)
    (hS : JamesTreeSelectedClosure S e) (x : SegmentJamesTreeSpace 𝕜 p S) :
    jamesTreeSelectedProjection e hS (jamesTreeSelectedInsert e hS x) =
      jamesTreeSelectedInsert e hS x := by
  simp only [jamesTreeSelectedProjection, ContinuousLinearMap.comp_apply, jamesTreeSelectedRead_insert]

theorem jamesTreeSelectedProjection_idempotent (e : DyadicSubtreeEmbedding)
    (hS : JamesTreeSelectedClosure S e) :
    (jamesTreeSelectedProjection (𝕜 := 𝕜) (p := p) e hS).comp
      (jamesTreeSelectedProjection e hS) = jamesTreeSelectedProjection e hS := by
  ext x
  exact jamesTreeSelectedProjection_insert e hS (jamesTreeSelectedRead e hS x)

theorem norm_jamesTreeSelectedProjection_le (e : DyadicSubtreeEmbedding)
    (hS : JamesTreeSelectedClosure S e) :
    ‖jamesTreeSelectedProjection (𝕜 := 𝕜) (p := p) e hS‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  exact (jamesTreeSelectedInsert_norm_le e hS (jamesTreeSelectedRead e hS x)).trans
    (by simpa only [one_mul] using jamesTreeSelectedRead_norm_le e hS x)

theorem jamesTreeSelected_norms (e : DyadicSubtreeEmbedding) (hS : JamesTreeSelectedClosure S e) :
    ‖jamesTreeSelectedInsert (𝕜 := 𝕜) (p := p) e hS‖ = 1 ∧
    ‖jamesTreeSelectedRead (𝕜 := 𝕜) (p := p) e hS‖ = 1 ∧
    ‖jamesTreeSelectedProjection (𝕜 := 𝕜) (p := p) e hS‖ = 1 := by
  let x : SegmentJamesTreeSpace 𝕜 p S :=
    jamesTreeDenseEmbedding 𝕜 p S (JamesTreePreSpace.single [] 1)
  have hx : ‖x‖ = 1 := by simp [x]
  have hix : ‖jamesTreeSelectedInsert e hS x‖ = 1 := by rw [jamesTreeSelectedInsert_norm, hx]
  have lower (T : SegmentJamesTreeSpace 𝕜 p S →L[𝕜] SegmentJamesTreeSpace 𝕜 p S)
      (y : SegmentJamesTreeSpace 𝕜 p S) (hy : ‖y‖ = 1) (hTy : ‖T y‖ = 1) : 1 ≤ ‖T‖ := by
    simpa only [hy, hTy, mul_one] using T.le_opNorm y
  refine ⟨le_antisymm (norm_jamesTreeSelectedInsert_le e hS) (lower _ x hx hix),
    le_antisymm (norm_jamesTreeSelectedRead_le e hS) ?_,
    le_antisymm (norm_jamesTreeSelectedProjection_le e hS) ?_⟩
  · exact lower _ _ hix (by rw [jamesTreeSelectedRead_insert, hx])
  · exact lower _ _ hix (by rw [jamesTreeSelectedProjection_insert, hix])

theorem jamesTreeSelectedProjection_range (e : DyadicSubtreeEmbedding)
    (hS : JamesTreeSelectedClosure S e) :
    LinearMap.range (jamesTreeSelectedProjection (𝕜 := 𝕜) (p := p) e hS).toLinearMap =
      LinearMap.range (jamesTreeSelectedInsert (𝕜 := 𝕜) (p := p) e hS).toLinearMap := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨jamesTreeSelectedRead e hS x, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨jamesTreeSelectedInsert e hS x, jamesTreeSelectedProjection_insert e hS x⟩

end ThesisCommon

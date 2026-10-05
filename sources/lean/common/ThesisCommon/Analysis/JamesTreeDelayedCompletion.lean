import ThesisCommon.Analysis.JamesTreeDelayedPreSpace
import Mathlib.Analysis.Normed.Operator.Completeness

/-! Actual selected-subtree maps on the completed segment spaces. They extend
the finite-coordinate insertion and reading, are contractions, and have an
exact retraction identity. Their composition is a norm-one projection. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜] {p : BanachExponent} {S : JamesTreeSegmentFamily}

def jamesTreeDelayedInsert (e : DyadicDelayedFork) (hS : JamesTreeDelayedForkClosure S e) :
    SegmentJamesTreeSpace 𝕜 p S →L[𝕜] SegmentJamesTreeSpace 𝕜 p S :=
  ((jamesTreeDenseEmbedding 𝕜 p S).toContinuousLinearMap.comp
    (JamesTreePreSpace.delayedInsert e hS)).extend
      (jamesTreeDenseEmbedding 𝕜 p S).toContinuousLinearMap
      (jamesTreeDenseEmbedding_denseRange 𝕜 p S)
      (jamesTreeDenseEmbedding 𝕜 p S).isometry.isUniformInducing

def jamesTreeDelayedRead (e : DyadicDelayedFork) (hS : JamesTreeDelayedForkClosure S e) :
    SegmentJamesTreeSpace 𝕜 p S →L[𝕜] SegmentJamesTreeSpace 𝕜 p S :=
  ((jamesTreeDenseEmbedding 𝕜 p S).toContinuousLinearMap.comp
    (JamesTreePreSpace.delayedRead e hS.cells)).extend
      (jamesTreeDenseEmbedding 𝕜 p S).toContinuousLinearMap
      (jamesTreeDenseEmbedding_denseRange 𝕜 p S)
      (jamesTreeDenseEmbedding 𝕜 p S).isometry.isUniformInducing

@[simp] theorem jamesTreeDelayedInsert_dense (e : DyadicDelayedFork)
    (hS : JamesTreeDelayedForkClosure S e) (a : JamesTreePreSpace 𝕜 p S) :
    jamesTreeDelayedInsert e hS (jamesTreeDenseEmbedding 𝕜 p S a) =
      jamesTreeDenseEmbedding 𝕜 p S (JamesTreePreSpace.delayedInsert e hS a) :=
  ContinuousLinearMap.extend_eq _ _ _ _ a

@[simp] theorem jamesTreeDelayedRead_dense (e : DyadicDelayedFork)
    (hS : JamesTreeDelayedForkClosure S e) (a : JamesTreePreSpace 𝕜 p S) :
    jamesTreeDelayedRead e hS (jamesTreeDenseEmbedding 𝕜 p S a) =
      jamesTreeDenseEmbedding 𝕜 p S (JamesTreePreSpace.delayedRead e hS.cells a) :=
  ContinuousLinearMap.extend_eq _ _ _ _ a

theorem jamesTreeDelayedInsert_norm_le (e : DyadicDelayedFork) (hS : JamesTreeDelayedForkClosure S e)
    (x : SegmentJamesTreeSpace 𝕜 p S) : ‖jamesTreeDelayedInsert e hS x‖ ≤ ‖x‖ := by
  refine (jamesTreeDenseEmbedding_denseRange 𝕜 p S).induction_on x ?_ ?_
  · exact isClosed_le (jamesTreeDelayedInsert e hS).continuous.norm continuous_norm
  · intro a
    rw [jamesTreeDelayedInsert_dense, jamesTreeDenseEmbedding_norm, jamesTreeDenseEmbedding_norm]
    exact JamesTreePreSpace.delayedInsertLinear_norm_le e hS a

theorem jamesTreeDelayedRead_norm_le (e : DyadicDelayedFork) (hS : JamesTreeDelayedForkClosure S e)
    (x : SegmentJamesTreeSpace 𝕜 p S) : ‖jamesTreeDelayedRead e hS x‖ ≤ ‖x‖ := by
  refine (jamesTreeDenseEmbedding_denseRange 𝕜 p S).induction_on x ?_ ?_
  · exact isClosed_le (jamesTreeDelayedRead e hS).continuous.norm continuous_norm
  · intro a
    rw [jamesTreeDelayedRead_dense, jamesTreeDenseEmbedding_norm, jamesTreeDenseEmbedding_norm]
    exact JamesTreePreSpace.delayedReadLinear_norm_le e hS.cells a

theorem norm_jamesTreeDelayedInsert_le (e : DyadicDelayedFork) (hS : JamesTreeDelayedForkClosure S e) :
    ‖jamesTreeDelayedInsert (𝕜 := 𝕜) (p := p) e hS‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa only [one_mul] using jamesTreeDelayedInsert_norm_le e hS x

theorem norm_jamesTreeDelayedRead_le (e : DyadicDelayedFork) (hS : JamesTreeDelayedForkClosure S e) :
    ‖jamesTreeDelayedRead (𝕜 := 𝕜) (p := p) e hS‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa only [one_mul] using jamesTreeDelayedRead_norm_le e hS x

@[simp] theorem jamesTreeDelayedRead_insert (e : DyadicDelayedFork)
    (hS : JamesTreeDelayedForkClosure S e) (x : SegmentJamesTreeSpace 𝕜 p S) :
    jamesTreeDelayedRead e hS (jamesTreeDelayedInsert e hS x) = x := by
  refine (jamesTreeDenseEmbedding_denseRange 𝕜 p S).induction_on x ?_ ?_
  · exact isClosed_eq
      ((jamesTreeDelayedRead e hS).continuous.comp (jamesTreeDelayedInsert e hS).continuous)
      continuous_id
  · intro a
    rw [jamesTreeDelayedInsert_dense, jamesTreeDelayedRead_dense]
    apply congrArg (jamesTreeDenseEmbedding 𝕜 p S)
    exact DFunLike.congr_fun (JamesTreePreSpace.delayedRead_comp_insert e hS) a

theorem jamesTreeDelayedRead_comp_insert (e : DyadicDelayedFork)
    (hS : JamesTreeDelayedForkClosure S e) :
    (jamesTreeDelayedRead (𝕜 := 𝕜) (p := p) e hS).comp (jamesTreeDelayedInsert e hS) =
      ContinuousLinearMap.id 𝕜 _ :=
  ContinuousLinearMap.ext (jamesTreeDelayedRead_insert e hS)

theorem jamesTreeDelayedInsert_norm (e : DyadicDelayedFork)
    (hS : JamesTreeDelayedForkClosure S e) (x : SegmentJamesTreeSpace 𝕜 p S) :
    ‖jamesTreeDelayedInsert e hS x‖ = ‖x‖ := by
  apply le_antisymm (jamesTreeDelayedInsert_norm_le e hS x)
  simpa only [jamesTreeDelayedRead_insert] using
    jamesTreeDelayedRead_norm_le e hS (jamesTreeDelayedInsert e hS x)

def jamesTreeDelayedIsometry (e : DyadicDelayedFork) (hS : JamesTreeDelayedForkClosure S e) :
    SegmentJamesTreeSpace 𝕜 p S →ₗᵢ[𝕜] SegmentJamesTreeSpace 𝕜 p S :=
  { (jamesTreeDelayedInsert e hS).toLinearMap with norm_map' := jamesTreeDelayedInsert_norm e hS }

def jamesTreeDelayedProjection (e : DyadicDelayedFork) (hS : JamesTreeDelayedForkClosure S e) :
    SegmentJamesTreeSpace 𝕜 p S →L[𝕜] SegmentJamesTreeSpace 𝕜 p S :=
  (jamesTreeDelayedInsert e hS).comp (jamesTreeDelayedRead e hS)

@[simp] theorem jamesTreeDelayedProjection_insert (e : DyadicDelayedFork)
    (hS : JamesTreeDelayedForkClosure S e) (x : SegmentJamesTreeSpace 𝕜 p S) :
    jamesTreeDelayedProjection e hS (jamesTreeDelayedInsert e hS x) =
      jamesTreeDelayedInsert e hS x := by
  simp only [jamesTreeDelayedProjection, ContinuousLinearMap.comp_apply, jamesTreeDelayedRead_insert]

theorem jamesTreeDelayedProjection_idempotent (e : DyadicDelayedFork)
    (hS : JamesTreeDelayedForkClosure S e) :
    (jamesTreeDelayedProjection (𝕜 := 𝕜) (p := p) e hS).comp
      (jamesTreeDelayedProjection e hS) = jamesTreeDelayedProjection e hS := by
  ext x
  exact jamesTreeDelayedProjection_insert e hS (jamesTreeDelayedRead e hS x)

theorem norm_jamesTreeDelayedProjection_le (e : DyadicDelayedFork)
    (hS : JamesTreeDelayedForkClosure S e) :
    ‖jamesTreeDelayedProjection (𝕜 := 𝕜) (p := p) e hS‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  exact (jamesTreeDelayedInsert_norm_le e hS (jamesTreeDelayedRead e hS x)).trans
    (by simpa only [one_mul] using jamesTreeDelayedRead_norm_le e hS x)

theorem jamesTreeDelayed_norms (e : DyadicDelayedFork) (hS : JamesTreeDelayedForkClosure S e) :
    ‖jamesTreeDelayedInsert (𝕜 := 𝕜) (p := p) e hS‖ = 1 ∧
    ‖jamesTreeDelayedRead (𝕜 := 𝕜) (p := p) e hS‖ = 1 ∧
    ‖jamesTreeDelayedProjection (𝕜 := 𝕜) (p := p) e hS‖ = 1 := by
  let x : SegmentJamesTreeSpace 𝕜 p S :=
    jamesTreeDenseEmbedding 𝕜 p S (JamesTreePreSpace.single [] 1)
  have hx : ‖x‖ = 1 := by simp [x]
  have hix : ‖jamesTreeDelayedInsert e hS x‖ = 1 := by rw [jamesTreeDelayedInsert_norm, hx]
  have lower (T : SegmentJamesTreeSpace 𝕜 p S →L[𝕜] SegmentJamesTreeSpace 𝕜 p S)
      (y : SegmentJamesTreeSpace 𝕜 p S) (hy : ‖y‖ = 1) (hTy : ‖T y‖ = 1) : 1 ≤ ‖T‖ := by
    simpa only [hy, hTy, mul_one] using T.le_opNorm y
  refine ⟨le_antisymm (norm_jamesTreeDelayedInsert_le e hS) (lower _ x hx hix),
    le_antisymm (norm_jamesTreeDelayedRead_le e hS) ?_,
    le_antisymm (norm_jamesTreeDelayedProjection_le e hS) ?_⟩
  · exact lower _ _ hix (by rw [jamesTreeDelayedRead_insert, hx])
  · exact lower _ _ hix (by rw [jamesTreeDelayedProjection_insert, hix])

theorem jamesTreeDelayedProjection_range (e : DyadicDelayedFork)
    (hS : JamesTreeDelayedForkClosure S e) :
    LinearMap.range (jamesTreeDelayedProjection (𝕜 := 𝕜) (p := p) e hS).toLinearMap =
      LinearMap.range (jamesTreeDelayedInsert (𝕜 := 𝕜) (p := p) e hS).toLinearMap := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨jamesTreeDelayedRead e hS x, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨jamesTreeDelayedInsert e hS x, jamesTreeDelayedProjection_insert e hS x⟩

end ThesisCommon

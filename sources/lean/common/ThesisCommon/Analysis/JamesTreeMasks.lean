import ThesisCommon.Analysis.JamesTreePartialTests
import ThesisCommon.Analysis.JamesTreeSpace
import Mathlib.Analysis.Normed.Operator.Completeness

/-! Genuine contractive coordinate masks whenever intersections preserve
the chosen segments. The hypothesis is combinatorial and is discharged
for level truncations in a separate module. -/
noncomputable section
namespace ThesisCommon
attribute [local instance] Classical.propDecidable

def JamesTreeMaskClosed (S : JamesTreeSegmentFamily) (A : Set DyadicTreeNode) : Prop :=
  ∀ B, S.allows B → (B.filter (· ∈ A)).Nonempty → S.allows (B.filter (· ∈ A))

namespace JamesTreePreSpace
variable {𝕜 : Type*} [RCLike 𝕜] {p : BanachExponent} {S : JamesTreeSegmentFamily}

def maskLinear (A : Set DyadicTreeNode) :
    JamesTreePreSpace 𝕜 p S →ₗ[𝕜] JamesTreePreSpace 𝕜 p S where
  toFun a := Finsupp.filter (· ∈ A) a
  map_add' a b := by
    apply ext
    intro t
    change (if t ∈ A then a t + b t else 0) =
      (if t ∈ A then a t else 0) + (if t ∈ A then b t else 0)
    split_ifs <;> simp
  map_smul' c a := by
    apply ext
    intro t
    change (if t ∈ A then c • a t else 0) = c • (if t ∈ A then a t else 0)
    split_ifs <;> simp

@[simp] theorem maskLinear_apply (A : Set DyadicTreeNode)
    (a : JamesTreePreSpace 𝕜 p S) (t : DyadicTreeNode) :
    maskLinear A a t = if t ∈ A then a t else 0 := rfl

theorem maskLinear_norm_le (A : Set DyadicTreeNode) (hA : JamesTreeMaskClosed S A)
    (a : JamesTreePreSpace 𝕜 p S) : ‖maskLinear A a‖ ≤ ‖a‖ := by
  classical
  apply norm_le
  intro T
  have heq : jamesTreeTestMap 𝕜 p T (coefficients (maskLinear A a)) =
      WithLp.toLp p.val (fun j => ∑ t ∈ (T.segment j).filter (· ∈ A), a t) := by
    ext j
    change (∑ t ∈ T.segment j, if t ∈ A then a t else 0) =
      ∑ t ∈ (T.segment j).filter (· ∈ A), a t
    rw [Finset.sum_filter]
  rw [heq]
  apply jamesTree_partial_test_norm_le p a
  · intro j hj
    exact hA _ (T.allowed j) hj
  · intro i j hij
    exact (T.disjoint hij).mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)

def mask (A : Set DyadicTreeNode) (hA : JamesTreeMaskClosed S A) :
    JamesTreePreSpace 𝕜 p S →L[𝕜] JamesTreePreSpace 𝕜 p S :=
  (maskLinear A).mkContinuous 1 (fun a => by simpa using maskLinear_norm_le A hA a)

@[simp] theorem mask_apply (A : Set DyadicTreeNode) (hA : JamesTreeMaskClosed S A)
    (a : JamesTreePreSpace 𝕜 p S) (t : DyadicTreeNode) :
    mask A hA a t = if t ∈ A then a t else 0 := rfl

theorem mask_idempotent (A : Set DyadicTreeNode) (hA : JamesTreeMaskClosed S A)
    (a : JamesTreePreSpace 𝕜 p S) : mask A hA (mask A hA a) = mask A hA a := by
  ext t
  by_cases ht : t ∈ A <;> simp only [mask_apply, ht, ite_true, ite_false]

end JamesTreePreSpace
variable {𝕜 : Type*} [RCLike 𝕜] {p : BanachExponent} {S : JamesTreeSegmentFamily}

def jamesTreeMask (A : Set DyadicTreeNode) (hA : JamesTreeMaskClosed S A) :
    SegmentJamesTreeSpace 𝕜 p S →L[𝕜] SegmentJamesTreeSpace 𝕜 p S :=
  ((jamesTreeDenseEmbedding 𝕜 p S).toContinuousLinearMap.comp
    (JamesTreePreSpace.mask A hA)).extend
      (jamesTreeDenseEmbedding 𝕜 p S).toContinuousLinearMap
      (jamesTreeDenseEmbedding_denseRange 𝕜 p S)
      (jamesTreeDenseEmbedding 𝕜 p S).isometry.isUniformInducing

@[simp] theorem jamesTreeMask_dense (A : Set DyadicTreeNode)
    (hA : JamesTreeMaskClosed S A) (a : JamesTreePreSpace 𝕜 p S) :
    jamesTreeMask A hA (jamesTreeDenseEmbedding 𝕜 p S a) =
      jamesTreeDenseEmbedding 𝕜 p S (JamesTreePreSpace.mask A hA a) :=
  ContinuousLinearMap.extend_eq _ _ _ _ a

theorem jamesTreeMask_norm_le (A : Set DyadicTreeNode) (hA : JamesTreeMaskClosed S A)
    (x : SegmentJamesTreeSpace 𝕜 p S) : ‖jamesTreeMask A hA x‖ ≤ ‖x‖ := by
  refine (jamesTreeDenseEmbedding_denseRange 𝕜 p S).induction_on x ?_ ?_
  · exact isClosed_le (jamesTreeMask A hA).continuous.norm continuous_norm
  · intro a
    rw [jamesTreeMask_dense, jamesTreeDenseEmbedding_norm, jamesTreeDenseEmbedding_norm]
    exact JamesTreePreSpace.maskLinear_norm_le A hA a

theorem norm_jamesTreeMask_le (A : Set DyadicTreeNode) (hA : JamesTreeMaskClosed S A) :
    ‖jamesTreeMask (𝕜 := 𝕜) (p := p) A hA‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa only [one_mul] using jamesTreeMask_norm_le A hA x

theorem jamesTreeMask_idempotent (A : Set DyadicTreeNode)
    (hA : JamesTreeMaskClosed S A) (x : SegmentJamesTreeSpace 𝕜 p S) :
    jamesTreeMask A hA (jamesTreeMask A hA x) = jamesTreeMask A hA x := by
  refine (jamesTreeDenseEmbedding_denseRange 𝕜 p S).induction_on x ?_ ?_
  · exact isClosed_eq ((jamesTreeMask A hA).continuous.comp (jamesTreeMask A hA).continuous)
      (jamesTreeMask A hA).continuous
  · intro a
    simp only [jamesTreeMask_dense, JamesTreePreSpace.mask_idempotent]

end ThesisCommon

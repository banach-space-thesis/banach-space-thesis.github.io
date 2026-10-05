import ThesisCommon.Analysis.JamesTreeMultiplierEstimates
import ThesisCommon.Analysis.JamesTreeCoordinates

/-! Actual completed James-tree scalar multipliers from finite-chain bounds.
The inverse identities below hold on every completed vector. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜] {p : BanachExponent} {S : JamesTreeSegmentFamily}

def JamesTreeCoefficientBound (S : JamesTreeSegmentFamily) (d : DyadicTreeNode → 𝕜)
    (C : ℝ) : Prop :=
  ∀ A, S.allows A → ∃ c : 𝕜, ‖c‖ + ∑ t ∈ A, ‖d t-c‖ ≤ C

namespace JamesTreePreSpace
def multiplier (hp : 0 < p.val.toReal)
    (hS : ∀ A, S.allows A → JamesTreeMaskClosed S (A : Set DyadicTreeNode))
    (d : DyadicTreeNode → 𝕜) {C : ℝ} (hC : 0 ≤ C) (hd : JamesTreeCoefficientBound S d C) :
    JamesTreePreSpace 𝕜 p S →L[𝕜] JamesTreePreSpace 𝕜 p S :=
  (multiplierLinear d).mkContinuous C (multiplierLinear_norm_le hp hS d hC hd)
end JamesTreePreSpace

def jamesTreeMultiplier (hp : 0 < p.val.toReal)
    (hS : ∀ A, S.allows A → JamesTreeMaskClosed S (A : Set DyadicTreeNode))
    (d : DyadicTreeNode → 𝕜) {C : ℝ} (hC : 0 ≤ C) (hd : JamesTreeCoefficientBound S d C) :
    SegmentJamesTreeSpace 𝕜 p S →L[𝕜] SegmentJamesTreeSpace 𝕜 p S :=
  ((jamesTreeDenseEmbedding 𝕜 p S).toContinuousLinearMap.comp
    (JamesTreePreSpace.multiplier hp hS d hC hd)).extend
      (jamesTreeDenseEmbedding 𝕜 p S).toContinuousLinearMap
      (jamesTreeDenseEmbedding_denseRange 𝕜 p S)
      (jamesTreeDenseEmbedding 𝕜 p S).isometry.isUniformInducing

@[simp] theorem jamesTreeMultiplier_dense (hp : 0 < p.val.toReal)
    (hS : ∀ A, S.allows A → JamesTreeMaskClosed S (A : Set DyadicTreeNode))
    (d : DyadicTreeNode → 𝕜) {C : ℝ} (hC : 0 ≤ C) (hd : JamesTreeCoefficientBound S d C)
    (a : JamesTreePreSpace 𝕜 p S) :
    jamesTreeMultiplier hp hS d hC hd (jamesTreeDenseEmbedding 𝕜 p S a) =
      jamesTreeDenseEmbedding 𝕜 p S (JamesTreePreSpace.multiplierLinear d a) :=
  ContinuousLinearMap.extend_eq _ _ _ _ a

theorem jamesTreeMultiplier_norm_le (hp : 0 < p.val.toReal)
    (hS : ∀ A, S.allows A → JamesTreeMaskClosed S (A : Set DyadicTreeNode))
    (d : DyadicTreeNode → 𝕜) {C : ℝ} (hC : 0 ≤ C) (hd : JamesTreeCoefficientBound S d C)
    (x : SegmentJamesTreeSpace 𝕜 p S) : ‖jamesTreeMultiplier hp hS d hC hd x‖ ≤ C * ‖x‖ := by
  refine (jamesTreeDenseEmbedding_denseRange 𝕜 p S).induction_on x ?_ ?_
  · exact isClosed_le (jamesTreeMultiplier hp hS d hC hd).continuous.norm
      (continuous_const.mul continuous_norm)
  · intro a
    rw [jamesTreeMultiplier_dense, jamesTreeDenseEmbedding_norm, jamesTreeDenseEmbedding_norm]
    exact JamesTreePreSpace.multiplierLinear_norm_le hp hS d hC hd a

theorem norm_jamesTreeMultiplier_le (hp : 0 < p.val.toReal)
    (hS : ∀ A, S.allows A → JamesTreeMaskClosed S (A : Set DyadicTreeNode))
    (d : DyadicTreeNode → 𝕜) {C : ℝ} (hC : 0 ≤ C) (hd : JamesTreeCoefficientBound S d C) :
    ‖jamesTreeMultiplier hp hS d hC hd‖ ≤ C :=
  ContinuousLinearMap.opNorm_le_bound _ hC (jamesTreeMultiplier_norm_le hp hS d hC hd)

@[simp] theorem jamesTreeCoordinate_multiplier (hp : 0 < p.val.toReal)
    (hS : ∀ A, S.allows A → JamesTreeMaskClosed S (A : Set DyadicTreeNode))
    (d : DyadicTreeNode → 𝕜) {C : ℝ} (hC : 0 ≤ C) (hd : JamesTreeCoefficientBound S d C)
    (t : DyadicTreeNode) (x : SegmentJamesTreeSpace 𝕜 p S) :
    jamesTreeCoordinate t (jamesTreeMultiplier hp hS d hC hd x) = d t * jamesTreeCoordinate t x := by
  refine (jamesTreeDenseEmbedding_denseRange 𝕜 p S).induction_on x ?_ ?_
  · exact isClosed_eq
      ((jamesTreeCoordinate t).continuous.comp (jamesTreeMultiplier hp hS d hC hd).continuous)
      (continuous_const.mul (jamesTreeCoordinate t).continuous)
  · intro a
    simp only [jamesTreeMultiplier_dense, jamesTreeCoordinate_dense,
      JamesTreePreSpace.multiplierLinear_apply]

theorem jamesTreeMultiplier_reciprocal_comp (hp : 0 < p.val.toReal)
    (hS : ∀ A, S.allows A → JamesTreeMaskClosed S (A : Set DyadicTreeNode))
    (d : DyadicTreeNode → 𝕜) (hne : ∀ t, d t ≠ 0) {C K : ℝ}
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hd : JamesTreeCoefficientBound S d C)
    (hi : JamesTreeCoefficientBound S (fun t => (d t)⁻¹) K) :
    (jamesTreeMultiplier hp hS (fun t => (d t)⁻¹) hK hi).comp
      (jamesTreeMultiplier hp hS d hC hd) = ContinuousLinearMap.id 𝕜 _ := by
  apply ContinuousLinearMap.ext
  intro x
  refine (jamesTreeDenseEmbedding_denseRange 𝕜 p S).induction_on x ?_ ?_
  · exact isClosed_eq
      ((jamesTreeMultiplier hp hS (fun t => (d t)⁻¹) hK hi).continuous.comp
        (jamesTreeMultiplier hp hS d hC hd).continuous) continuous_id
  · intro a
    change jamesTreeMultiplier hp hS (fun t => (d t)⁻¹) hK hi
      (jamesTreeMultiplier hp hS d hC hd (jamesTreeDenseEmbedding 𝕜 p S a)) = _
    rw [jamesTreeMultiplier_dense, jamesTreeMultiplier_dense]
    apply congrArg (jamesTreeDenseEmbedding 𝕜 p S)
    apply JamesTreePreSpace.ext
    intro t
    simp only [JamesTreePreSpace.multiplierLinear_apply, ← mul_assoc, inv_mul_cancel₀ (hne t), one_mul]

end ThesisCommon

import ThesisCommon.Analysis.CZeroInfinityEmbedding
import ThesisCommon.Analysis.CZeroAdjointFactorization
import ThesisCommon.Analysis.AdjointWeakEssentialNorm

/-! The genuine non-weak-compactness and countable orthogonal self-copies
of scalar c₀ and ℓ∞, for algebra-norm factorization arguments. -/
noncomputable section
set_option synthInstance.maxSize 1024
set_option maxSynthPendingDepth 3
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

theorem not_weaklyCompact_id_cZero :
    ¬ IsWeaklyCompactOperator (ContinuousLinearMap.id 𝕜 (CZeroSum 𝕜)) := by
  intro h
  have hl := cZero_lower_bound_le_adjoint_weakEssentialNorm
    (ContinuousLinearMap.id 𝕜 (CZeroSum 𝕜)) (ContinuousLinearMap.id 𝕜 (CZeroSum 𝕜))
    ContinuousLinearMap.norm_id_le zero_le_one (fun x => by simp)
  have hh := hl.trans (weakEssentialNorm_banachAdjoint_le (ContinuousLinearMap.id 𝕜 (CZeroSum 𝕜)))
  rw [h.weakEssentialNorm_eq_zero] at hh
  norm_num at hh

theorem not_weaklyCompact_id_ellInfinity :
    ¬ IsWeaklyCompactOperator (ContinuousLinearMap.id 𝕜 (EllInfinitySum 𝕜)) := by
  intro h
  have hl := cZero_lower_bound_le_adjoint_weakEssentialNorm
    (ContinuousLinearMap.id 𝕜 (EllInfinitySum 𝕜))
    (cZeroToInfinityIsometry (𝕜 := 𝕜)).toContinuousLinearMap
    (cZeroToInfinityIsometry (𝕜 := 𝕜)).norm_toContinuousLinearMap_le zero_le_one
    (fun x => by
      change 1 * ‖x‖ ≤ ‖cZeroToInfinityIsometry (𝕜 := 𝕜) x‖
      rw [one_mul, LinearIsometry.norm_map])
  have hh := hl.trans (weakEssentialNorm_banachAdjoint_le (ContinuousLinearMap.id 𝕜 (EllInfinitySum 𝕜)))
  rw [h.weakEssentialNorm_eq_zero] at hh
  norm_num at hh

theorem exists_orthogonal_selfCopies_cZero :
    ∃ J P : ℕ → CZeroSum 𝕜 →L[𝕜] CZeroSum 𝕜,
      (∀ n, (P n).comp (J n) = ContinuousLinearMap.id 𝕜 _) ∧
      (∀ n m, n ≠ m → (P n).comp (J m) = 0) := by
  refine ⟨fun n => cZeroExtend (disjointCoordinateEmbedding n),
    fun n => cZeroRestrict (disjointCoordinateEmbedding n), ?_, ?_⟩
  · intro n
    ext x k
    simp
  · intro n m hnm
    ext x k
    change Function.extend (disjointCoordinateEmbedding m) x 0 (disjointCoordinateEmbedding n k) = 0
    have hnot : ¬ ∃ j, disjointCoordinateEmbedding m j = disjointCoordinateEmbedding n k := by
      rintro ⟨j, hj⟩
      exact hnm (disjointCoordinateEmbedding_disjoint hj).symm
    simp [Function.extend_apply' _ _ _ hnot]

theorem exists_orthogonal_selfCopies_ellInfinity :
    ∃ J P : ℕ → EllInfinitySum 𝕜 →L[𝕜] EllInfinitySum 𝕜,
      (∀ n, (P n).comp (J n) = ContinuousLinearMap.id 𝕜 _) ∧
      (∀ n m, n ≠ m → (P n).comp (J m) = 0) := by
  refine ⟨fun n => lpExtend ∞ (disjointCoordinateEmbedding n),
    fun n => lpRestrict ∞ (disjointCoordinateEmbedding n), ?_, ?_⟩
  · intro n
    ext x k
    simp
  · intro n m hnm
    ext x k
    change Function.extend (disjointCoordinateEmbedding m) x 0 (disjointCoordinateEmbedding n k) = 0
    have hnot : ¬ ∃ j, disjointCoordinateEmbedding m j = disjointCoordinateEmbedding n k := by
      rintro ⟨j, hj⟩
      exact hnm (disjointCoordinateEmbedding_disjoint hj).symm
    simp [Function.extend_apply' _ _ _ hnot]

end ThesisCommon

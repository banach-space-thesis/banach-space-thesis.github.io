import ThesisCommon.Analysis.EllOneWeakEssentialIdentity
import ThesisCommon.Analysis.DisjointSequenceBlocks

/-! Genuine scalar ℓ1 geometry for unrestricted algebra-norm minimality. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

theorem not_weaklyCompact_id_scalarEllOne :
    ¬ IsWeaklyCompactOperator (ContinuousLinearMap.id 𝕜 (lp (fun _ : ℕ => 𝕜) 1)) := by
  intro h
  have hz := h.weakEssentialNorm_eq_zero
  rw [weakEssentialNorm_id_scalarEllOne] at hz
  norm_num at hz

theorem exists_orthogonal_selfCopies_scalarEllOne :
    ∃ J P : ℕ → lp (fun _ : ℕ => 𝕜) 1 →L[𝕜] lp (fun _ : ℕ => 𝕜) 1,
      (∀ n, (P n).comp (J n) = ContinuousLinearMap.id 𝕜 _) ∧
      (∀ n m, n ≠ m → (P n).comp (J m) = 0) := by
  refine ⟨fun n => lpExtend 1 (disjointCoordinateEmbedding n),
    fun n => lpRestrict 1 (disjointCoordinateEmbedding n), ?_, ?_⟩
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

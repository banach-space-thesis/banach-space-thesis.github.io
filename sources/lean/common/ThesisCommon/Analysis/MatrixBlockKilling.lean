import ThesisCommon.Analysis.MatrixBlockKillingCore
import ThesisCommon.Analysis.MatrixHilbertSchmidtComparison

/-! The full block projection lemma, with both quantitative comparison
premises discharged on the actual finite ℓp operator spaces. -/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

theorem exists_matrixBlock_small_on_subspace (p : BanachExponent)
    (hp : 1 < p.val.toReal) (hfin : p.val ≠ ∞) (k d : ℕ) (hk : 0 < k) (hd : 0 < d)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      ∀ E : Submodule 𝕜 (FiniteMatrixBlock 𝕜 p N), Module.finrank 𝕜 E = d →
        ∃ α τ : Fin k ↪o Fin N, ∀ x : E,
          ‖matrixBlockProjection p α.toEmbedding τ.toEmbedding (x : FiniteMatrixBlock 𝕜 p N)‖ ≤ ε * ‖x‖ := by
  apply exists_matrixBlock_small_on_subspace_of_comparisons p
    |1 / p.val.toReal - 1 / 2| (abs_nonneg _) (matrixExponentDeviation_lt_half p hp)
    (fun N hN A => matrixHilbertSchmidtNorm_le_dimension_mul_norm p hfin hN A)
    (fun N hN A => norm_le_dimension_mul_matrixHilbertSchmidtNorm p hfin hN A) k d hk hd hε

end ThesisCommon

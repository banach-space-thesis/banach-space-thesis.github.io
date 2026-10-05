import ThesisCommon.Analysis.MatrixSumOperators

/-! The concrete data produced by the almost-diagonalisation recursion.
The past subspaces and future bands describe actual bounded-product vectors. -/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

structure MatrixAlmostDiagonalData (p : BanachExponent)
    (T : FiniteMatrixSum 𝕜 p →L[𝕜] FiniteMatrixSum 𝕜 p) (b : ℕ → ℝ) where
  n : ℕ → ℕ
  n_strictMono : StrictMono n
  le_n : ∀ k, k ≤ n k
  row : ∀ k, Fin (k + 1) ↪o Fin (n k + 1)
  col : ∀ k, Fin (k + 1) ↪o Fin (n k + 1)
  band : ℕ → Set ℕ
  band_antitone : Antitone band
  n_mem_band : ∀ k, n k ∈ band k
  past : ℕ → Submodule 𝕜 (FiniteMatrixSum 𝕜 p)
  past_monotone : Monotone past
  single_mem_past : ∀ k (x : FiniteMatrixBlock 𝕜 p (k + 1)),
    matrixSumSingle (𝕜 := 𝕜) p (n k)
      (matrixInsert (𝕜 := 𝕜) p (row k).toEmbedding (col k).toEmbedding x) ∈ past (k + 1)
  past_small : ∀ k (y : FiniteMatrixSum 𝕜 p), y ∈ past k →
    ‖matrixBlockProjection (𝕜 := 𝕜) p (row k).toEmbedding (col k).toEmbedding (T y (n k))‖ ≤
      b k * ‖T y (n k)‖
  future_small : ∀ k,
    ‖((matrixSumCoordinate (𝕜 := 𝕜) p (n k)).comp T).comp
      (matrixSumMask (𝕜 := 𝕜) p (band (k + 1)))‖ ≤ b k

end ThesisCommon

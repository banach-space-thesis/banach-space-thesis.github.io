import ThesisCommon.Analysis.InfinityScalarRows
import ThesisCommon.Analysis.BoundedColumnSelection

/-! The full small-interference conclusion, with summability included.
The matrix is transposed only as notation: rows of this nonnegative matrix
are the vectors x_n, so bounded scalar coordinate sums are its column bounds.
The shared proof is the same nested-infinite-set construction as the source.
-/
noncomputable section
open scoped ENNReal BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

theorem bounded_finite_sums_small_off_diagonal
    {x : ℕ → lp (fun _ : ℕ => 𝕜) ∞} {K : ℝ} (hK : 0 ≤ K)
    (h : HasBoundedFiniteSums (𝕜 := 𝕜) x K)
    {M : Set ℕ} (hM : M.Infinite) {ε : ℝ} (hε : 0 < ε) :
    ∃ f : ℕ ↪ ℕ, StrictMono f ∧ (∀ k, f k ∈ M) ∧ ∀ k,
      Summable (fun j => if j = k then 0 else ‖x (f j) (f k)‖) ∧
      (∑' j, if j = k then 0 else ‖x (f j) (f k)‖) < ε :=
  bounded_columns_small_off_diagonal (fun n m => ‖x n m‖)
    (fun _ _ => norm_nonneg _) (bounded_finite_sums_coordinate_sum_le hK h) hM hε

theorem infinity_images_have_bounded_finite_sums
    (T : lp (fun _ : ℕ => 𝕜) ∞ →L[𝕜] lp (fun _ : ℕ => 𝕜) ∞) :
    HasBoundedFiniteSums (𝕜 := 𝕜) (fun n => T (lp.single ∞ n (1 : 𝕜))) ‖T‖ := by
  intro F a
  dsimp only
  simp only [← map_smul]
  rw [← map_sum]
  exact (T.le_opNorm _).trans (mul_le_mul_of_nonneg_left
    (infinity_norm_sum_single_le F a) (norm_nonneg T))

end ThesisCommon

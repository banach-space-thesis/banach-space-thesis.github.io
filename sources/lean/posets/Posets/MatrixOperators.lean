import Posets.Matrices
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-! A matrix with summable, uniformly bounded rows acts as a genuine bounded
linear operator on ℓ∞, with the paper's quantitative estimate. -/
noncomputable section
open Filter Topology
open scoped BoundedContinuousFunction
namespace Posets
variable {𝕜 : Type*} [RCLike 𝕜]

theorem summable_matrix_row (M : ScalarMatrix 𝕜) (hM : HasBoundedRows 𝕜 M)
    (f : ℕ →ᵇ 𝕜) (k : ℕ) : Summable (fun n => M k n * f n) := by
  apply ((hM.1 k).mul_right ‖f‖).of_norm_bounded
  intro n
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm n) (norm_nonneg _)

theorem matrixNorm_nonneg (M : ScalarMatrix 𝕜) (hM : HasBoundedRows 𝕜 M) :
    0 ≤ matrixNorm 𝕜 M := by
  apply (tsum_nonneg (fun n => norm_nonneg (M 0 n))).trans
  exact le_ciSup (by obtain ⟨C, hC⟩ := hM.2; exact ⟨C, by rintro _ ⟨k, rfl⟩; exact hC k⟩) 0

theorem matrixAction_bound (M : ScalarMatrix 𝕜) (hM : HasBoundedRows 𝕜 M)
    (f : ℕ →ᵇ 𝕜) (k : ℕ) : ‖matrixAction 𝕜 M f k‖ ≤ matrixNorm 𝕜 M * ‖f‖ := by
  have hbound : ∀ n, ‖M k n * f n‖ ≤ ‖M k n‖ * ‖f‖ := by
    intro n
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm n) (norm_nonneg _)
  calc
    ‖matrixAction 𝕜 M f k‖ ≤ ∑' n, ‖M k n‖ * ‖f‖ :=
      tsum_of_norm_bounded ((hM.1 k).mul_right ‖f‖).hasSum hbound
    _ = (∑' n, ‖M k n‖) * ‖f‖ := tsum_mul_right
    _ ≤ matrixNorm 𝕜 M * ‖f‖ := mul_le_mul_of_nonneg_right
      (le_ciSup (by obtain ⟨C, hC⟩ := hM.2; exact ⟨C, by rintro _ ⟨j, rfl⟩; exact hC j⟩) k)
      (norm_nonneg f)

def matrixOnBounded (M : ScalarMatrix 𝕜) (hM : HasBoundedRows 𝕜 M)
    (f : ℕ →ᵇ 𝕜) : ℕ →ᵇ 𝕜 :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete (matrixAction 𝕜 M f)
    (matrixNorm 𝕜 M * ‖f‖) (matrixAction_bound M hM f)

/-- Definition 4.11: the action is a continuous linear map on the actual
space of bounded scalar sequences, rather than just a formal infinite sum. -/
def matrixOperator (M : ScalarMatrix 𝕜) (hM : HasBoundedRows 𝕜 M) :
    (ℕ →ᵇ 𝕜) →L[𝕜] (ℕ →ᵇ 𝕜) :=
  ({toFun := matrixOnBounded M hM
    map_add' := by
      intro f g
      ext k
      change (∑' n, M k n * (f n + g n)) =
        (∑' n, M k n * f n) + ∑' n, M k n * g n
      simp_rw [mul_add]
      exact (summable_matrix_row M hM f k).tsum_add (summable_matrix_row M hM g k)
    map_smul' := by
      intro a f
      ext k
      change (∑' n, M k n * (a * f n)) = a * ∑' n, M k n * f n
      simp_rw [mul_left_comm (M k _) a]
      exact tsum_mul_left} : (ℕ →ᵇ 𝕜) →ₗ[𝕜] (ℕ →ᵇ 𝕜)).mkContinuous
    (matrixNorm 𝕜 M) (fun f =>
      (BoundedContinuousFunction.norm_le
        (mul_nonneg (matrixNorm_nonneg M hM) (norm_nonneg f))).mpr
        (matrixAction_bound M hM f))

@[simp] theorem matrixOperator_apply (M : ScalarMatrix 𝕜) (hM : HasBoundedRows 𝕜 M)
    (f : ℕ →ᵇ 𝕜) (k : ℕ) : matrixOperator M hM f k = ∑' n, M k n * f n := rfl

theorem norm_matrixOperator_le (M : ScalarMatrix 𝕜) (hM : HasBoundedRows 𝕜 M) :
    ‖matrixOperator M hM‖ ≤ matrixNorm 𝕜 M := by
  apply ContinuousLinearMap.opNorm_le_bound _ (matrixNorm_nonneg M hM)
  intro f
  apply (BoundedContinuousFunction.norm_le
    (mul_nonneg (matrixNorm_nonneg M hM) (norm_nonneg f))).mpr
  exact matrixAction_bound M hM f

end Posets

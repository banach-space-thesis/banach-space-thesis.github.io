import ThesisCommon.Analysis.InfinityAtomicPart
import ThesisCommon.Analysis.InfinityAnnihilator

/-! A genuine matrix representation after restricting an arbitrary bounded
ell_infinity operator to a suitable infinite coordinate support. Absolute
convergence and the representation are conclusions, not assumptions.
-/
noncomputable section
open scoped ENNReal BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

theorem infinity_operator_row_sum_le
    (T : lp (fun _ : ℕ => 𝕜) ∞ →L[𝕜] lp (fun _ : ℕ => 𝕜) ∞) (m : ℕ) (F : Finset ℕ) :
    ∑ n ∈ F, ‖T (lp.single ∞ n (1 : 𝕜)) m‖ ≤ ‖T‖ := by
  let φ := (lpCoordinate (𝕜 := 𝕜) ∞ m).comp T
  apply (infinity_functional_row_sum_le φ F).trans
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul_of_nonneg_right (norm_lpCoordinate_le ∞ m) (norm_nonneg T)).trans_eq (one_mul _))

theorem infinity_matrix_restriction
    (T : lp (fun _ : ℕ => 𝕜) ∞ →L[𝕜] lp (fun _ : ℕ => 𝕜) ∞)
    {A : Set ℕ} (hA : A.Infinite) :
    ∃ M : Set ℕ, M ⊆ A ∧ M.Infinite ∧
      ∀ m (x : lp (fun _ : ℕ => 𝕜) ∞), (∀ n ∉ M, x n = 0) →
        HasSum (fun n => x n * T (lp.single ∞ n (1 : 𝕜)) m) (T x m) := by
  let φ := fun m => (lpCoordinate (𝕜 := 𝕜) ∞ m).comp T
  obtain ⟨M, hMA, hM, hzero⟩ := infinity_common_annihilator
    (fun m => φ m - infinityAtomicPart (φ m)) (fun m => infinity_residual_single (φ m)) hA
  refine ⟨M, hMA, hM, ?_⟩
  intro m x hx
  have heq := hzero m x hx
  rw [ContinuousLinearMap.sub_apply, sub_eq_zero] at heq
  change T x m = ∑' n, x n * T (lp.single ∞ n (1 : 𝕜)) m at heq
  rw [heq]
  exact (infinity_weighted_coefficients_summable (φ m) x).hasSum

end ThesisCommon

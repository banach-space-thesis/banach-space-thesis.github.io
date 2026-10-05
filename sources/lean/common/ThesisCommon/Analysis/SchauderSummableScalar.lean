import ThesisCommon.Analysis.SchauderOperators
import ThesisCommon.Analysis.SchauderSummablePerturbation

/-! Absolutely summable diagonal errors control the norm of a genuine
bounded diagonal operator. Only bounded coordinates and a Schauder basis
are required; Haar unconditionality is not used. -/

noncomputable section
open scoped BigOperators
namespace ThesisCommon.NormalizedSchauderBasis
variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [CompleteSpace X]

theorem norm_diagonal_sub_scalar_le (b : NormalizedSchauderBasis 𝕜 X)
    {K : ℝ} (hK : ∀ n, ‖b.coord n‖ ≤ K)
    (D : X →L[𝕜] X) (d : ℕ → 𝕜) (hD : ∀ n, D (b.vector n) = d n • b.vector n)
    (c : 𝕜) (hs : Summable (fun n => ‖d n - c‖)) :
    ‖D - c • ContinuousLinearMap.id 𝕜 X‖ ≤ K * ∑' n, ‖d n - c‖ := by
  let F : ℕ → X →L[𝕜] X := fun n => (b.coord n).smulRight ((d n - c) • b.vector n)
  have hnorm (n : ℕ) : ‖F n‖ ≤ K * ‖d n - c‖ := by
    dsimp only [F]
    rw [ContinuousLinearMap.norm_smulRight_apply, norm_smul, b.norm_vector, mul_one]
    exact mul_le_mul_of_nonneg_right (hK n) (norm_nonneg _)
  have hF : Summable F := (hs.mul_left K).of_norm_bounded hnorm
  have hFnorm : Summable (fun n => ‖F n‖) :=
    (hs.mul_left K).of_nonneg_of_le (fun n => norm_nonneg _) hnorm
  have heq : D - c • ContinuousLinearMap.id 𝕜 X = ∑' n, F n := by
    apply b.operator_ext
    intro j
    have h := (ContinuousLinearMap.apply 𝕜 X (b.vector j)).map_tsum hF
    change (D - c • ContinuousLinearMap.id 𝕜 X) (b.vector j) =
      (ContinuousLinearMap.apply 𝕜 X (b.vector j)) (∑' n, F n)
    rw [h, tsum_eq_single j]
    · simp [ContinuousLinearMap.apply_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.id_apply, hD, F, ContinuousLinearMap.smulRight_apply,
        b.biorthogonal, if_pos rfl, one_smul, sub_smul]
    · intro n hnj
      simp only [F, ContinuousLinearMap.apply_apply, ContinuousLinearMap.smulRight_apply,
        b.biorthogonal, if_neg hnj, zero_smul]
  rw [heq]
  calc
    _ ≤ ∑' n, ‖F n‖ := norm_tsum_le_tsum_norm hFnorm
    _ ≤ ∑' n, K * ‖d n - c‖ := hFnorm.tsum_le_tsum hnorm (hs.mul_left K)
    _ = _ := tsum_mul_left

end ThesisCommon.NormalizedSchauderBasis

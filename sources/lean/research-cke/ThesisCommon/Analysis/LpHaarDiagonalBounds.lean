import ThesisCommon.Analysis.LpHaarSchauderBasis
import ThesisCommon.Analysis.SchauderKernelTail

/-! Every bounded operator on actual interval Lp has uniformly bounded
raw Haar diagonal coefficients. Normalisation cancels exactly; no
unconditionality or symmetry of the Haar basis is assumed. -/

noncomputable section
open scoped ENNReal
namespace ThesisCommon
variable (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent) (hp : p.val ≠ ∞)
include hp

theorem intervalLpHaarBasis_coord_norm_le (i : ℕ) :
    ‖(intervalLpHaarBasis 𝕜 p hp).coord i‖ ≤ 6 := by
  convert (intervalLpHaarBasis 𝕜 p hp).coord_norm_le_of_prefix_bound
    (by norm_num : (0 : ℝ) ≤ 3) (intervalLpHaarBasis_prefix_norm_le 𝕜 p hp) i
    using 1 <;> norm_num

theorem lpHaarRawCoordinate_diagonal_normalized
    (T : IntervalLp 𝕜 p →L[𝕜] IntervalLp 𝕜 p)
    (i : Option LpHaarTreeIndex) :
    lpHaarNormalizedCoordinate 𝕜 p i (T (lpHaarNormalizedVector 𝕜 p i)) =
      lpHaarRawCoordinate 𝕜 p i (T (lpHaarRawVector 𝕜 p i)) := by
  have hn : ((‖lpHaarRawVector 𝕜 p i‖ : ℝ) : 𝕜) ≠ 0 :=
    RCLike.ofReal_ne_zero.mpr (lpHaarRawVector_norm_pos 𝕜 p hp i).ne'
  simp only [lpHaarNormalizedCoordinate, lpHaarNormalizedVector,
    ContinuousLinearMap.smul_apply, map_smul, smul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ hn, one_mul]

theorem lpHaar_operator_diagonal_norm_le
    (T : IntervalLp 𝕜 p →L[𝕜] IntervalLp 𝕜 p) (n : ℕ) (k : Fin (2 ^ n)) :
    ‖lpHaarDyadicCoefficient 𝕜 p n k (T (lpHaarDyadic 𝕜 p n k))‖ ≤ 6 * ‖T‖ := by
  let i : Option LpHaarTreeIndex := some ⟨n, k⟩
  let j := lpHaarEncode i
  have he : lpHaarIndexEquiv j = i := lpHaarDecode_encode i
  have hc : ‖lpHaarNormalizedCoordinate 𝕜 p i‖ ≤ 6 := by
    simpa only [intervalLpHaarBasis, he] using intervalLpHaarBasis_coord_norm_le 𝕜 p hp j
  change ‖lpHaarRawCoordinate 𝕜 p i (T (lpHaarRawVector 𝕜 p i))‖ ≤ _
  rw [← lpHaarRawCoordinate_diagonal_normalized 𝕜 p hp T i]
  calc
    _ ≤ ‖lpHaarNormalizedCoordinate 𝕜 p i‖ * ‖T (lpHaarNormalizedVector 𝕜 p i)‖ :=
      (lpHaarNormalizedCoordinate 𝕜 p i).le_opNorm _
    _ ≤ 6 * (‖T‖ * ‖lpHaarNormalizedVector 𝕜 p i‖) :=
      mul_le_mul hc (T.le_opNorm _) (norm_nonneg _) (by norm_num)
    _ = _ := by rw [lpHaarNormalizedVector_norm 𝕜 p hp, mul_one]

end ThesisCommon

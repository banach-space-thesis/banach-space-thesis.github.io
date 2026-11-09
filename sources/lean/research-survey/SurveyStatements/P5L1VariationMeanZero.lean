import SurveyStatements.P5L1VariationLinfty
import SurveyStatements.P5Support.LpMeanZeroRetracts

/-! The finite-branch necessity and full scalar trace result on the actual
cancellative L¹ space. Its multiplier is extended by the genuine mean-zero
projection, with a proved norm bound. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
namespace SurveyStatements.P5L1Variation
open SurveyStatements.P5Support
local instance : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) := ⟨by simp⟩

abbrev MeanZeroL1 (𝕜 : Type*) [RCLike 𝕜] := IntervalLpMeanZero 𝕜 ⟨1, le_rfl⟩

def meanZeroHaar (𝕜 : Type*) [RCLike 𝕜] (n : ℕ) (k : Fin (2 ^ n)) : MeanZeroL1 𝕜 :=
  ⟨lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ n k, by
    change lpHaarIntegral (lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ n k) = 0
    rw [lpHaarIntegral_apply]
    exact lpHaarDyadic_integral_zero 𝕜 ⟨1, le_rfl⟩ n k k.isLt⟩

theorem meanZeroProjection_norm_le (𝕜 : Type*) [RCLike 𝕜] (f : IntervalL1 𝕜) :
    ‖intervalLpMeanZeroProjection 𝕜 ⟨1, le_rfl⟩ f‖ ≤ 2 * ‖f‖ := by
  have hc : ‖lpHaarRawVector 𝕜 ⟨1, le_rfl⟩ none‖ = 1 := by
    change ‖Lp.const (1 : ℝ≥0∞) (volume.restrict (Icc (0 : ℝ) 1)) (1 : 𝕜)‖ = 1
    rw [Lp.norm_const' _ _ _ (by norm_num) (by norm_num)]
    simp
  change ‖f - lpHaarIntegral f • lpHaarRawVector 𝕜 ⟨1, le_rfl⟩ none‖ ≤ 2 * ‖f‖
  have hi : ‖lpHaarIntegral f‖ ≤ ‖f‖ := by
    rw [lpHaarIntegral_apply]
    exact lpHaarIntegral_norm_le f
  calc
    _ ≤ ‖f‖ + ‖lpHaarIntegral f • lpHaarRawVector 𝕜 ⟨1, le_rfl⟩ none‖ := norm_sub_le _ _
    _ = ‖f‖ + ‖lpHaarIntegral f‖ := by rw [norm_smul, hc, mul_one]
    _ ≤ _ := by linarith

def extendMeanZero (𝕜 : Type*) [RCLike 𝕜]
    (R : MeanZeroL1 𝕜 →L[𝕜] MeanZeroL1 𝕜) : IntervalL1 𝕜 →L[𝕜] IntervalL1 𝕜 :=
  (intervalLpMeanZeroSubmodule 𝕜 ⟨1, le_rfl⟩).subtypeL.comp
    (R.comp (intervalLpMeanZeroProjection 𝕜 ⟨1, le_rfl⟩))

theorem extendMeanZero_norm_le (𝕜 : Type*) [RCLike 𝕜]
    (R : MeanZeroL1 𝕜 →L[𝕜] MeanZeroL1 𝕜) : ‖extendMeanZero 𝕜 R‖ ≤ 2 * ‖R‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro f
  change ‖R (intervalLpMeanZeroProjection 𝕜 ⟨1, le_rfl⟩ f)‖ ≤ (2 * ‖R‖) * ‖f‖
  calc
    _ ≤ ‖R‖ * ‖intervalLpMeanZeroProjection 𝕜 ⟨1, le_rfl⟩ f‖ := R.le_opNorm _
    _ ≤ ‖R‖ * (2 * ‖f‖) :=
      mul_le_mul_of_nonneg_left (meanZeroProjection_norm_le 𝕜 f) (norm_nonneg R)
    _ = _ := by ring

theorem meanZeroProjection_haar (𝕜 : Type*) [RCLike 𝕜]
    (n : ℕ) (k : Fin (2 ^ n)) :
    intervalLpMeanZeroProjection 𝕜 ⟨1, le_rfl⟩ (lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ n k) =
      meanZeroHaar 𝕜 n k := by
  apply Subtype.ext
  change lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ n k -
      lpHaarIntegral (lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ n k) •
        lpHaarRawVector 𝕜 ⟨1, le_rfl⟩ none = lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ n k
  rw [lpHaarIntegral_apply, lpHaarDyadic_integral_zero 𝕜 ⟨1, le_rfl⟩ n k k.isLt]
  simp

theorem extendMeanZero_haar (𝕜 : Type*) [RCLike 𝕜]
    (R : MeanZeroL1 𝕜 →L[𝕜] MeanZeroL1 𝕜)
    (d : (n : ℕ) → Fin (2 ^ n) → 𝕜)
    (hR : ∀ n k, R (meanZeroHaar 𝕜 n k) = d n k • meanZeroHaar 𝕜 n k)
    (n : ℕ) (k : Fin (2 ^ n)) :
    extendMeanZero 𝕜 R (lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ n k) =
      d n k • lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ n k := by
  change (R (intervalLpMeanZeroProjection 𝕜 ⟨1, le_rfl⟩
    (lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ n k))).val = _
  rw [meanZeroProjection_haar, hR]
  rfl

theorem meanZero_finite_branch_variation_le (𝕜 : Type*) [RCLike 𝕜]
    (R : MeanZeroL1 𝕜 →L[𝕜] MeanZeroL1 𝕜)
    (d : (n : ℕ) → Fin (2 ^ n) → 𝕜)
    (hR : ∀ n k, R (meanZeroHaar 𝕜 n k) = d n k • meanZeroHaar 𝕜 n k)
    {r : ℕ} (B : DyadicBranch r) (N : ℕ) :
    (∑ j ∈ Finset.range N, ‖B.symbol 𝕜 d (j + 1) - B.symbol 𝕜 d j‖) ≤ 12 * ‖R‖ := by
  have hv := B.finite_variation_le 𝕜 (extendMeanZero 𝕜 R) d
    (extendMeanZero_haar 𝕜 R d hR) N
  have hn := extendMeanZero_norm_le 𝕜 R
  linarith

theorem meanZero_exists_full_trace_Linfty_density (𝕜 : Type*) [RCLike 𝕜]
    (R : MeanZeroL1 𝕜 →L[𝕜] MeanZeroL1 𝕜)
    (d : (n : ℕ) → Fin (2 ^ n) → 𝕜)
    (hR : ∀ n k, R (meanZeroHaar 𝕜 n k) = d n k • meanZeroHaar 𝕜 n k) :
    ∃ m : IntervalLinfty 𝕜, ‖m‖ ≤ 2 * ‖R‖ ∧
      ∀ s : Set ℝ, Tendsto (fun n => lpHaarLevelTrace d n s) atTop
        (𝓝 (∫ x in s, m x ∂(volume.restrict (Icc (0 : ℝ) 1)))) := by
  obtain ⟨m, hm, htrace⟩ := exists_full_trace_Linfty_density 𝕜 (extendMeanZero 𝕜 R) d
    (extendMeanZero_haar 𝕜 R d hR)
  exact ⟨m, hm.trans (extendMeanZero_norm_le 𝕜 R), htrace⟩

end SurveyStatements.P5L1Variation

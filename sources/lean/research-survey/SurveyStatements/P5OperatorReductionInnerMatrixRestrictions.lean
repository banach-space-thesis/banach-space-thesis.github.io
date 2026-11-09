import SurveyStatements.P5OperatorReductionDisjointReaders
import SurveyStatements.P5Support.LpHaarBiorthogonal

/-! Actual L1 normalized Haar coordinates are norm-one Haar integral
readers restricted to their genuine disjoint parent cells. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter Set
open scoped ENNReal Classical BigOperators

namespace SurveyStatements.P5OperatorReduction
open SurveyStatements.P5 SurveyStatements.P5Support
variable {𝕜 : Type*} [RCLike 𝕜]

local instance innerMatrixNativeIntervalProbability :
    IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) := ⟨by simp⟩

def operatorReductionL1Exponent : BanachExponent := ⟨1, le_rfl⟩

def innerMatrixHaarReader (𝕜 : Type*) [RCLike 𝕜] (n : ℕ) (k : Fin (2 ^ n)) :
    IntervalLp 𝕜 operatorReductionL1Exponent →L[𝕜] 𝕜 :=
  (lpHaarIntegral (𝕜 := 𝕜) (p := 1) (μ := unitIntervalMeasure)).comp
    (lpHaarMultiply (𝕜 := 𝕜) (p := 1) (μ := unitIntervalMeasure)
      (lpHaarCell (n + 1) (2 * k.val)) (lpHaarCell (n + 1) (2 * k.val + 1))
      measurableSet_Ioc measurableSet_Ioc
      (lpHaarCell_disjoint_sameLevel (n + 1) (by omega)))

theorem innerMatrixHaarReader_apply (n : ℕ) (k : Fin (2 ^ n))
    (y : IntervalLp 𝕜 operatorReductionL1Exponent) :
    innerMatrixHaarReader 𝕜 n k y =
      ∫ x, lpHaarFunction 𝕜 (lpHaarCell (n + 1) (2 * k.val))
        (lpHaarCell (n + 1) (2 * k.val + 1)) x * y x ∂unitIntervalMeasure := by
  rw [innerMatrixHaarReader, ContinuousLinearMap.comp_apply, lpHaarIntegral_apply]
  exact integral_congr_ae (lpHaarMultiply_coe _ _ measurableSet_Ioc measurableSet_Ioc
    (lpHaarCell_disjoint_sameLevel (n + 1) (by omega)) y)

theorem norm_innerMatrixHaarReader_le (n : ℕ) (k : Fin (2 ^ n)) :
    ‖innerMatrixHaarReader 𝕜 n k‖ ≤ 1 := by
  unfold innerMatrixHaarReader
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul
      (norm_lpHaarIntegral_le (𝕜 := 𝕜) (p := 1) (μ := unitIntervalMeasure))
      (norm_lpHaarMultiply_le (𝕜 := 𝕜) (p := 1) (μ := unitIntervalMeasure)
        _ _ measurableSet_Ioc measurableSet_Ioc
        (lpHaarCell_disjoint_sameLevel (n + 1) (by omega)))
      (norm_nonneg _) zero_le_one).trans_eq (one_mul 1))

theorem innerMatrixNormalizedCoordinate_eq_reader (n : ℕ) (k : Fin (2 ^ n)) :
    lpHaarNormalizedCoordinate 𝕜 operatorReductionL1Exponent (some ⟨n, k⟩) =
      innerMatrixHaarReader 𝕜 n k := by
  have hm : (volume.restrict (Icc (0 : ℝ) 1)).real
      (lpHaarCell (n + 1) (2 * k.val) ∪ lpHaarCell (n + 1) (2 * k.val + 1)) =
      intervalLpDyadicRadius n := by
    rw [lpHaarCell_children, measureReal_def, lpHaarCell_measure n k k.isLt,
      ENNReal.toReal_ofReal (intervalLpDyadicRadius_pos n).le]
  have hn : ((intervalLpDyadicRadius n : ℝ) : 𝕜) ≠ 0 :=
    RCLike.ofReal_ne_zero.mpr (intervalLpDyadicRadius_pos n).ne'
  ext y
  rw [lpHaarNormalizedCoordinate, ContinuousLinearMap.smul_apply, smul_eq_mul,
    lpHaarRawVector, lpHaarRawCoordinate, lpHaarDyadicCoefficient, lpHaarCoefficient_apply,
    lpHaarDyadic_norm 𝕜 operatorReductionL1Exponent (by norm_num [operatorReductionL1Exponent])
      n k k.isLt, hm]
  simp only [operatorReductionL1Exponent, ENNReal.toReal_one, div_one, Real.rpow_one]
  rw [← mul_assoc, mul_inv_cancel₀ hn, one_mul]
  simpa only [unitIntervalMeasure] using
    (innerMatrixHaarReader_apply (𝕜 := 𝕜) n k y).symm

theorem innerMatrixHaarReader_eq_restricted (n : ℕ) (k : Fin (2 ^ n)) :
    innerMatrixHaarReader 𝕜 n k =
      restrictedFunctional (lpHaarCell n k) measurableSet_Ioc
        (innerMatrixHaarReader 𝕜 n k) := by
  ext y
  change innerMatrixHaarReader 𝕜 n k y = innerMatrixHaarReader 𝕜 n k
    (vectorIndicatorMultiply (𝕜 := 𝕜) (lpHaarCell n k) measurableSet_Ioc y)
  rw [innerMatrixHaarReader_apply, innerMatrixHaarReader_apply]
  apply integral_congr_ae
  filter_upwards [vectorIndicatorMultiply_ae (𝕜 := 𝕜)
    (lpHaarCell n k) measurableSet_Ioc y] with x hx
  rw [hx]
  by_cases hmem : x ∈ lpHaarCell n k
  · rw [Set.indicator_of_mem hmem]
  · have hchildren : x ∉ lpHaarCell (n + 1) (2 * k.val) ∪
        lpHaarCell (n + 1) (2 * k.val + 1) := by
      rw [lpHaarCell_children]
      exact hmem
    simp only [mem_union, not_or] at hchildren
    simp [lpHaarFunction, hchildren.1, hchildren.2]

theorem norm_innerMatrixHaarReader_eq_one (n : ℕ) (k : Fin (2 ^ n)) :
    ‖innerMatrixHaarReader 𝕜 n k‖ = 1 := by
  apply le_antisymm (norm_innerMatrixHaarReader_le n k)
  have hp : operatorReductionL1Exponent.val ≠ ∞ := by
    norm_num [operatorReductionL1Exponent]
  have hvalue : innerMatrixHaarReader 𝕜 n k
      (lpHaarNormalizedVector 𝕜 operatorReductionL1Exponent (some ⟨n, k⟩)) = 1 := by
    rw [← innerMatrixNormalizedCoordinate_eq_reader n k]
    simpa only [if_pos rfl] using lpHaarNormalized_biorthogonal
      𝕜 operatorReductionL1Exponent hp (some ⟨n, k⟩) (some ⟨n, k⟩)
  have h := (innerMatrixHaarReader 𝕜 n k).le_opNorm
    (lpHaarNormalizedVector 𝕜 operatorReductionL1Exponent (some ⟨n, k⟩))
  rw [hvalue, norm_one,
    lpHaarNormalizedVector_norm 𝕜 operatorReductionL1Exponent hp, mul_one] at h
  exact h

theorem innerMatrixNormalizedCoordinate_eq_restricted (n : ℕ) (k : Fin (2 ^ n)) :
    lpHaarNormalizedCoordinate 𝕜 operatorReductionL1Exponent (some ⟨n, k⟩) =
      restrictedFunctional (lpHaarCell n k) measurableSet_Ioc
        (innerMatrixHaarReader 𝕜 n k) :=
  (innerMatrixNormalizedCoordinate_eq_reader n k).trans (innerMatrixHaarReader_eq_restricted n k)

theorem innerMatrixNormalizedCoordinate_sum_le (n : ℕ)
    (S : Finset (Fin (2 ^ n))) (y : IntervalLp 𝕜 operatorReductionL1Exponent) :
    (∑ k ∈ S, ‖lpHaarNormalizedCoordinate 𝕜 operatorReductionL1Exponent
      (some ⟨n, k⟩) y‖) ≤ ‖y‖ := by
  simp_rw [innerMatrixNormalizedCoordinate_eq_restricted]
  exact sum_norm_restrictedFunctional_le S (fun k => lpHaarCell n k)
    (fun _ => measurableSet_Ioc)
    (fun i _ j _ hij => lpHaarCell_disjoint_sameLevel n (fun h => hij (Fin.ext h)))
    (innerMatrixHaarReader 𝕜 n) (fun k _ => norm_innerMatrixHaarReader_le n k) y

end SurveyStatements.P5OperatorReduction

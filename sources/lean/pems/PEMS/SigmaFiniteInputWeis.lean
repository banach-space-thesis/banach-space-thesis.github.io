import PEMS.FiniteWeisBestApproximation
import PEMS.L1InputIsometryNoncompactness
import ThesisCommon.Analysis.L1DensityEquiv

/-! The actual real Weis norm identity and best approximation for
sigma-finite input and finite output measures. A proved positive finite
change of density supplies an onto L1 isometry; exact cutoff transport
preserves the original localized functional, not a replacement quantity. -/
noncomputable section
open MeasureTheory Set ThesisCommon
open scoped ENNReal NNReal ThesisCommon.PositiveOperatorOrder
namespace PEMS
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y} [SigmaFinite μ] [IsFiniteMeasure ν]

theorem weakEssentialNorm_eq_localized_real_sigmaFiniteInput
    (T : LOne ℝ μ →L[ℝ] LOne ℝ ν) :
    weakEssentialNorm T = localizedWeakNoncompactness T := by
  obtain ⟨g, hg, hgpos, hgfin⟩ := exists_positive_finite_density μ
  letI := hgfin
  let e := lOneWithDensityEquiv hg hgpos
  have h := weakEssentialNorm_eq_localized_real_finite
    (T.comp e.toLinearIsometry.toContinuousLinearMap)
  rwa [weakEssentialNorm_precomp_isometry, localizedWeakNoncompactness_precomp_isometry] at h

theorem weakEssentialNorm_abs_real_sigmaFiniteInput
    (T : LOne ℝ μ →L[ℝ] LOne ℝ ν) : weakEssentialNorm |T| = weakEssentialNorm T := by
  rw [weakEssentialNorm_eq_localized_real_sigmaFiniteInput, localizedWeakNoncompactness_abs,
    weakEssentialNorm_eq_localized_real_sigmaFiniteInput]

theorem weaklyCompact_abs_iff_real_sigmaFiniteInput (T : LOne ℝ μ →L[ℝ] LOne ℝ ν) :
    IsWeaklyCompactOperator |T| ↔ IsWeaklyCompactOperator T := by
  rw [← weakEssentialNorm_eq_zero_iff |T|, ← weakEssentialNorm_eq_zero_iff T,
    weakEssentialNorm_abs_real_sigmaFiniteInput]

theorem exists_real_sigmaFiniteInput_weaklyCompact_bestApproximation
    (T : LOne ℝ μ →L[ℝ] LOne ℝ ν) :
    ∃ W : LOne ℝ μ →L[ℝ] LOne ℝ ν, IsWeaklyCompactOperator W ∧
      ‖T - W‖ = weakEssentialNorm T := by
  obtain ⟨g, hg, hgpos, hgfin⟩ := exists_positive_finite_density μ
  letI := hgfin
  let e := lOneWithDensityEquiv hg hgpos
  let A := e.toLinearIsometry.toContinuousLinearMap
  let B := e.symm.toLinearIsometry.toContinuousLinearMap
  obtain ⟨W', hW, hnorm⟩ := exists_real_finite_weaklyCompact_bestApproximation (T.comp A)
  let W := W'.comp B
  refine ⟨W, hW.comp_right B, ?_⟩
  have herr : (T - W).comp A = T.comp A - W' := by
    apply ContinuousLinearMap.ext
    intro f
    change T (e f) - W' (e.symm (e f)) = T (e f) - W' f
    rw [LinearIsometryEquiv.symm_apply_apply]
  calc
    ‖T - W‖ = ‖(T - W).comp A‖ := ((T - W).opNorm_comp_linearIsometryEquiv e).symm
    _ = ‖T.comp A - W'‖ := by rw [herr]
    _ = weakEssentialNorm (T.comp A) := hnorm
    _ = weakEssentialNorm T := weakEssentialNorm_precomp_isometry e T

theorem real_sigmaFiniteInput_attained_weis_formula
    (T : LOne ℝ μ →L[ℝ] LOne ℝ ν) :
    ∃ W : LOne ℝ μ →L[ℝ] LOne ℝ ν, IsWeaklyCompactOperator W ∧
      weakEssentialNorm T = ‖T - W‖ ∧ ‖T - W‖ = localizedWeakNoncompactness T := by
  obtain ⟨W, hW, heq⟩ := exists_real_sigmaFiniteInput_weaklyCompact_bestApproximation T
  exact ⟨W, hW, heq.symm, heq.trans (weakEssentialNorm_eq_localized_real_sigmaFiniteInput T)⟩

theorem theorem_1_1_real_sigmaFiniteInput_finiteOutput
    (T : LOne ℝ μ →L[ℝ] LOne ℝ ν) : Theorem_1_1 μ ν T := by
  intro _ _
  exact real_sigmaFiniteInput_attained_weis_formula T

end PEMS

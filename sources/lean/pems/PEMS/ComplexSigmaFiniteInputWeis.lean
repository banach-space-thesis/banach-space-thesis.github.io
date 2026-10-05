import PEMS.ComplexFiniteWeisBestApproximation
import PEMS.SigmaFiniteInputWeis
import ThesisCommon.Analysis.L1DensityEquivRCLike

/-! The actual complex Weis norm identity and best approximation for
sigma-finite input and finite output measures. The positive finite density
change is a proved onto complex-linear isometry and preserves the original
localized functional exactly, including null measures and empty spaces. -/
noncomputable section
open MeasureTheory Set ThesisCommon
open scoped ENNReal NNReal
namespace PEMS
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y} [SigmaFinite μ] [IsFiniteMeasure ν]

theorem weakEssentialNorm_eq_localized_complex_sigmaFiniteInput
    (T : LOne ℂ μ →L[ℂ] LOne ℂ ν) :
    weakEssentialNorm T = localizedWeakNoncompactness T := by
  obtain ⟨g, hg, hgpos, hgfin⟩ := exists_positive_finite_density μ
  letI := hgfin
  let e := lOneWithDensityEquiv_rclike (𝕜 := ℂ) hg hgpos
  have h := weakEssentialNorm_eq_localized_complex_finite
    (T.comp e.toLinearIsometry.toContinuousLinearMap)
  rwa [weakEssentialNorm_precomp_isometry, localizedWeakNoncompactness_precomp_isometry] at h

theorem weakEssentialNorm_complex_modulus_sigmaFiniteInput
    (T : LOne ℂ μ →L[ℂ] LOne ℂ ν) :
    weakEssentialNorm (complexL1OperatorModulus T) = weakEssentialNorm T := by
  rw [weakEssentialNorm_eq_localized_real_sigmaFiniteInput,
    localizedWeakNoncompactness_complex_modulus, weakEssentialNorm_eq_localized_complex_sigmaFiniteInput]

theorem weaklyCompact_complex_modulus_iff_sigmaFiniteInput
    (T : LOne ℂ μ →L[ℂ] LOne ℂ ν) :
    IsWeaklyCompactOperator (complexL1OperatorModulus T) ↔ IsWeaklyCompactOperator T := by
  rw [← weakEssentialNorm_eq_zero_iff (complexL1OperatorModulus T),
    ← weakEssentialNorm_eq_zero_iff T, weakEssentialNorm_complex_modulus_sigmaFiniteInput]

theorem exists_complex_sigmaFiniteInput_weaklyCompact_bestApproximation
    (T : LOne ℂ μ →L[ℂ] LOne ℂ ν) :
    ∃ W : LOne ℂ μ →L[ℂ] LOne ℂ ν, IsWeaklyCompactOperator W ∧
      ‖T - W‖ = weakEssentialNorm T := by
  obtain ⟨g, hg, hgpos, hgfin⟩ := exists_positive_finite_density μ
  letI := hgfin
  let e := lOneWithDensityEquiv_rclike (𝕜 := ℂ) hg hgpos
  let A := e.toLinearIsometry.toContinuousLinearMap
  let B := e.symm.toLinearIsometry.toContinuousLinearMap
  obtain ⟨W', hW, hnorm⟩ := exists_complex_finite_weaklyCompact_bestApproximation (T.comp A)
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

theorem complex_sigmaFiniteInput_attained_weis_formula
    (T : LOne ℂ μ →L[ℂ] LOne ℂ ν) :
    ∃ W : LOne ℂ μ →L[ℂ] LOne ℂ ν, IsWeaklyCompactOperator W ∧
      weakEssentialNorm T = ‖T - W‖ ∧ ‖T - W‖ = localizedWeakNoncompactness T := by
  obtain ⟨W, hW, heq⟩ := exists_complex_sigmaFiniteInput_weaklyCompact_bestApproximation T
  exact ⟨W, hW, heq.symm, heq.trans (weakEssentialNorm_eq_localized_complex_sigmaFiniteInput T)⟩

theorem theorem_1_1_complex_sigmaFiniteInput_finiteOutput
    (T : LOne ℂ μ →L[ℂ] LOne ℂ ν) : Theorem_1_1 μ ν T := by
  intro _ _
  exact complex_sigmaFiniteInput_attained_weis_formula T

end PEMS

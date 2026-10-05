import PEMS.FiniteWeakCompactSolidity
import PEMS.FiniteWeisBestApproximation
import ThesisCommon.Analysis.ComplexL1WeakCompact
import ThesisCommon.Analysis.ComplexL1BandMembership

/-! Weak compactness and the actual complex operator modulus on finite
measure spaces. The proof uses real solidity and scalar restriction, and
does not depend on the complex Weis norm formula. -/
noncomputable section
open MeasureTheory ThesisCommon
open scoped ThesisCommon.PositiveOperatorOrder
namespace PEMS
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [IsFiniteMeasure ν]

theorem weaklyCompact_of_complex_modulus_real_finite
    (T : LOne ℂ μ →L[ℂ] LOne ℂ ν)
    (hT : IsWeaklyCompactOperator (complexL1OperatorModulus T)) :
    IsWeaklyCompactOperator T := by
  apply (weaklyCompact_complexL1_components_iff T).mpr
  exact ⟨weaklyCompact_of_abs_le_real_finite (abs_complexL1OperatorRe_le_modulus T) hT,
    weaklyCompact_of_abs_le_real_finite (abs_complexL1OperatorIm_le_modulus T) hT⟩

theorem weaklyCompact_complex_modulus_of_finite
    (T : LOne ℂ μ →L[ℂ] LOne ℂ ν) (hT : IsWeaklyCompactOperator T) :
    IsWeaklyCompactOperator (complexL1OperatorModulus T) := by
  have hr := (weaklyCompact_abs_iff_real_finite (complexL1OperatorRe T)).mpr
    hT.complexL1OperatorRe
  have hi := (weaklyCompact_abs_iff_real_finite (complexL1OperatorIm T)).mpr
    hT.complexL1OperatorIm
  apply weaklyCompact_of_abs_le_real_finite _ (hr.add hi)
  rw [abs_of_nonneg (show 0 ≤ complexL1OperatorModulus T from complexL1OperatorModulus_nonneg T)]
  exact complexL1OperatorModulus_le_abs_re_add_abs_im T

theorem weaklyCompact_complex_modulus_iff_finite
    (T : LOne ℂ μ →L[ℂ] LOne ℂ ν) :
    IsWeaklyCompactOperator (complexL1OperatorModulus T) ↔ IsWeaklyCompactOperator T :=
  ⟨weaklyCompact_of_complex_modulus_real_finite T, weaklyCompact_complex_modulus_of_finite T⟩

theorem weaklyCompact_of_complex_modulus_le_finite
    {T : LOne ℂ μ →L[ℂ] LOne ℂ ν} {H : LOne ℝ μ →L[ℝ] LOne ℝ ν}
    (hTH : complexL1OperatorModulus T ≤ H) (hH : IsWeaklyCompactOperator H) :
    IsWeaklyCompactOperator T := by
  apply weaklyCompact_of_complex_modulus_real_finite
  apply weaklyCompact_of_abs_le_real_finite _ hH
  rwa [abs_of_nonneg (show 0 ≤ complexL1OperatorModulus T from complexL1OperatorModulus_nonneg T)]

end PEMS

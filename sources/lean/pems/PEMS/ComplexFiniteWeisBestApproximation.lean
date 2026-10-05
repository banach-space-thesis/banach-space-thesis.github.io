import PEMS.ComplexFiniteWeakCompactModulus
import PEMS.ComplexFiniteWeisReduction
import PEMS.ComplexL1WeakNoncompactnessGeneral
import ThesisCommon.Analysis.ComplexIntegralPhaseLift

/-! Actual best weakly compact approximation for complex L1 operators on
arbitrary finite measure spaces. Positive real attainment is lifted through
the phase of the genuine integral kernel. The independent weak compactness
criterion and localized lower bound close the exact norm identity. -/
noncomputable section
open MeasureTheory Set ThesisCommon
open scoped ThesisCommon.PositiveOperatorOrder
namespace PEMS
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [IsFiniteMeasure ν]

theorem exists_complex_finite_weaklyCompact_modulus_bestApproximation
    (T : LOne ℂ μ →L[ℂ] LOne ℂ ν) :
    ∃ V : LOne ℂ μ →L[ℂ] LOne ℂ ν, IsWeaklyCompactOperator V ∧
      IsIntegralOperator V ∧
      complexL1OperatorModulus V ≤ integralBandProjection (complexL1OperatorModulus T) ∧
      ‖T - V‖ = weakEssentialNorm (complexL1OperatorModulus T) := by
  obtain ⟨H, hH, hH0, hHP, hnorm⟩ :=
    exists_positive_finite_weaklyCompact_bestApproximation (complexL1OperatorModulus T)
      (complexL1OperatorModulus_nonneg T)
  obtain ⟨V, hVI, hMV, _, herr⟩ := exists_complex_integral_phaseLift_norm T hH0 hHP
  refine ⟨V, weaklyCompact_of_complex_modulus_real_finite V ?_, hVI, ?_, herr.trans hnorm⟩
  · rwa [hMV]
  · rwa [hMV]

theorem weakEssentialNorm_eq_localized_complex_finite
    (T : LOne ℂ μ →L[ℂ] LOne ℂ ν) :
    weakEssentialNorm T = localizedWeakNoncompactness T := by
  obtain ⟨V, hV, _, _, herr⟩ := exists_complex_finite_weaklyCompact_modulus_bestApproximation T
  have hmod : weakEssentialNorm (complexL1OperatorModulus T) = localizedWeakNoncompactness T := by
    rw [weakEssentialNorm_eq_localized_real_finite, localizedWeakNoncompactness_complex_modulus]
  exact le_antisymm ((weakEssentialNorm_le T hV).trans_eq (herr.trans hmod))
    (localizedWeakNoncompactness_le_complex_weakEssentialNorm T)

theorem weakEssentialNorm_complex_modulus_finite
    (T : LOne ℂ μ →L[ℂ] LOne ℂ ν) :
    weakEssentialNorm (complexL1OperatorModulus T) = weakEssentialNorm T := by
  rw [weakEssentialNorm_eq_localized_real_finite, localizedWeakNoncompactness_complex_modulus,
    weakEssentialNorm_eq_localized_complex_finite]

theorem exists_complex_finite_weaklyCompact_bestApproximation
    (T : LOne ℂ μ →L[ℂ] LOne ℂ ν) :
    ∃ V : LOne ℂ μ →L[ℂ] LOne ℂ ν, IsWeaklyCompactOperator V ∧
      ‖T - V‖ = weakEssentialNorm T := by
  obtain ⟨V, hV, _, _, herr⟩ := exists_complex_finite_weaklyCompact_modulus_bestApproximation T
  exact ⟨V, hV, herr.trans (weakEssentialNorm_complex_modulus_finite T)⟩

theorem complex_finite_attained_weis_formula (T : LOne ℂ μ →L[ℂ] LOne ℂ ν) :
    ∃ V : LOne ℂ μ →L[ℂ] LOne ℂ ν, IsWeaklyCompactOperator V ∧
      weakEssentialNorm T = ‖T - V‖ ∧ ‖T - V‖ = localizedWeakNoncompactness T := by
  obtain ⟨V, hV, herr⟩ := exists_complex_finite_weaklyCompact_bestApproximation T
  exact ⟨V, hV, herr.symm, herr.trans (weakEssentialNorm_eq_localized_complex_finite T)⟩

theorem theorem_1_1_complex_finite (T : LOne ℂ μ →L[ℂ] LOne ℂ ν) :
    Theorem_1_1 μ ν T := by
  intro _ _
  exact complex_finite_attained_weis_formula T

theorem complex_finite_weis_norm_formula
    {k : X × Y → ℂ} (S K : LOne ℂ μ →L[ℂ] LOne ℂ ν)
    (hS : IsComplexSingularOperator S) (hk : IsIntegralKernel k K) :
    weakEssentialNorm (S + K) = localizedWeakNoncompactness (S + K) ∧
    weakEssentialNorm (S + K) =
      sInf (Set.range (fun j : ℕ => ‖S + hk.complexTruncatedOperator j‖)) := by
  have h := weakEssentialNorm_eq_localized_complex_finite (S + K)
  exact ⟨h, h.trans (complex_finite_truncationInf_eq_localized S K hS hk).symm⟩

theorem complex_finite_weis_essSup_formula
    {k : X × Y → ℂ} (S K : LOne ℂ μ →L[ℂ] LOne ℂ ν)
    (hS : IsComplexSingularOperator S) (hk : IsIntegralKernel k K) :
    weakEssentialNorm (S + K) = localizedWeakNoncompactness (S + K) ∧
    weakEssentialNorm (S + K) = sInf (Set.range (fun j : ℕ =>
      essSup (fun x => positiveAdjointOne (complexL1OperatorModulus S)
        (complexL1OperatorModulus_nonneg S) x +
        ∫ y, ‖truncatedKernel (j : ℝ) k (x, y)‖ ∂ν) μ)) := by
  have h := weakEssentialNorm_eq_localized_complex_finite (S + K)
  exact ⟨h, h.trans (complex_finite_localized_eq_essSup S K hS hk)⟩

end PEMS

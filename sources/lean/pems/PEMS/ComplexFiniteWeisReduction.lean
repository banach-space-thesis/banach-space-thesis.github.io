import PEMS.ComplexL1WeakNoncompactnessModulus
import PEMS.FiniteWeisFormula
import PEMS.SingularFiniteMeasure
import ThesisCommon.Analysis.ComplexIntegralKernelTruncation

/-! The real finite-measure formula transfers exactly to the localized
functional and truncation norms of a complex operator. The weak-essential-
norm comparison for complex scalars is an independent compactness step. -/
noncomputable section
open MeasureTheory Set ThesisCommon
open scoped ThesisCommon.PositiveOperatorOrder
namespace PEMS
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [IsFiniteMeasure ν]

theorem complex_singular_finite_alpha_eq_norm
    (S : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν) (hS : IsComplexSingularOperator S) :
    alphaTheta S univ = ‖S‖ := by
  rw [← alphaTheta_complex_modulus S univ MeasurableSet.univ,
    singular_finite_alpha_eq_norm _ hS.modulus, norm_complexL1OperatorModulus]

theorem complex_singular_finite_localized_eq_norm
    (S : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν) (hS : IsComplexSingularOperator S) :
    localizedWeakNoncompactness S = ‖S‖ := by
  rw [localizedWeakNoncompactness_eq_alphaTheta_univ]
  exact complex_singular_finite_alpha_eq_norm S hS

theorem complex_finite_truncationInf_eq_localized
    {k : X × Y → ℂ} (S K : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν)
    (hS : IsComplexSingularOperator S) (hk : IsIntegralKernel k K) :
    sInf (Set.range (fun j : ℕ => ‖S + hk.complexTruncatedOperator j‖)) =
      localizedWeakNoncompactness (S + K) := by
  obtain ⟨hphi, hnorm⟩ := real_finite_weis_norm_formula
    (complexL1OperatorModulus S) (complexL1OperatorModulus K) hS.modulus hk.complex_modulus
  have hmod := complex_singular_integral_modulus_add hS (show IsIntegralOperator K from ⟨k, hk⟩)
  have hphi' : localizedWeakNoncompactness
      (complexL1OperatorModulus S + complexL1OperatorModulus K) =
      localizedWeakNoncompactness (S + K) := by
    rw [← hmod, localizedWeakNoncompactness_complex_modulus]
  rw [show (fun j : ℕ => ‖S + hk.complexTruncatedOperator j‖) =
      (fun j : ℕ => ‖complexL1OperatorModulus S + hk.complex_modulus.truncatedOperator j‖) from
    funext fun j => complex_singular_truncated_norm_modulus hS hk j]
  exact hnorm.symm.trans (hphi.trans hphi')

theorem complex_finite_truncationInf_le_localized
    {k : X × Y → ℂ} (S K : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν)
    (hS : IsComplexSingularOperator S) (hk : IsIntegralKernel k K) :
    sInf (Set.range (fun j : ℕ => ‖S + hk.complexTruncatedOperator j‖)) ≤
      localizedWeakNoncompactness (S + K) :=
  (complex_finite_truncationInf_eq_localized S K hS hk).le

theorem complex_singular_truncated_norm_eq_essSup [IsFiniteMeasure μ]
    {k : X × Y → ℂ} {S K : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν}
    (hS : IsComplexSingularOperator S) (hk : IsIntegralKernel k K) (r : ℝ) :
    ‖S + hk.complexTruncatedOperator r‖ =
      essSup (fun x => positiveAdjointOne (complexL1OperatorModulus S)
        (complexL1OperatorModulus_nonneg S) x +
        ∫ y, ‖truncatedKernel r k (x, y)‖ ∂ν) μ := by
  rw [complex_singular_truncated_norm_modulus hS hk r]
  have h := singular_truncated_norm_eq_essSup_adjoint_column hk.complex_modulus hS.modulus r
  simpa only [abs_of_nonneg (show 0 ≤ complexL1OperatorModulus S from
    complexL1OperatorModulus_nonneg S), truncatedKernel_norm, abs_of_nonneg (norm_nonneg _)] using h

theorem complex_finite_localized_eq_essSup
    {k : X × Y → ℂ} (S K : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν)
    (hS : IsComplexSingularOperator S) (hk : IsIntegralKernel k K) :
    localizedWeakNoncompactness (S + K) = sInf (Set.range (fun j : ℕ =>
      essSup (fun x => positiveAdjointOne (complexL1OperatorModulus S)
        (complexL1OperatorModulus_nonneg S) x +
        ∫ y, ‖truncatedKernel (j : ℝ) k (x, y)‖ ∂ν) μ)) := by
  rw [← complex_finite_truncationInf_eq_localized S K hS hk]
  exact congrArg sInf (congrArg Set.range (funext fun j =>
    complex_singular_truncated_norm_eq_essSup hS hk j))

end PEMS

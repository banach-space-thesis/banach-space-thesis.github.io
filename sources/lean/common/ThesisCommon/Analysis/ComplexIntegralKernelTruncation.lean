import ThesisCommon.Analysis.ComplexIntegralKernelModulus
import ThesisCommon.Analysis.ComplexIntegralOperatorBand
import ThesisCommon.Analysis.IntegralKernelDomination

/-! Genuine complex kernel truncations and their real moduli. These use
the sharp derived column bound and the proved complex integral band. -/
noncomputable section
open MeasureTheory Set
open scoped ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}

omit [MeasurableSpace X] [MeasurableSpace Y] in
theorem truncatedKernel_norm (k : X × Y → ℂ) (r : ℝ) :
    truncatedKernel r (fun z => ‖k z‖) = fun z => ‖truncatedKernel r k z‖ := by
  funext z
  by_cases hz : r ≤ ‖k z‖ <;>
    simp [truncatedKernel, Real.norm_of_nonneg (norm_nonneg _), hz]

variable [SigmaFinite μ] [SigmaFinite ν]

theorem IsComplexSingularOperator.modulus {S : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν}
    (hS : IsComplexSingularOperator S) : IsSingularOperator (complexL1OperatorModulus S) := by
  apply (integralBandProjection_eq_zero_iff _).mp
  have h := congrArg complexL1OperatorModulus ((complexIntegralBandProjection_eq_zero_iff S).mpr hS)
  simpa only [complexIntegralBandProjection_modulus, complexL1OperatorModulus_zero] using h

variable {k : X × Y → ℂ} {K : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν}

def IsIntegralKernel.complexTruncatedOperator (hk : IsIntegralKernel k K) (r : ℝ) :
    Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν :=
  truncatedKernelOperator hk.measurable hk.hasKernelBound_complex r

theorem IsIntegralKernel.complexTruncatedOperator_represents (hk : IsIntegralKernel k K) (r : ℝ) :
    IsIntegralKernel (truncatedKernel r k) (hk.complexTruncatedOperator r) :=
  isIntegralKernel_truncatedKernelOperator _ _ _

theorem IsIntegralKernel.complex_modulus_truncatedOperator [IsFiniteMeasure μ]
    (hk : IsIntegralKernel k K) (r : ℝ) :
    complexL1OperatorModulus (hk.complexTruncatedOperator r) =
      hk.complex_modulus.truncatedOperator r := by
  apply IsIntegralKernel.unique (k := truncatedKernel r (fun z => ‖k z‖))
  · rw [truncatedKernel_norm]
    exact (hk.complexTruncatedOperator_represents r).complex_modulus
  · exact hk.complex_modulus.truncatedOperator_represents r

theorem complex_singular_truncated_norm_modulus [IsFiniteMeasure μ]
    {S : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν} (hS : IsComplexSingularOperator S)
    (hk : IsIntegralKernel k K) (r : ℝ) :
    ‖S + hk.complexTruncatedOperator r‖ =
      ‖complexL1OperatorModulus S + hk.complex_modulus.truncatedOperator r‖ := by
  rw [← norm_complexL1OperatorModulus,
    complex_singular_integral_modulus_add hS ⟨_, hk.complexTruncatedOperator_represents r⟩,
    hk.complex_modulus_truncatedOperator]

end ThesisCommon

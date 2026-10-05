import ThesisCommon.Analysis.ComplexKernelPhaseLift

/-! The exact phase lift needed for complex best approximation. A positive
integral fragment of |T| is lifted using the actual integral kernel of the
integral part, while the singular part stays disjoint from the correction. -/
noncomputable section
open MeasureTheory
open scoped ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y} [SigmaFinite μ] [SigmaFinite ν]

theorem exists_complex_integral_phaseLift (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν)
    {H : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν} (hH : 0 ≤ H)
    (hHP : H ≤ integralBandProjection (complexL1OperatorModulus T)) :
    ∃ V : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν, IsIntegralOperator V ∧
      complexL1OperatorModulus V = H ∧
      complexL1OperatorModulus (T-V) = complexL1OperatorModulus T-H := by
  have hHI : IsIntegralOperator H := integralOperatorOrderClosedIdeal.nonneg_le_mem
    (integralBandProjection_isIntegral (complexL1OperatorModulus T)) hH hHP
  obtain ⟨h,hh⟩ := hHI
  obtain ⟨k,hk⟩ := complexIntegralBandProjection_isIntegral T
  have hHK : H ≤ complexL1OperatorModulus (complexIntegralBandProjection T) := by
    rwa [complexIntegralBandProjection_modulus]
  obtain ⟨V,hV,hMV,herr⟩ := hk.exists_complex_phaseLift hh hH hHK
  refine ⟨V,hV,hMV,?_⟩
  have hsubI : IsIntegralOperator (complexIntegralBandProjection T-V) := by
    obtain ⟨v,hv⟩ := hV
    exact ⟨_,hk.sub_rclike hv⟩
  have he := complex_singular_integral_modulus_add
    (complexIntegralBandProjection_residual_singular T) hsubI
  rw [sub_add_sub_cancel,herr,complexIntegralBandProjection_residual_modulus,
    complexIntegralBandProjection_modulus] at he
  calc
    complexL1OperatorModulus (T-V) =
        (complexL1OperatorModulus T-integralBandProjection (complexL1OperatorModulus T)) +
          (integralBandProjection (complexL1OperatorModulus T)-H) := he
    _ = complexL1OperatorModulus T-H := by abel

theorem exists_complex_integral_phaseLift_norm (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν)
    {H : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν} (hH : 0 ≤ H)
    (hHP : H ≤ integralBandProjection (complexL1OperatorModulus T)) :
    ∃ V : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν, IsIntegralOperator V ∧
      complexL1OperatorModulus V = H ∧ ‖V‖ = ‖H‖ ∧ ‖T-V‖ = ‖complexL1OperatorModulus T-H‖ := by
  obtain ⟨V,hV,hMV,herr⟩ := exists_complex_integral_phaseLift T hH hHP
  refine ⟨V,hV,hMV,?_,?_⟩
  · rw [← norm_complexL1OperatorModulus,hMV]
  · rw [← norm_complexL1OperatorModulus,herr]

end ThesisCommon

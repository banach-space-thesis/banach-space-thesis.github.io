import ThesisCommon.Analysis.GowersMaureyWienerRepresentativeProduct
import ThesisCommon.Analysis.WienerMapPrimeness
import ThesisCommon.Analysis.WienerMaximalIdeals

/-! Consequences of the actual constructed Wiener representative. All
operator approximation hypotheses remain visible: their discharge is the
still separate source approximation theorem. No identification of the
whole strictly singular ideal is needed for these consequences. -/
noncomputable section
namespace ThesisCommon.GowersMaurey

theorem wienerRepresentative_kernel_strictlySingular (D : ConstructionData ℂ)
    (happrox : ∀ T : ShiftSpace D →L[ℂ] ShiftSpace D, IsFiniteSpreadApproximable D T)
    (T : ShiftSpace D →L[ℂ] ShiftSpace D)
    (hT : wienerRepresentative D happrox T = 0) : IsStrictlySingularOperator T :=
  isStrictlySingularOperator_of_spaceOperatorSeminorm_zero D T
    ((wienerRepresentative_eq_zero_iff D happrox T).mp hT)

theorem shiftSpace_not_hasPFP_of_finiteSpreadApproximation (D : ConstructionData ℂ)
    (happrox : ∀ T : ShiftSpace D →L[ℂ] ShiftSpace D, IsFiniteSpreadApproximable D T) :
    ¬ HasPFP ℂ (ShiftSpace D) :=
  not_hasPFP_of_wiener_quotient_map (wienerRepresentative D happrox).toLinearMap
    (wienerRepresentative_surjective D happrox) (wienerRepresentative_id D happrox)
    (wienerRepresentative_comp D happrox)

theorem shiftSpace_projection_finite_or_finiteComplement_of_finiteSpreadApproximation
    (D : ConstructionData ℂ)
    (happrox : ∀ T : ShiftSpace D →L[ℂ] ShiftSpace D, IsFiniteSpreadApproximable D T)
    (P : ShiftSpace D →L[ℂ] ShiftSpace D) (hP : P.comp P = P) :
    FiniteDimensional ℂ (LinearMap.range P.toLinearMap) ∨
      FiniteDimensional ℂ
        (LinearMap.range (ContinuousLinearMap.id ℂ (ShiftSpace D) - P).toLinearMap) :=
  projection_finite_or_finiteComplement_of_wiener_map_kernel_le
    (wienerRepresentative D happrox).toLinearMap
    (wienerRepresentative_kernel_strictlySingular D happrox)
    (wienerRepresentative_id D happrox) (wienerRepresentative_comp D happrox) P hP

theorem shiftSpace_prime_of_finiteSpreadApproximation (D : ConstructionData ℂ)
    (happrox : ∀ T : ShiftSpace D →L[ℂ] ShiftSpace D, IsFiniteSpreadApproximable D T) :
    IsPrimeBanachSpace ℂ (ShiftSpace D) :=
  (shiftSpace_everyHyperplane D).isPrime_of_wienerMap
    (wienerRepresentative D happrox).toLinearMap
    (wienerRepresentative_kernel_strictlySingular D happrox)
    (wienerRepresentative_id D happrox) (wienerRepresentative_comp D happrox)

theorem shiftSpace_primary_of_finiteSpreadApproximation (D : ConstructionData ℂ)
    (happrox : ∀ T : ShiftSpace D →L[ℂ] ShiftSpace D, IsFiniteSpreadApproximable D T) :
    IsPrimary ℂ (ShiftSpace D) :=
  (shiftSpace_prime_of_finiteSpreadApproximation D happrox).isPrimary
    (shiftSpace_infiniteDimensional D)

theorem shiftSpace_continuum_le_maximalIdeals_of_finiteSpreadApproximation
    (D : ConstructionData ℂ)
    (happrox : ∀ T : ShiftSpace D →L[ℂ] ShiftSpace D, IsFiniteSpreadApproximable D T) :
    Cardinal.continuum ≤ Cardinal.mk
      {J : TwoSidedIdeal (ShiftSpace D →L[ℂ] ShiftSpace D) // IsCoatom J} :=
  continuum_le_maximalIdeals_of_wiener_quotient_map
    (wienerRepresentative D happrox).toLinearMap
    (wienerRepresentative_surjective D happrox) (wienerRepresentative_id D happrox)
    (wienerRepresentative_comp D happrox)

end ThesisCommon.GowersMaurey

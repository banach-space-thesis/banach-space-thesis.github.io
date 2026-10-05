import ThesisCommon.Analysis.GowersMaureyWienerQuotient
import ThesisCommon.Analysis.GowersMaureyStrictlySingularConverse
import ThesisCommon.Analysis.GowersMaureyStrictlySingularIdeal
import ThesisCommon.Analysis.WienerIdealCardinality

/-! The exact strictly singular quotient, retaining the genuine finite-spread
approximation input. Both kernel inclusions, the actual quotient norm,
the unit and literal convolution are now discharged. -/
noncomputable section
namespace ThesisCommon.GowersMaurey

theorem spaceOperatorSeminormIdeal_eq_strictlySingularIdeal
    (D : ConstructionData ℂ)
    (happrox : ∀ T : ShiftSpace D →L[ℂ] ShiftSpace D, IsFiniteSpreadApproximable D T) :
    spaceOperatorSeminormIdeal D happrox = strictlySingularIdeal D := by
  ext T
  rw [mem_spaceOperatorSeminormIdeal, mem_strictlySingularIdeal]
  exact spaceOperatorSeminorm_zero_iff_strictlySingular_of_approximable (happrox T)

theorem hasStrictlySingularWienerQuotient_of_finiteSpreadApproximation
    (D : ConstructionData ℂ)
    (happrox : ∀ T : ShiftSpace D →L[ℂ] ShiftSpace D, IsFiniteSpreadApproximable D T) :
    HasStrictlySingularWienerQuotient ℂ (ShiftSpace D) := by
  refine ⟨spaceOperatorSeminormIdeal D happrox, ?_, inferInstance,
    (wienerQuotientIsometryEquiv D happrox).toContinuousLinearEquiv, ?_, ?_⟩
  · intro T
    rw [mem_spaceOperatorSeminormIdeal]
    exact spaceOperatorSeminorm_zero_iff_strictlySingular_of_approximable (happrox T)
  · exact wienerQuotientIsometryEquiv_unit D happrox
  · intro S T n
    exact congrArg (fun a : WienerSequences ℂ => a n)
      (wienerQuotientIsometryEquiv_comp D happrox S T)

theorem shiftSpace_hasContinuumManyMaximalOperatorIdeals_of_finiteSpreadApproximation
    (D : ConstructionData ℂ)
    (happrox : ∀ T : ShiftSpace D →L[ℂ] ShiftSpace D, IsFiniteSpreadApproximable D T)
    (hall : AllMaximalIdealsContainStrictlySingular ℂ (ShiftSpace D)) :
    HasContinuumManyMaximalOperatorIdeals ℂ (ShiftSpace D) :=
  HasStrictlySingularWienerQuotient.hasContinuumManyMaximalOperatorIdeals
    (hasStrictlySingularWienerQuotient_of_finiteSpreadApproximation D happrox) hall

end ThesisCommon.GowersMaurey

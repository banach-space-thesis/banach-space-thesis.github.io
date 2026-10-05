import ThesisCommon.Analysis.GowersMaureyMaximalIdeals
import ThesisCommon.Analysis.GowersMaureyStrictlySingularWienerQuotient

/-! Exact cardinality of all algebraically maximal operator ideals, using
the proved containment of the actual strictly singular ideal. Only the
source's finite-spread approximation input remains conditional. -/
noncomputable section
namespace ThesisCommon.GowersMaurey

theorem hasContinuumManyMaximalOperatorIdeals_of_finiteSpreadApproximation
    (D : ConstructionData ℂ)
    (happrox : ∀ T : ShiftSpace D →L[ℂ] ShiftSpace D, IsFiniteSpreadApproximable D T) :
    HasContinuumManyMaximalOperatorIdeals ℂ (ShiftSpace D) :=
  shiftSpace_hasContinuumManyMaximalOperatorIdeals_of_finiteSpreadApproximation
    D happrox (allMaximalIdealsContainStrictlySingular D)

end ThesisCommon.GowersMaurey

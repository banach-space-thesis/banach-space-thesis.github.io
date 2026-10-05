import PFP.GowersMaureyStatements
import ThesisCommon.Analysis.GowersMaureyMaximalIdealCardinality
import ThesisCommon.Analysis.GowersMaureyWienerMapConsequences

/-! The exact Example 7.1 conclusion reduced to the remaining genuine
finite-spread approximation theorem on every bounded operator. This is a
conditional assembly and does not discharge that analytic input. -/
noncomputable section
namespace PFP
open ThesisCommon ThesisCommon.GowersMaurey

theorem example_7_1_of_finiteSpreadApproximation (D : ConstructionData ℂ)
    (happrox : ∀ T : ShiftSpace D →L[ℂ] ShiftSpace D, IsFiniteSpreadApproximable D T) :
    Example_7_1 D :=
  ⟨shiftSpace_prime_of_finiteSpreadApproximation D happrox,
    shiftSpace_primary_of_finiteSpreadApproximation D happrox,
    hasStrictlySingularWienerQuotient_of_finiteSpreadApproximation D happrox,
    allMaximalIdealsContainStrictlySingular D,
    hasContinuumManyMaximalOperatorIdeals_of_finiteSpreadApproximation D happrox,
    shiftSpace_not_hasPFP_of_finiteSpreadApproximation D happrox⟩

end PFP

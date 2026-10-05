import ThesisCommon.Analysis.GowersMaureyOperatorApproximation
import ThesisCommon.Analysis.GowersMaureyMaximalIdealCardinality
import ThesisCommon.Analysis.GowersMaureyWienerMapConsequences

/-! Unconditional consequences for the actual shift-generated Gowers--Maurey
space. The finite-spread representation premise is discharged by its proved
operator-approximation theorem. These results apply to every admissible
construction, including the fixed named complex space. -/
noncomputable section
namespace ThesisCommon.GowersMaurey

theorem spaceOperatorSeminorm_zero_iff_strictlySingular
    (D : ConstructionData ℂ) (T : ShiftSpace D →L[ℂ] ShiftSpace D) :
    spaceOperatorSeminorm D T = 0 ↔ IsStrictlySingularOperator T :=
  spaceOperatorSeminorm_zero_iff_strictlySingular_of_approximable (finiteSpreadApproximable D T)

theorem shiftSpace_hasStrictlySingularWienerQuotient (D : ConstructionData ℂ) :
    HasStrictlySingularWienerQuotient ℂ (ShiftSpace D) :=
  hasStrictlySingularWienerQuotient_of_finiteSpreadApproximation D (finiteSpreadApproximable D)

theorem shiftSpace_prime (D : ConstructionData ℂ) : IsPrimeBanachSpace ℂ (ShiftSpace D) :=
  shiftSpace_prime_of_finiteSpreadApproximation D (finiteSpreadApproximable D)

theorem shiftSpace_primary (D : ConstructionData ℂ) : IsPrimary ℂ (ShiftSpace D) :=
  shiftSpace_primary_of_finiteSpreadApproximation D (finiteSpreadApproximable D)

theorem shiftSpace_not_hasPFP (D : ConstructionData ℂ) : ¬ HasPFP ℂ (ShiftSpace D) :=
  shiftSpace_not_hasPFP_of_finiteSpreadApproximation D (finiteSpreadApproximable D)

theorem shiftSpace_hasContinuumManyMaximalOperatorIdeals (D : ConstructionData ℂ) :
    HasContinuumManyMaximalOperatorIdeals ℂ (ShiftSpace D) :=
  hasContinuumManyMaximalOperatorIdeals_of_finiteSpreadApproximation D (finiteSpreadApproximable D)

theorem shiftSpace_projection_finite_or_finiteComplement
    (D : ConstructionData ℂ) (P : ShiftSpace D →L[ℂ] ShiftSpace D) (hP : P.comp P = P) :
    FiniteDimensional ℂ (LinearMap.range P.toLinearMap) ∨
      FiniteDimensional ℂ
        (LinearMap.range (ContinuousLinearMap.id ℂ (ShiftSpace D) - P).toLinearMap) :=
  shiftSpace_projection_finite_or_finiteComplement_of_finiteSpreadApproximation D
    (finiteSpreadApproximable D) P hP

end ThesisCommon.GowersMaurey

import SurveyStatements.P2Calkin
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! The finite-dimensional case of the source's nonrepresentation conclusion. -/

noncomputable section
set_option autoImplicit false

namespace SurveyStatements.P2
universe u v
variable (X : Type v) [NormedAddCommGroup X] [NormedSpace ℂ X]
  [FiniteDimensional ℂ X]

theorem isCompactOperator_of_finiteDimensional (T : BoundedOperators X) :
    IsCompactOperator T := by
  letI : ProperSpace X := FiniteDimensional.proper ℂ X
  apply (isCompactOperator_iff_isCompact_closure_image_closedBall
    T.toLinearMap zero_lt_one).mpr
  exact ((isCompact_closedBall (0 : X) 1).image T.continuous).closure

@[simp] theorem calkinQuotient_eq_zero_of_finiteDimensional (T : BoundedOperators X) :
    calkinQuotient X T = 0 :=
  (calkinQuotient_eq_zero_iff X T).mpr (isCompactOperator_of_finiteDimensional X T)

/-- No nonzero unital algebra is the Calkin algebra of a finite-dimensional space. -/
theorem no_calkinIso_of_finiteDimensional (A : Type u) [NormedRing A]
    [NormedAlgebra ℂ A] [Nontrivial A] :
    ¬ Nonempty (CalkinBanachAlgebraIso X A) := by
  rintro ⟨e⟩
  have hone := e.map_one_representative
  rw [calkinQuotient_eq_zero_of_finiteDimensional] at hone
  have hzero : e.toContinuousLinearEquiv 0 = 0 := e.toContinuousLinearEquiv.map_zero
  exact zero_ne_one (hzero.symm.trans hone)

end SurveyStatements.P2

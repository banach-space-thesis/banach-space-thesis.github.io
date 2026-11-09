import SurveyStatements.P2CalkinMatrixUnits
import SurveyStatements.P2AbsorbedRows
import SurveyStatements.P2MatrixEllOneLifts
import SurveyStatements.P2EllOneSynthesis

/-! The bounded first row produces an actual separable-range noncompact operator. -/

noncomputable section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
open scoped BigOperators ENNReal
open TopologicalSpace

namespace SurveyStatements.P2
universe v
variable (X : Type v) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem false_of_oppositeShift_calkinIso
    (e : CalkinBanachAlgebraIso X (ShiftQuotient LargeAlphabet)ᵐᵒᵖ)
    (hX : ¬ SeparableSpace X)
    (hsimple : ∀ J : TwoSidedIdeal (Calkin X), J = ⊥ ∨ J = ⊤) : False := by
  classical
  let D := ‖e.toContinuousLinearEquiv.symm.toContinuousLinearMap‖
  have hD : 0 ≤ D := norm_nonneg _
  let E : ℕ → ℕ → BoundedOperators X := fun i j =>
    boundedCalkinLift X (transportedMatrixUnit X e i j)
  have hqE : ∀ i j, calkinQuotient X (E i j) = transportedMatrixUnit X e i j :=
    fun i j => calkinQuotient_boundedCalkinLift X _
  have hE : ∀ i j k l, IsCompactOperator (matrixRelationError E i j k l) := by
    intro i j k l
    apply (calkinQuotient_eq_zero_iff X _).mp
    change (CompactOperators X).mkQ
      (E i j * E k l - if j = k then E i l else 0) = 0
    rw [map_sub]
    change calkinQuotient X (E i j * E k l) -
      calkinQuotient X (if j = k then E i l else 0) = 0
    rw [calkinQuotient_mul, hqE, hqE, transportedMatrixUnit_mul]
    split_ifs
    · exact sub_eq_zero.mpr (hqE i l).symm
    · simp only [calkinQuotient, Submodule.Quotient.mk_zero, sub_self]
  have hEnorm : ∀ i j, ‖E i j‖ ≤ D + 1 := by
    intro i j
    exact (norm_boundedCalkinLift_lt X _).le.trans
      (add_le_add_right (norm_transportedMatrixUnit_le X e i j) 1)
  have hrow : ∀ (F : Finset ℕ) (a : F → ℂ),
      ‖calkinQuotient X (finiteRowRepresentative E F a)‖ ≤ D * ‖a‖ := by
    intro F a
    change ‖(CompactOperators X).mkQ (∑ j : F, a j • E 0 j.val)‖ ≤ D * ‖a‖
    simp only [map_sum, map_smul]
    change ‖∑ j : F, a j • calkinQuotient X (E 0 j.val)‖ ≤ D * ‖a‖
    simp only [hqE]
    exact norm_sum_transportedMatrixUnit_finite_row_le X e 0 F a
  let K := rationalRowCorrection E D hD hrow
  have hK : ∀ c, IsCompactOperator (K c) := rationalRowCorrection_compact E D hD hrow
  have hKnorm : ∀ c : RationalFiniteCoefficients,
      ‖finiteRowRepresentative E c.1 (fun j => rationalComplex (c.2 j)) + K c‖ ≤
        (D + 1) * ‖fun j => rationalComplex (c.2 j)‖ :=
    rationalRowCorrection_norm_le E D hD hrow
  let N := matrixErrorAbsorption E hE K hK
  letI : IsClosed (N.subspace : Set X) := N.closed
  have hNne : absorbedMatrixUnit N 0 0 ≠ 0 :=
    absorbedMatrixUnit_diagonal_ne_zero N hX hsimple 0 (by
      rw [hqE]
      exact transportedMatrixUnit_diagonal_ne_zero X e 0)
  have hNrow : ∀ (F : Finset ℕ) (a : ℕ → ℂ), (∀ j ∈ F, ‖a j‖ ≤ 1) →
      ‖∑ j ∈ F, a j • absorbedMatrixUnit N 0 j‖ ≤ D + 1 :=
    fun F a ha => absorbedMatrixUnit_unit_row_bound N (D + 1)
      (add_nonneg hD zero_le_one) hKnorm F a ha
  have hNcol : ∀ i, ‖absorbedMatrixUnit N i 0‖ ≤ D + 1 := fun i =>
    (norm_quotientEndomorphism_le N.subspace (E i 0) (N.invariant i 0)).trans (hEnorm i 0)
  obtain ⟨Θ, x, B, hB, hx, hΘ⟩ := exists_ellOne_unit_lifts_of_matrixUnits N.subspace
    (absorbedMatrixUnit N) (absorbedMatrixUnit_mul N) hNne (D + 1) (D + 1)
    (add_nonneg hD zero_le_one) (add_nonneg hD zero_le_one) hNrow hNcol
  obtain ⟨T, hsep, hnoncompact⟩ :=
    exists_separable_noncompact_of_ellOne_unit_lifts Θ x B hB hx hΘ
  exact hnoncompact (compact_of_separableRange_of_simple_calkin X hX hsimple hsep)

end SurveyStatements.P2

import SurveyStatements.P2MatrixNonrepresentation

/-! The compact-quotient version of Proposition 4.3, with the matrix units
arbitrary and only the stated row/column estimates. The earlier survey proof
was specialized to its particular opposite-shift algebra and simplicity.
-/

noncomputable section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
open scoped BigOperators
open TopologicalSpace

namespace NonCalkinAlgebra
open SurveyStatements.P2
universe v
variable (X : Type v) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem controlled_calkin_matrix_units_impossible
    (hcompact : ∀ T : BoundedOperators X,
      IsSeparable (Set.range T) → IsCompactOperator T)
    (e : ℕ → ℕ → Calkin X)
    (hmul : ∀ i j k l, e i j * e k l = if j = k then e i l else 0)
    (hne : e 0 0 ≠ 0)
    (Cr Cc : ℝ) (hCr : 0 ≤ Cr) (hCc : 0 ≤ Cc)
    (hrow : ∀ (F : Finset ℕ) (a : F → ℂ),
      ‖∑ j : F, a j • e 0 j.val‖ ≤ Cr * ‖a‖)
    (hcolumn : ∀ i, ‖e i 0‖ ≤ Cc) : False := by
  classical
  let E : ℕ → ℕ → BoundedOperators X := fun i j => boundedCalkinLift X (e i j)
  have hqE : ∀ i j, calkinQuotient X (E i j) = e i j :=
    fun i j => calkinQuotient_boundedCalkinLift X _
  have hE : ∀ i j k l, IsCompactOperator (matrixRelationError E i j k l) := by
    intro i j k l
    apply (calkinQuotient_eq_zero_iff X _).mp
    change (CompactOperators X).mkQ (E i j * E k l - if j = k then E i l else 0) = 0
    rw [map_sub]
    change calkinQuotient X (E i j * E k l) -
      calkinQuotient X (if j = k then E i l else 0) = 0
    rw [calkinQuotient_mul, hqE, hqE, hmul]
    split_ifs
    · exact sub_eq_zero.mpr (hqE i l).symm
    · simp only [calkinQuotient, Submodule.Quotient.mk_zero, sub_self]
  have hquotrow : ∀ (F : Finset ℕ) (a : F → ℂ),
      ‖calkinQuotient X (finiteRowRepresentative E F a)‖ ≤ Cr * ‖a‖ := by
    intro F a
    change ‖(CompactOperators X).mkQ (∑ j : F, a j • E 0 j.val)‖ ≤ Cr * ‖a‖
    simp only [map_sum, map_smul]
    change ‖∑ j : F, a j • calkinQuotient X (E 0 j.val)‖ ≤ Cr * ‖a‖
    simp only [hqE]
    exact hrow F a
  let K := rationalRowCorrection E Cr hCr hquotrow
  have hK : ∀ c, IsCompactOperator (K c) := rationalRowCorrection_compact E Cr hCr hquotrow
  have hKnorm : ∀ c : RationalFiniteCoefficients,
      ‖finiteRowRepresentative E c.1 (fun j => rationalComplex (c.2 j)) + K c‖ ≤
        (Cr + 1) * ‖fun j => rationalComplex (c.2 j)‖ :=
    rationalRowCorrection_norm_le E Cr hCr hquotrow
  let N := matrixErrorAbsorption E hE K hK
  letI : IsClosed (N.subspace : Set X) := N.closed
  have hNne : absorbedMatrixUnit N 0 0 ≠ 0 := by
    intro hz
    have hsep : IsSeparable (Set.range (E 0 0)) := by
      apply N.separable.mono
      rintro y ⟨x, rfl⟩
      apply (Submodule.Quotient.mk_eq_zero _).mp
      have h := congrArg (fun T : (X ⧸ N.subspace) →L[ℂ] (X ⧸ N.subspace) =>
        T (N.subspace.mkQ x)) hz
      simpa only [absorbedMatrixUnit, quotientEndomorphism_mk,
        ContinuousLinearMap.zero_apply] using h
    have hezero := (calkinQuotient_eq_zero_iff X _).mpr (hcompact _ hsep)
    exact hne ((hqE 0 0).symm.trans hezero)
  have hNrow : ∀ (F : Finset ℕ) (a : ℕ → ℂ), (∀ j ∈ F, ‖a j‖ ≤ 1) →
      ‖∑ j ∈ F, a j • absorbedMatrixUnit N 0 j‖ ≤ Cr + 1 :=
    fun F a ha => absorbedMatrixUnit_unit_row_bound N (Cr + 1)
      (add_nonneg hCr zero_le_one) hKnorm F a ha
  have hNcol : ∀ i, ‖absorbedMatrixUnit N i 0‖ ≤ Cc + 1 := by
    intro i
    exact (norm_quotientEndomorphism_le N.subspace (E i 0) (N.invariant i 0)).trans
      ((norm_boundedCalkinLift_lt X _).le.trans (add_le_add_right (hcolumn i) 1))
  obtain ⟨Θ, x, B, hB, hx, hΘ⟩ := exists_ellOne_unit_lifts_of_matrixUnits N.subspace
    (absorbedMatrixUnit N) (absorbedMatrixUnit_mul N) hNne (Cr + 1) (Cc + 1)
    (add_nonneg hCr zero_le_one) (add_nonneg hCc zero_le_one) hNrow hNcol
  obtain ⟨T, hsep, hnoncompact⟩ :=
    exists_separable_noncompact_of_ellOne_unit_lifts Θ x B hB hx hΘ
  exact hnoncompact (hcompact T hsep)

end NonCalkinAlgebra

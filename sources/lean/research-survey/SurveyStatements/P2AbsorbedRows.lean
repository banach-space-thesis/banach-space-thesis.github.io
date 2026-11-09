import SurveyStatements.P2MatrixErrorAbsorption
import SurveyStatements.P2CalkinCorrections

/-! Actual countable compact corrections give the full complex row bound on the invariant quotient. -/

noncomputable section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
open scoped BigOperators

namespace SurveyStatements.P2
universe v

theorem unit_row_bound_of_finite_subtype {Z : Type*}
    [SeminormedAddCommGroup Z] [NormedSpace ℂ Z] (U : ℕ → Z) (D : ℝ) (hD : 0 ≤ D)
    (hrow : ∀ (F : Finset ℕ) (b : F → ℂ), ‖∑ j : F, b j • U j.val‖ ≤ D * ‖b‖)
    (F : Finset ℕ) (a : ℕ → ℂ) (ha : ∀ j ∈ F, ‖a j‖ ≤ 1) :
    ‖∑ j ∈ F, a j • U j‖ ≤ D := by
  have ha' : ‖fun j : F => a j.val‖ ≤ 1 :=
    (pi_norm_le_iff_of_nonneg zero_le_one).mpr (fun j => ha j.val j.property)
  calc
    ‖∑ j ∈ F, a j • U j‖ = ‖∑ j : F, a j.val • U j.val‖ :=
      congrArg norm (Finset.sum_coe_sort F (fun j : ℕ => a j • U j)).symm
    _ ≤ D * ‖fun j : F => a j.val‖ := hrow F (fun j => a j.val)
    _ ≤ D * 1 := mul_le_mul_of_nonneg_left ha' hD
    _ = D := mul_one D

variable {X : Type v} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

local instance absorbedSubspace_isClosed
    {E : ℕ → ℕ → BoundedOperators X} {K : RationalFiniteCoefficients → BoundedOperators X}
    (N : MatrixErrorAbsorption E K) : IsClosed (N.subspace : Set X) := N.closed

def finiteRowRepresentative (E : ℕ → ℕ → BoundedOperators X) (F : Finset ℕ)
    (a : F → ℂ) : BoundedOperators X := ∑ j : F, a j • E 0 j.val

def rationalRowCorrection (E : ℕ → ℕ → BoundedOperators X) (C : ℝ) (hC : 0 ≤ C)
    (hrow : ∀ (F : Finset ℕ) (a : F → ℂ),
      ‖calkinQuotient X (finiteRowRepresentative E F a)‖ ≤ C * ‖a‖)
    (c : RationalFiniteCoefficients) : BoundedOperators X :=
  Classical.choose (exists_compactCorrection_norm_le X
    (finiteRowRepresentative E c.1 (fun j => rationalComplex (c.2 j)))
    ‖fun j => rationalComplex (c.2 j)‖ C (norm_nonneg _) hC
    (hrow c.1 (fun j => rationalComplex (c.2 j))))

theorem rationalRowCorrection_compact (E : ℕ → ℕ → BoundedOperators X) (C hC hrow)
    (c : RationalFiniteCoefficients) : IsCompactOperator (rationalRowCorrection E C hC hrow c) :=
  (Classical.choose_spec (exists_compactCorrection_norm_le X
    (finiteRowRepresentative E c.1 (fun j => rationalComplex (c.2 j)))
    ‖fun j => rationalComplex (c.2 j)‖ C (norm_nonneg _) hC
    (hrow c.1 (fun j => rationalComplex (c.2 j))))).1

theorem rationalRowCorrection_norm_le (E : ℕ → ℕ → BoundedOperators X) (C hC hrow)
    (c : RationalFiniteCoefficients) :
    ‖finiteRowRepresentative E c.1 (fun j => rationalComplex (c.2 j)) +
      rationalRowCorrection E C hC hrow c‖ ≤ (C + 1) * ‖fun j => rationalComplex (c.2 j)‖ :=
  (Classical.choose_spec (exists_compactCorrection_norm_le X
    (finiteRowRepresentative E c.1 (fun j => rationalComplex (c.2 j)))
    ‖fun j => rationalComplex (c.2 j)‖ C (norm_nonneg _) hC
    (hrow c.1 (fun j => rationalComplex (c.2 j))))).2

theorem absorbedMatrixUnit_finite_row_bound
    {E : ℕ → ℕ → BoundedOperators X} {K : RationalFiniteCoefficients → BoundedOperators X}
    (N : MatrixErrorAbsorption E K) (D : ℝ)
    (hKnorm : ∀ c : RationalFiniteCoefficients,
      ‖finiteRowRepresentative E c.1 (fun j => rationalComplex (c.2 j)) + K c‖ ≤
        D * ‖fun j => rationalComplex (c.2 j)‖)
    (F : Finset ℕ) (a : F → ℂ) :
    ‖∑ j : F, a j • absorbedMatrixUnit N 0 j.val‖ ≤ D * ‖a‖ := by
  letI : IsClosed (N.subspace : Set X) := N.closed
  apply finite_row_bound_of_rational (fun j : F => absorbedMatrixUnit N 0 j.val) D _ a
  intro b
  let S := finiteRowRepresentative E F (fun j => rationalComplex (b j))
  have hS : N.subspace ≤ N.subspace.comap S.toLinearMap := by
    intro x hx
    change S x ∈ N.subspace
    simp only [S, finiteRowRepresentative, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smul_apply]
    exact N.subspace.sum_mem (fun j _ => N.subspace.smul_mem _ (N.invariant 0 j.val hx))
  have hsum : (∑ j : F, rationalComplex (b j) • absorbedMatrixUnit N 0 j.val) =
      quotientEndomorphism N.subspace S hS := by
    ext y
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective N.subspace y
    simp only [S, finiteRowRepresentative, absorbedMatrixUnit, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smul_apply, quotientEndomorphism_mk, map_sum, map_smul]
  rw [hsum]
  exact (norm_quotientEndomorphism_le_correction N.subspace S (K ⟨F, b⟩) hS
    (N.corrections ⟨F, b⟩)).trans (hKnorm ⟨F, b⟩)

theorem absorbedMatrixUnit_unit_row_bound
    {E : ℕ → ℕ → BoundedOperators X} {K : RationalFiniteCoefficients → BoundedOperators X}
    (N : MatrixErrorAbsorption E K) (D : ℝ) (hD : 0 ≤ D)
    (hKnorm : ∀ c : RationalFiniteCoefficients,
      ‖finiteRowRepresentative E c.1 (fun j => rationalComplex (c.2 j)) + K c‖ ≤
        D * ‖fun j => rationalComplex (c.2 j)‖)
    (F : Finset ℕ) (a : ℕ → ℂ) (ha : ∀ j ∈ F, ‖a j‖ ≤ 1) :
    ‖∑ j ∈ F, a j • absorbedMatrixUnit N 0 j‖ ≤ D := by
  exact unit_row_bound_of_finite_subtype (fun j => absorbedMatrixUnit N 0 j) D hD
    (absorbedMatrixUnit_finite_row_bound N D hKnorm) F a ha

end SurveyStatements.P2

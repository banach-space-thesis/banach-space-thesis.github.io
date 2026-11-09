import SurveyStatements.P2InvariantAbsorption
import SurveyStatements.P2InvariantQuotient
import SurveyStatements.P2SeparableRangeCalkin
import SurveyStatements.P2RationalCoefficients

/-! Countably many actual matrix errors and row corrections disappear in a separable invariant quotient. -/

noncomputable section
set_option autoImplicit false
open TopologicalSpace

namespace SurveyStatements.P2
universe v
variable {X : Type v} [NormedAddCommGroup X] [NormedSpace ℂ X]

def matrixRelationError (E : ℕ → ℕ → BoundedOperators X) (i j k l : ℕ) : BoundedOperators X :=
  E i j * E k l - if j = k then E i l else 0

structure MatrixErrorAbsorption (E : ℕ → ℕ → BoundedOperators X)
    (K : RationalFiniteCoefficients → BoundedOperators X) where
  subspace : Submodule ℂ X
  closed : IsClosed (subspace : Set X)
  separable : IsSeparable (subspace : Set X)
  invariant : ∀ i j, subspace ≤ subspace.comap (E i j).toLinearMap
  errors : ∀ i j k l x, matrixRelationError E i j k l x ∈ subspace
  corrections : ∀ c x, K c x ∈ subspace

def matrixErrorAbsorption (E : ℕ → ℕ → BoundedOperators X)
    (hE : ∀ i j k l, IsCompactOperator (matrixRelationError E i j k l))
    (K : RationalFiniteCoefficients → BoundedOperators X)
    (hK : ∀ c, IsCompactOperator (K c)) : MatrixErrorAbsorption E K := by
  let U : ℕ → BoundedOperators X := fun n => E (Nat.unpair n).1 (Nat.unpair n).2
  let S : Set X := (⋃ p : (ℕ × ℕ) × (ℕ × ℕ),
      Set.range (matrixRelationError E p.1.1 p.1.2 p.2.1 p.2.2)) ∪
    ⋃ c : RationalFiniteCoefficients, Set.range (K c)
  have hS : IsSeparable S :=
    (IsSeparable.iUnion (fun p : (ℕ × ℕ) × (ℕ × ℕ) =>
      compactOperator_range_isSeparable (hE p.1.1 p.1.2 p.2.1 p.2.2))).union
      (IsSeparable.iUnion (fun c => compactOperator_range_isSeparable (hK c)))
  refine
    { subspace := invariantAbsorptionSubspace U S
      closed := invariantAbsorptionSubspace_isClosed U S
      separable := invariantAbsorptionSubspace_isSeparable U S hS
      invariant := ?_
      errors := ?_
      corrections := ?_ }
  · intro i j x hx
    have h := invariantAbsorptionSubspace_invariant U S (Nat.pair i j) hx
    simpa only [U, Nat.unpair_pair] using h
  · intro i j k l x
    apply subset_invariantAbsorptionSubspace U S
    exact Or.inl (Set.mem_iUnion.mpr ⟨((i, j), (k, l)), x, rfl⟩)
  · intro c x
    apply subset_invariantAbsorptionSubspace U S
    exact Or.inr (Set.mem_iUnion.mpr ⟨c, x, rfl⟩)

def absorbedMatrixUnit {E : ℕ → ℕ → BoundedOperators X}
    {K : RationalFiniteCoefficients → BoundedOperators X}
    (N : MatrixErrorAbsorption E K) (i j : ℕ) :
    (X ⧸ N.subspace) →L[ℂ] (X ⧸ N.subspace) :=
  quotientEndomorphism N.subspace (E i j) (N.invariant i j)

theorem absorbedMatrixUnit_mul {E : ℕ → ℕ → BoundedOperators X}
    {K : RationalFiniteCoefficients → BoundedOperators X}
    (N : MatrixErrorAbsorption E K) (i j k l : ℕ) :
    absorbedMatrixUnit N i j * absorbedMatrixUnit N k l =
      if j = k then absorbedMatrixUnit N i l else 0 := by
  classical
  ext y
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective N.subspace y
  have hz : N.subspace.mkQ (matrixRelationError E i j k l x) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr (N.errors i j k l x)
  by_cases hjk : j = k
  · simp only [absorbedMatrixUnit, ContinuousLinearMap.mul_apply,
      quotientEndomorphism_mk, if_pos hjk]
    simpa only [matrixRelationError, if_pos hjk, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.mul_apply, map_sub, sub_eq_zero] using hz
  · simp only [absorbedMatrixUnit, ContinuousLinearMap.mul_apply,
      quotientEndomorphism_mk, if_neg hjk, ContinuousLinearMap.zero_apply]
    simpa only [matrixRelationError, if_neg hjk, sub_zero,
      ContinuousLinearMap.mul_apply] using hz

theorem absorbedMatrixUnit_diagonal_ne_zero [CompleteSpace X]
    {E : ℕ → ℕ → BoundedOperators X} {K : RationalFiniteCoefficients → BoundedOperators X}
    (N : MatrixErrorAbsorption E K) (hX : ¬ SeparableSpace X)
    (hsimple : ∀ J : TwoSidedIdeal (Calkin X), J = ⊥ ∨ J = ⊤)
    (i : ℕ) (hne : calkinQuotient X (E i i) ≠ 0) : absorbedMatrixUnit N i i ≠ 0 := by
  intro hz
  have hsep : IsSeparable (Set.range (E i i)) := by
    apply N.separable.mono
    rintro y ⟨x, rfl⟩
    apply (Submodule.Quotient.mk_eq_zero _).mp
    have h := congrArg (fun T : (X ⧸ N.subspace) →L[ℂ] (X ⧸ N.subspace) =>
      T (N.subspace.mkQ x)) hz
    simpa only [absorbedMatrixUnit, quotientEndomorphism_mk, ContinuousLinearMap.zero_apply] using h
  have hcompact := compact_of_separableRange_of_simple_calkin X hX hsimple hsep
  exact hne ((calkinQuotient_eq_zero_iff X _).mpr hcompact)

end SurveyStatements.P2

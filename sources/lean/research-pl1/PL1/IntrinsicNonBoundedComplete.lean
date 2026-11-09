import PL1.IntrinsicWalshBlocks
import PL1.SingularResolvents
import PL1.DecompositionRNP
import PL1.ScalarDecompositionRNP
import PL1.UnconditionalRNP
import PL1.SchurExample

/-! # Failure of bounded completeness for the actual intrinsic Walsh decompositions -/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace PL1.Noise

open DecompositionRNP

theorem intrinsic_not_boundedlyComplete_real (rates : ℕ → ℝ≥0)
    (hRNP : ¬ HasRadonNikodymProperty.{_, 0} (dyadicSystem ℝ rates).IntrinsicSpace) :
    ¬ BoundedlyComplete (intrinsicExpectation ℝ rates) := by
  intro hBC
  apply hRNP
  apply hasRadonNikodymProperty_of_boundedlyCompleteDecomposition
  exact {
    projection := intrinsicExpectation ℝ rates
    finiteDimensional := intrinsicExpectation_range_finiteDimensional ℝ rates
    nested := intrinsicExpectation_comp_of_le ℝ rates
    uniformBound := ⟨1, norm_intrinsicExpectation_le ℝ rates⟩
    tendsto_identity := tendsto_intrinsicExpectation ℝ rates
    bounded_complete := hBC }

theorem schur_intrinsic_not_boundedlyComplete_real :
    ¬ BoundedlyComplete (intrinsicExpectation ℝ schurRates) :=
  intrinsic_not_boundedlyComplete_real schurRates schur_intrinsic_not_RNP_real

theorem constant_intrinsic_not_boundedlyComplete_real :
    ¬ BoundedlyComplete (intrinsicExpectation ℝ constantRates) :=
  intrinsic_not_boundedlyComplete_real constantRates constant_intrinsic_not_RNP_real

/-- Failure of bounded completeness gives an actual bounded coherent branch that is not Cauchy.
This is an existence consequence; it does not identify a particular martingale. -/
theorem exists_nonCauchy_branch_of_not_boundedlyComplete
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (P : ℕ → E →L[ℝ] E) (hP : ¬ BoundedlyComplete P) :
    ∃ x : ℕ → E, (∀ m n, m ≤ n → P m (x n) = x m) ∧
      (∃ M : ℝ, ∀ n, ‖x n‖ ≤ M) ∧ ¬ CauchySeq x := by
  classical
  by_contra! h
  apply hP
  intro x hx hbounded
  exact cauchySeq_tendsto_of_complete (h x hx hbounded)

theorem schur_intrinsic_exists_nonCauchy_branch_real :
    ∃ x : ℕ → (dyadicSystem ℝ schurRates).IntrinsicSpace,
      (∀ m n, m ≤ n → intrinsicExpectation ℝ schurRates m (x n) = x m) ∧
      (∃ M : ℝ, ∀ n, ‖x n‖ ≤ M) ∧ ¬ CauchySeq x :=
  exists_nonCauchy_branch_of_not_boundedlyComplete _ schur_intrinsic_not_boundedlyComplete_real

theorem constant_intrinsic_exists_nonCauchy_branch_real :
    ∃ x : ℕ → (dyadicSystem ℝ constantRates).IntrinsicSpace,
      (∀ m n, m ≤ n → intrinsicExpectation ℝ constantRates m (x n) = x m) ∧
      (∃ M : ℝ, ∀ n, ‖x n‖ ≤ M) ∧ ¬ CauchySeq x :=
  exists_nonCauchy_branch_of_not_boundedlyComplete _ constant_intrinsic_not_boundedlyComplete_real

theorem intrinsic_not_boundedlyComplete_scalar (K : Type*) [RCLike K] (rates : ℕ → ℝ≥0)
    (hRNP : ¬ @HasRadonNikodymProperty.{_, 0}
      (UnderlyingReal K (dyadicSystem K rates).IntrinsicSpace)
      (inferInstanceAs (NormedAddCommGroup (dyadicSystem K rates).IntrinsicSpace))
      (NormedSpace.restrictScalars ℝ K (dyadicSystem K rates).IntrinsicSpace)) :
    ¬ ScalarDecompositionRNP.BoundedlyComplete (intrinsicExpectation K rates) := by
  intro hBC
  exact hRNP (ScalarDecompositionRNP.hasRNP_of_scalar_projections
    (intrinsicExpectation K rates) (intrinsicExpectation_range_finiteDimensional K rates)
    (intrinsicExpectation_comp_of_le K rates) ⟨1, norm_intrinsicExpectation_le K rates⟩
    (tendsto_intrinsicExpectation K rates) hBC)

theorem schur_intrinsic_not_boundedlyComplete (K : Type*) [RCLike K] :
    ¬ ScalarDecompositionRNP.BoundedlyComplete (intrinsicExpectation K schurRates) :=
  intrinsic_not_boundedlyComplete_scalar K schurRates (schur_intrinsic_not_RNP K)

theorem constant_intrinsic_not_boundedlyComplete (K : Type*) [RCLike K] :
    ¬ ScalarDecompositionRNP.BoundedlyComplete (intrinsicExpectation K constantRates) :=
  intrinsic_not_boundedlyComplete_scalar K constantRates (constant_intrinsic_not_RNP K)

theorem schur_intrinsic_exists_nonCauchy_branch (K : Type*) [RCLike K] :
    ∃ x : ℕ → (dyadicSystem K schurRates).IntrinsicSpace,
      (∀ m n, m ≤ n → intrinsicExpectation K schurRates m (x n) = x m) ∧
      (∃ M : ℝ, ∀ n, ‖x n‖ ≤ M) ∧ ¬ CauchySeq x :=
  ScalarDecompositionRNP.exists_nonCauchy_branch _ (schur_intrinsic_not_boundedlyComplete K)

theorem constant_intrinsic_exists_nonCauchy_branch (K : Type*) [RCLike K] :
    ∃ x : ℕ → (dyadicSystem K constantRates).IntrinsicSpace,
      (∀ m n, m ≤ n → intrinsicExpectation K constantRates m (x n) = x m) ∧
      (∃ M : ℝ, ∀ n, ‖x n‖ ≤ M) ∧ ¬ CauchySeq x :=
  ScalarDecompositionRNP.exists_nonCauchy_branch _ (constant_intrinsic_not_boundedlyComplete K)

/-- The actual real Schur example has no uniformly bounded sign transformations for its FDD. -/
theorem schur_intrinsic_no_uniform_sign_bound :
    ¬ ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (ε : ℕ → ℝ)
      (y : (dyadicSystem ℝ schurRates).IntrinsicSpace),
      (∀ j, ε j = 1 ∨ ε j = -1) →
        ‖∑ j ∈ Finset.range (N + 1), ε j •
          UnconditionalDecomposition.difference (intrinsicExpectation ℝ schurRates) j y‖ ≤ C * ‖y‖ :=
  UnconditionalRNP.no_uniform_sign_bound_of_not_RNP
    (schurRates_intrinsic_hasSchurProperty ℝ) schur_intrinsic_not_RNP_real
    (intrinsicExpectation ℝ schurRates) (intrinsicExpectation_range_finiteDimensional ℝ schurRates)
    (intrinsicExpectation_comp_of_le ℝ schurRates) (tendsto_intrinsicExpectation ℝ schurRates)

end PL1.Noise

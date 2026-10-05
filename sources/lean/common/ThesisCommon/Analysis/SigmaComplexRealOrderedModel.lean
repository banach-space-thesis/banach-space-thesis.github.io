import ThesisCommon.Analysis.ALRenormSpectral
import ThesisCommon.Analysis.SigmaComplexALNormedCopy
import ThesisCommon.Analysis.ALAtomicRepresentationEllOne

/-! The general ordered ℓ¹ model assembled from the proved spectral estimate,
the positive-partition norm, and Schur atomicity. This is also the real ordered
input needed for the complexification argument. -/
noncomputable section
open scoped BigOperators
universe u v
namespace ThesisCommon

theorem exists_ordered_ellOne_of_conditionallyComplete_equiv
    {E : Type u} {I : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ConditionallyCompleteLattice E] [IsOrderedAddMonoid E] [IsOrderedModule ℝ E]
    [HasSolidNorm E] [CompleteSpace E] (d : E ≃L[ℝ] lp (fun _ : I => ℝ) 1) :
    ∃ J : Type u, ∃ a : E ≃L[ℝ] lp (fun _ : J => ℝ) 1,
      ∀ x : E, 0 ≤ x ↔ ∀ j, 0 ≤ a x j := by
  let A : ℝ := max 1 ‖d.toContinuousLinearMap‖
  let B : ℝ := max 1 ‖d.symm.toContinuousLinearMap‖
  have hA : 0 < A := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  let C : ℝ := (128*A*B)^2
  have hC : 0 ≤ C := sq_nonneg _
  have hb : ∀ (n : ℕ) (z : Fin n → E), (∀ i, 0 ≤ z i) →
      (∑ i, ‖z i‖) ≤ C * ‖∑ i, z i‖ := by
    intro n z hz
    exact positive_decomposition_bound_of_equiv_ellOne d A B hA hB
      (le_max_right _ _) (le_max_right _ _) z hz
  let R := SigmaComplexPositivePartitionSpace (E := E) C hC hb
  let T : E ≃L[ℝ] R := sigmaComplexPositivePartitionSpaceEquiv C hC hb
  have hAL : ∀ x y : R, 0 ≤ x → 0 ≤ y → ‖x+y‖ = ‖x‖ + ‖y‖ :=
    sigmaComplexPositivePartitionSpace_AL C hC hb
  obtain ⟨J,a,ha⟩ := exists_ordered_ellOne_of_AL_equiv hAL (T.symm.trans d)
  refine ⟨J,T.trans a,?_⟩
  intro x
  exact (sigmaComplexPositivePartitionSpaceEquiv_nonneg C hC hb x).symm.trans (ha (T x))

end ThesisCommon


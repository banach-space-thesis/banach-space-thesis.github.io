import ThesisCommon.Analysis.ALRenormProjections
import ThesisCommon.Analysis.ALRenormPartition
import ThesisCommon.Analysis.BandProjectionModulus

/-! The analytic lower estimate applied to actual positive band projections.
The scalar cube estimate is proved from order and orthogonality here. -/
noncomputable section
open scoped BigOperators ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon
attribute [local instance] Classical.decEq
variable {E I J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [ConditionallyCompleteLattice E] [IsOrderedAddMonoid E]
variable [IsOrderedModule ℝ E] [HasSolidNorm E]

theorem positive_orthogonal_sum_le (R : J → E →L[ℝ] E)
    (hR : ∀ j, 0 ≤ R j) (hle : ∀ j, R j ≤ ContinuousLinearMap.id ℝ E)
    (horth : ∀ i j, i ≠ j → ∀ x : E, R i (R j x) = 0)
    (s : Finset J) (x : E) (hx : 0 ≤ x) : (∑ j ∈ s, R j x) ≤ x := by
  classical
  induction s using Finset.induction_on generalizing x with
  | empty => simpa using hx
  | @insert i s his ih =>
    have hres : 0 ≤ x-R i x := sub_nonneg.mpr (hle i x hx)
    have hs := ih (x-R i x) hres
    have heq : (∑ j ∈ s, R j (x-R i x)) = ∑ j ∈ s, R j x := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [map_sub, horth j i (fun h => his (h ▸ hj)), sub_zero]
    rw [heq] at hs
    rw [Finset.sum_insert his]
    have h := add_le_add_left hs (R i x)
    have heq : R i x + (x-R i x) = x := by abel
    simpa only [heq] using h

theorem positive_orthogonal_cube_bound [Fintype J] (R : J → E →L[ℝ] E)
    (hR : ∀ j, 0 ≤ R j) (hle : ∀ j, R j ≤ ContinuousLinearMap.id ℝ E)
    (horth : ∀ i j, i ≠ j → ∀ x : E, R i (R j x) = 0)
    (x : E) (b : J → ℝ) (hb : ∀ j, |b j| ≤ 1) :
    ‖∑ j, b j • R j x‖ ≤ ‖x‖ := by
  apply norm_le_norm_of_abs_le_abs
  calc
    |∑ j, b j • R j x| ≤ ∑ j, |b j • R j x| := lattice_abs_sum_le _ _
    _ ≤ ∑ j, R j |x| := by
      apply Finset.sum_le_sum
      intro j _
      rw [al_lattice_abs_smul]
      calc
        |b j| • |R j x| ≤ |R j x| := by
          have h := smul_le_smul_of_nonneg_right (hb j) (abs_nonneg (R j x))
          simpa only [one_smul] using h
        _ ≤ R j |x| := abs_apply_le_of_positive (hR j) x
    _ ≤ |x| := positive_orthogonal_sum_le R hR hle horth Finset.univ |x| (abs_nonneg x)

theorem positive_orthogonal_projection_sum_norm_le [Fintype J]
    (d : E ≃L[ℝ] lp (fun _ : I => ℝ) 1) (A C : ℝ) (hA : 0 < A) (hC : 0 < C)
    (hd : ‖d.toContinuousLinearMap‖ ≤ A) (hdinv : ‖d.symm.toContinuousLinearMap‖ ≤ C)
    (R : J → E →L[ℝ] E)
    (hR : ∀ j, 0 ≤ R j) (hle : ∀ j, R j ≤ ContinuousLinearMap.id ℝ E)
    (hid : ∀ j x, R j (R j x) = R j x)
    (horth : ∀ i j, i ≠ j → ∀ x : E, R i (R j x) = 0)
    (x : E) : (∑ j, ‖R j x‖) ≤ (128 * A * C)^2 * ‖x‖ := by
  apply unconditional_projection_sum_norm_le d A C hA hC hd hdinv R
    (positive_orthogonal_cube_bound R hR hle horth) _ x
  intro i j y
  by_cases hij : i = j
  · subst i
    simpa using hid j y
  · simpa [hij] using horth i j hij y

/-- A finite family of pairwise disjoint, order-closed ideals satisfies the
lower estimate through its constructed band projections. -/
theorem band_projection_sum_norm_le [Fintype J]
    (d : E ≃L[ℝ] lp (fun _ : I => ℝ) 1) (A C : ℝ) (hA : 0 < A) (hC : 0 < C)
    (hd : ‖d.toContinuousLinearMap‖ ≤ A) (hdinv : ‖d.symm.toContinuousLinearMap‖ ≤ C)
    (V : J → Submodule ℝ E) (hV : ∀ j, IsOrderClosedIdeal (V j))
    (hdis : ∀ i j, i ≠ j → ∀ x ∈ V i, ∀ y ∈ V j, |x| ⊓ |y| = 0)
    (x : E) : (∑ j, ‖bandProjection (hV j) x‖) ≤ (128 * A * C)^2 * ‖x‖ := by
  apply positive_orthogonal_projection_sum_norm_le d A C hA hC hd hdinv
    (fun j => bandProjection (hV j))
    (fun j => (hV j).bandProjection_nonneg) (fun j => (hV j).bandProjection_le_id)
    (fun j => (hV j).bandProjection_idempotent) _ x
  intro i j hij y
  apply ((hV i).bandProjection_eq_zero_iff _).mpr
  intro z hz
  exact hdis j i hij.symm _ ((hV j).bandProjection_mem y) z hz

end ThesisCommon

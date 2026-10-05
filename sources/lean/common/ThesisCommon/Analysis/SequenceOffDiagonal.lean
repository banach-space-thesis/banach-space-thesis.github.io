import ThesisCommon.Analysis.SequenceEntryOperators
import ThesisCommon.Analysis.SequencePrefixAlgebra

/-! The quantitative last step of UPFP's cotype diagonal reduction:
for an actual lower-triangular operator, a bound on each finite strict-lower
row sum bounds the difference from the actual diagonal operator.
-/
noncomputable section
open scoped ENNReal BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

private theorem norm_sum_apply_le (s : Finset ℕ) (F : ℕ → X →L[𝕜] X)
    (x : ℕ → X) {B : ℝ} (hx : ∀ i ∈ s, ‖x i‖ ≤ B) :
    ‖∑ i ∈ s, F i (x i)‖ ≤ (∑ i ∈ s, ‖F i‖) * B := by
  calc
    _ ≤ ∑ i ∈ s, ‖F i (x i)‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ s, ‖F i‖ * B := Finset.sum_le_sum fun i hi =>
      ((F i).le_opNorm (x i)).trans (mul_le_mul_of_nonneg_left (hx i hi) (norm_nonneg (F i)))
    _ = _ := (Finset.sum_mul ..).symm

/-- On ℓ∞, only the finitely many entries strictly below the diagonal remain. -/
theorem IsLpLowerPart.infinity_sub_diagonal_apply
    {T : EllInfinitySum X →L[𝕜] EllInfinitySum X} (h : IsLpLowerPart T T)
    (x : EllInfinitySum X) (k : ℕ) :
    (T - lpDiagonalPart T) x k = ∑ j ∈ Finset.range k, lpEntry T k j (x j) := by
  change T x k - lpEntry T k k (x k) = _
  rw [h.matrix_formula x k, Finset.sum_range_succ]
  simp only [lpEntry_apply, add_sub_cancel_right]

/-- Small strict-lower row sums imply a small operator difference on all ℓ∞. -/
theorem IsLpLowerPart.infinity_norm_sub_diagonal_le
    {T : EllInfinitySum X →L[𝕜] EllInfinitySum X} (h : IsLpLowerPart T T)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hsum : ∀ k, (∑ j ∈ Finset.range k, ‖lpEntry T k j‖) ≤ δ) :
    ‖T - lpDiagonalPart T‖ ≤ δ := by
  apply ContinuousLinearMap.opNorm_le_bound _ hδ
  intro x
  apply lp.norm_le_of_forall_le (mul_nonneg hδ (norm_nonneg x))
  intro k
  rw [h.infinity_sub_diagonal_apply]
  exact (norm_sum_apply_le (Finset.range k) (lpEntry T k) x
    (fun j _ => lp.norm_apply_le_norm ENNReal.top_ne_zero x j)).trans
      (mul_le_mul_of_nonneg_right (hsum k) (norm_nonneg x))

/-- The finite strict-lower action formula on c₀. -/
theorem IsCZeroLowerPart.sub_diagonal_apply
    {T : CZeroSum X →L[𝕜] CZeroSum X} (h : IsCZeroLowerPart T T)
    (x : CZeroSum X) (k : ℕ) :
    (T - cZeroDiagonalPart T) x k = ∑ j ∈ Finset.range k, cZeroEntry T k j (x j) := by
  change T x k - cZeroEntry T k k (x k) = _
  rw [h.matrix_formula x k, Finset.sum_range_succ]
  simp only [cZeroEntry_apply, add_sub_cancel_right]

/-- The corresponding bound on c₀; both operators already map into c₀. -/
theorem IsCZeroLowerPart.norm_sub_diagonal_le
    {T : CZeroSum X →L[𝕜] CZeroSum X} (h : IsCZeroLowerPart T T)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hsum : ∀ k, (∑ j ∈ Finset.range k, ‖cZeroEntry T k j‖) ≤ δ) :
    ‖T - cZeroDiagonalPart T‖ ≤ δ := by
  apply ContinuousLinearMap.opNorm_le_bound _ hδ
  intro x
  apply (BoundedContinuousFunction.norm_le (mul_nonneg hδ (norm_nonneg x))).mpr
  intro k
  change ‖(T - cZeroDiagonalPart T) x k‖ ≤ δ * ‖x‖
  rw [h.sub_diagonal_apply]
  exact (norm_sum_apply_le (Finset.range k) (cZeroEntry T k) x
    (fun j _ => BoundedContinuousFunction.norm_coe_le_norm x.toBCF j)).trans
      (mul_le_mul_of_nonneg_right (hsum k) (norm_nonneg x))

end ThesisCommon

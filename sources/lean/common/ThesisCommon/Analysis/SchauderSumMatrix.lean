import ThesisCommon.Analysis.SchauderSumOperators
import ThesisCommon.Analysis.SchauderMatrix

/-! Operator-valued block estimates on the genuine vector-valued basis sum.
Convergent coordinate truncations give column bounds; the outer norm-series
then turns a summable block majorant into an operator norm estimate.
-/
noncomputable section
open Filter Topology
open scoped BigOperators
namespace ThesisCommon
namespace SchauderSum
variable {𝕜 X Y Z : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
variable {b : NormalizedSchauderBasis 𝕜 X} {hb : b.IsOneUnconditional}

def block (T : SchauderSum b hb Y →L[𝕜] SchauderSum b hb Z) (r i : ℕ) : Y →L[𝕜] Z :=
  ((coordinate (b := b) (hb := hb) (Y := Z) r).comp T).comp (singleL i)

theorem block_apply (T : SchauderSum b hb Y →L[𝕜] SchauderSum b hb Z)
    (r i : ℕ) (y : Y) : block T r i y = T (single i y) r := rfl

theorem norm_le_of_column_bounds (T : SchauderSum b hb Y →L[𝕜] Z)
    {c : ℕ → ℝ} {C : ℝ} (hc : HasSum c C) (hC : 0 ≤ C)
    (hT : ∀ i, ‖T.comp (singleL i)‖ ≤ c i) : ‖T‖ ≤ C := by
  apply T.opNorm_le_bound hC
  intro y
  have ht := (T.continuous.tendsto y).comp (expansion y)
  apply le_of_tendsto' ht.norm
  intro N
  change ‖T (∑ i ∈ Finset.range N, single i (y i))‖ ≤ C * ‖y‖
  rw [map_sum]
  calc
    _ ≤ ∑ i ∈ Finset.range N, ‖T (single i (y i))‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range N, c i * ‖y‖ := by
      apply Finset.sum_le_sum
      intro i _
      exact ((T.comp (singleL i)).le_opNorm (y i)).trans
        (mul_le_mul (hT i) (norm_apply_le y i) (norm_nonneg _)
          ((norm_nonneg _).trans (hT i)))
    _ = (∑ i ∈ Finset.range N, c i) * ‖y‖ := (Finset.sum_mul ..).symm
    _ ≤ C * ‖y‖ := mul_le_mul_of_nonneg_right
      (hc.tsum_eq ▸ hc.summable.sum_le_tsum _
        (fun i _ => (norm_nonneg _).trans (hT i))) (norm_nonneg y)

theorem norm_le_of_block_majorant (T : SchauderSum b hb Y →L[𝕜] SchauderSum b hb Z)
    {c d : ℕ → ℝ} {C D : ℝ} (hc : HasSum c C) (hd : HasSum d D)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hd0 : ∀ i, 0 ≤ d i)
    (hT : ∀ r i, ‖block T r i‖ ≤ c r * d i) : ‖T‖ ≤ C * D := by
  apply norm_le_of_column_bounds T (hd.mul_left C) (mul_nonneg hC hD)
  intro i
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hC (hd0 i))
  intro y
  change ‖T (single i y)‖ ≤ C * d i * ‖y‖
  rw [norm_def, mul_assoc]
  apply b.norm_le_of_coordinate_majorant _ (hc.mul_right (d i * ‖y‖))
  intro r
  rw [coord_normVector, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _)]
  have hh := (block T r i).le_opNorm y
  change ‖T (single i y) r‖ ≤ _ at hh
  calc
    _ ≤ ‖block T r i‖ * ‖y‖ := hh
    _ ≤ (c r * d i) * ‖y‖ := mul_le_mul_of_nonneg_right (hT r i) (norm_nonneg _)
    _ = c r * (d i * ‖y‖) := mul_assoc _ _ _

/-- The source's positive-index block budget, shifted to zero-based indices. -/
theorem norm_le_of_geometric_blocks (T : SchauderSum b hb Y →L[𝕜] SchauderSum b hb Z)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hT : ∀ r i, ‖block T r i‖ ≤ ε / (2 : ℝ) ^ (r + i + 2)) : ‖T‖ ≤ ε := by
  have hc := NormalizedSchauderBasis.hasSum_half_geometric.mul_left ε
  have hh := norm_le_of_block_majorant T hc NormalizedSchauderBasis.hasSum_half_geometric
    (by simpa using hε) zero_le_one (fun i => by positivity)
  apply (by simpa using hh :
    (∀ r i, ‖block T r i‖ ≤
      (ε * ((1 / 2 : ℝ) * (1 / 2 : ℝ) ^ r)) *
        ((1 / 2 : ℝ) * (1 / 2 : ℝ) ^ i)) → ‖T‖ ≤ ε)
  intro r i
  convert hT r i using 1
  simp only [div_eq_mul_inv, pow_add, inv_pow, one_mul]
  ring

end SchauderSum
end ThesisCommon

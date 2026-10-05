import ThesisCommon.Analysis.SchauderBasis

/-! The small-matrix estimate from PFP Lemma 3.2. Both passages from
coefficients to vectors use convergent partial sums of the genuine basis.
Natural-number indices are zero-based, so the printed positive-index budget
ε / 2^(m+n) becomes ε / 2^(m+n+2).
-/
noncomputable section
open Filter Topology
open scoped BigOperators
namespace ThesisCommon
namespace NormalizedSchauderBasis
variable {𝕜 X Y : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable (b : NormalizedSchauderBasis 𝕜 X)

/-- Summable column majorants control an operator on any one-unconditional
normalized Schauder basis. The target can be an arbitrary normed space. -/
theorem norm_le_of_column_majorant (hb : b.IsOneUnconditional) (T : X →L[𝕜] Y)
    {c : ℕ → ℝ} {C : ℝ} (hc : HasSum c C) (hC : 0 ≤ C)
    (hT : ∀ n, ‖T (b.vector n)‖ ≤ c n) : ‖T‖ ≤ C := by
  apply T.opNorm_le_bound hC
  intro x
  have ht : Tendsto (fun N => ∑ n ∈ Finset.range N,
      b.coord n x • T (b.vector n)) atTop (𝓝 (T x)) := by
    have hh := (T.continuous.tendsto x).comp (b.expansion x)
    change Tendsto (fun N => T (∑ n ∈ Finset.range N,
      b.coord n x • b.vector n)) atTop (𝓝 (T x)) at hh
    simpa only [map_sum, map_smul] using hh
  apply le_of_tendsto' ht.norm
  intro N
  calc
    _ ≤ ∑ n ∈ Finset.range N, ‖b.coord n x • T (b.vector n)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.range N, ‖x‖ * c n := by
      apply Finset.sum_le_sum
      intro n _
      rw [norm_smul]
      exact mul_le_mul (b.coord_le_norm hb n x) (hT n) (norm_nonneg _) (norm_nonneg _)
    _ = ‖x‖ * ∑ n ∈ Finset.range N, c n := (Finset.mul_sum ..).symm
    _ ≤ ‖x‖ * C := mul_le_mul_of_nonneg_left
      (hc.tsum_eq ▸ hc.summable.sum_le_tsum _
        (fun n _ => (norm_nonneg _).trans (hT n))) (norm_nonneg _)
    _ = C * ‖x‖ := mul_comm _ _

/-- A product of summable scalar budgets bounds the operator norm by the
product of their sums. This contains the geometric small-matrix lemma. -/
theorem norm_le_of_matrix_majorant (hb : b.IsOneUnconditional) (T : X →L[𝕜] X)
    {c d : ℕ → ℝ} {C D : ℝ} (hc : HasSum c C) (hd : HasSum d D)
    (hCD : 0 ≤ C * D)
    (hT : ∀ m n, ‖b.coord m (T (b.vector n))‖ ≤ c m * d n) : ‖T‖ ≤ C * D := by
  apply b.norm_le_of_column_majorant hb T (hd.mul_left C) hCD
  intro n
  exact b.norm_le_of_coordinate_majorant (T (b.vector n)) (hc.mul_right (d n))
    (fun m => hT m n)

/-- The geometric weights 2^(-(n+1)) sum to one. -/
theorem hasSum_half_geometric :
    HasSum (fun n : ℕ => (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ n) 1 := by
  convert (hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)).mul_left (1 / 2 : ℝ) using 1
  norm_num

/-- Lemma 3.2 with a non-strict entry bound (a stronger hypothesis-to-conclusion
result) and the explicit shift from positive to zero-based indices. -/
theorem norm_le_of_geometric_entries (hb : b.IsOneUnconditional)
    (T : X →L[𝕜] X) {ε : ℝ} (hε : 0 ≤ ε)
    (hT : ∀ m n, ‖b.coord m (T (b.vector n))‖ ≤ ε / (2 : ℝ) ^ (m + n + 2)) :
    ‖T‖ ≤ ε := by
  have hc := hasSum_half_geometric.mul_left ε
  have hh := b.norm_le_of_matrix_majorant hb T hc hasSum_half_geometric
    (by simpa using hε)
  apply (by simpa using hh :
    (∀ m n, ‖b.coord m (T (b.vector n))‖ ≤
      (ε * ((1 / 2 : ℝ) * (1 / 2 : ℝ) ^ m)) *
        ((1 / 2 : ℝ) * (1 / 2 : ℝ) ^ n)) → ‖T‖ ≤ ε)
  intro m n
  convert hT m n using 1
  simp only [div_eq_mul_inv, pow_add, inv_pow, one_mul]
  ring

end NormalizedSchauderBasis
end ThesisCommon

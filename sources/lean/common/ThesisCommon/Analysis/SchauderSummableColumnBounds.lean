import ThesisCommon.Analysis.SchauderBasis

/-! Summable column bounds on an ordered Schauder basis. Only the actual
coordinate norms and convergent partial sums are used; no unconditionality
or pre-existing matrix representation is assumed. -/
noncomputable section
open Filter Topology
open scoped BigOperators
namespace ThesisCommon.NormalizedSchauderBasis
variable {𝕜 X Y : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable (b : NormalizedSchauderBasis 𝕜 X)

theorem norm_apply_le_of_summable_columns (T : X →L[𝕜] Y) {K : ℝ}
    (hcoord : ∀ n, ‖b.coord n‖ ≤ K) {a : ℕ → ℝ} (ha : Summable a)
    (hcol : ∀ n, ‖T (b.vector n)‖ ≤ a n) (x : X) :
    ‖T x‖ ≤ (K * ∑' n, a n) * ‖x‖ := by
  have hK : 0 ≤ K := (norm_nonneg (b.coord 0)).trans (hcoord 0)
  have han : ∀ n, 0 ≤ a n := fun n => (norm_nonneg _).trans (hcol n)
  apply le_of_tendsto' ((T.continuous.tendsto x).comp (b.expansion x)).norm
  intro N
  change ‖T (∑ n ∈ Finset.range N, b.coord n x • b.vector n)‖ ≤ _
  rw [map_sum]
  calc
    _ ≤ ∑ n ∈ Finset.range N, ‖T (b.coord n x • b.vector n)‖ := norm_sum_le _ _
    _ = ∑ n ∈ Finset.range N, ‖b.coord n x‖ * ‖T (b.vector n)‖ := by
      simp only [map_smul, norm_smul]
    _ ≤ ∑ n ∈ Finset.range N, (K * ‖x‖) * a n := by
      apply Finset.sum_le_sum
      intro n hn
      exact mul_le_mul
        (((b.coord n).le_opNorm x).trans
          (mul_le_mul_of_nonneg_right (hcoord n) (norm_nonneg x)))
        (hcol n) (norm_nonneg _) (mul_nonneg hK (norm_nonneg x))
    _ = (K * ‖x‖) * ∑ n ∈ Finset.range N, a n := by rw [Finset.mul_sum]
    _ ≤ (K * ‖x‖) * ∑' n, a n := mul_le_mul_of_nonneg_left
      (ha.sum_le_tsum _ (fun n _ => han n)) (mul_nonneg hK (norm_nonneg x))
    _ = _ := by ring

theorem norm_operator_le_of_summable_columns (T : X →L[𝕜] Y) {K : ℝ}
    (hcoord : ∀ n, ‖b.coord n‖ ≤ K) {a : ℕ → ℝ} (ha : Summable a)
    (hcol : ∀ n, ‖T (b.vector n)‖ ≤ a n) :
    ‖T‖ ≤ K * ∑' n, a n := by
  have hK : 0 ≤ K := (norm_nonneg (b.coord 0)).trans (hcoord 0)
  have han : ∀ n, 0 ≤ a n := fun n => (norm_nonneg _).trans (hcol n)
  apply T.opNorm_le_bound (mul_nonneg hK (tsum_nonneg han))
  exact b.norm_apply_le_of_summable_columns T hcoord ha hcol

theorem norm_sub_le_of_summable_columns (T S : X →L[𝕜] Y) {K : ℝ}
    (hcoord : ∀ n, ‖b.coord n‖ ≤ K) {a : ℕ → ℝ} (ha : Summable a)
    (hcol : ∀ n, ‖T (b.vector n) - S (b.vector n)‖ ≤ a n) :
    ‖T - S‖ ≤ K * ∑' n, a n := by
  apply b.norm_operator_le_of_summable_columns (T - S) hcoord ha
  simpa only [ContinuousLinearMap.sub_apply] using hcol

end ThesisCommon.NormalizedSchauderBasis

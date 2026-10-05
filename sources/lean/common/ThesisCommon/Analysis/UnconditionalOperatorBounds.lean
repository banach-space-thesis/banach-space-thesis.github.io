import ThesisCommon.Analysis.SchauderOperators
import ThesisCommon.Analysis.SchauderMatrix

/-! Coordinate, diagonal and small-matrix bounds with an arbitrary
unconditional constant. These keep the original norm rather than assuming
a renorming has already made the basis one-unconditional. -/
noncomputable section
open Filter Topology
open scoped BigOperators
namespace ThesisCommon.NormalizedSchauderBasis
variable {𝕜 X Y : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  (b : NormalizedSchauderBasis 𝕜 X)

theorem UnconditionalWith.coord_le_bound {K : ℝ} (h : b.UnconditionalWith K)
    (n : ℕ) (x : X) : ‖b.coord n x‖ ≤ K * ‖x‖ := by
  classical
  apply ge_of_tendsto ((b.expansion x).norm.const_mul K)
  filter_upwards [eventually_gt_atTop n] with N hN
  have hn : n ∈ Finset.range N := Finset.mem_range.mpr hN
  have hh := h.2 (Finset.range N) (Pi.single n (b.coord n x)) (fun j => b.coord j x)
    (by
      intro j _
      by_cases hnj : j = n
      · subst j; simp
      · simp [Pi.single_eq_of_ne hnj])
  simpa [Pi.single_apply, Finset.sum_ite_eq', hn, norm_smul, b.norm_vector] using hh

theorem UnconditionalWith.exists_diagonal_bound [CompleteSpace X] {K C : ℝ}
    (hb : b.UnconditionalWith K) (d : ℕ → 𝕜) (hC : 0 ≤ C)
    (hd : ∀ n, ‖d n‖ ≤ C) :
    ∃ D : X →L[𝕜] X, ‖D‖ ≤ K * C ∧ ∀ n, D (b.vector n) = d n • b.vector n := by
  apply b.exists_operator _ (mul_nonneg (zero_le_one.trans hb.1) hC)
  intro F a
  have hh := hb.2 F (fun n => a n * d n) (fun n => (C : 𝕜) * a n) (by
    intro n _
    rw [norm_mul, norm_mul, RCLike.norm_ofReal, abs_of_nonneg hC]
    nlinarith [hd n, norm_nonneg (a n)])
  simpa only [mul_smul, ← Finset.smul_sum, norm_smul,
    RCLike.norm_ofReal, abs_of_nonneg hC, mul_assoc] using hh

theorem UnconditionalWith.norm_le_of_column_majorant {K : ℝ}
    (hb : b.UnconditionalWith K) (T : X →L[𝕜] Y)
    {c : ℕ → ℝ} {C : ℝ} (hc : HasSum c C) (hC : 0 ≤ C)
    (hT : ∀ n, ‖T (b.vector n)‖ ≤ c n) : ‖T‖ ≤ K * C := by
  have hK : 0 ≤ K := zero_le_one.trans hb.1
  apply T.opNorm_le_bound (mul_nonneg hK hC)
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
    _ ≤ ∑ n ∈ Finset.range N, (K * ‖x‖) * c n := by
      apply Finset.sum_le_sum
      intro n _
      rw [norm_smul]
      exact mul_le_mul (hb.coord_le_bound b n x) (hT n) (norm_nonneg _)
        (mul_nonneg hK (norm_nonneg _))
    _ = (K * ‖x‖) * ∑ n ∈ Finset.range N, c n := (Finset.mul_sum ..).symm
    _ ≤ (K * ‖x‖) * C := mul_le_mul_of_nonneg_left
      (hc.tsum_eq ▸ hc.summable.sum_le_tsum _
        (fun n _ => (norm_nonneg _).trans (hT n))) (mul_nonneg hK (norm_nonneg _))
    _ = _ := by ring

theorem UnconditionalWith.norm_le_of_matrix_majorant {K : ℝ}
    (hb : b.UnconditionalWith K) (T : X →L[𝕜] X)
    {c d : ℕ → ℝ} {C D : ℝ} (hc : HasSum c C) (hd : HasSum d D)
    (hCD : 0 ≤ C * D)
    (hT : ∀ m n, ‖b.coord m (T (b.vector n))‖ ≤ c m * d n) :
    ‖T‖ ≤ K * (C * D) := by
  apply hb.norm_le_of_column_majorant b T (hd.mul_left C) hCD
  intro n
  exact b.norm_le_of_coordinate_majorant (T (b.vector n)) (hc.mul_right (d n))
    (fun m => hT m n)

theorem UnconditionalWith.norm_le_of_geometric_entries {K : ℝ}
    (hb : b.UnconditionalWith K) (T : X →L[𝕜] X) {ε : ℝ} (hε : 0 ≤ ε)
    (hT : ∀ m n, ‖b.coord m (T (b.vector n))‖ ≤ ε / (2 : ℝ) ^ (m + n + 2)) :
    ‖T‖ ≤ K * ε := by
  have hc := hasSum_half_geometric.mul_left ε
  have hh := hb.norm_le_of_matrix_majorant b T hc hasSum_half_geometric
    (by simpa using hε)
  apply (by simpa using hh :
    (∀ m n, ‖b.coord m (T (b.vector n))‖ ≤
      (ε * ((1 / 2 : ℝ) * (1 / 2 : ℝ) ^ m)) *
        ((1 / 2 : ℝ) * (1 / 2 : ℝ) ^ n)) → ‖T‖ ≤ K * ε)
  intro m n
  convert hT m n using 1
  simp only [div_eq_mul_inv, pow_add, inv_pow, one_mul]
  ring

end ThesisCommon.NormalizedSchauderBasis

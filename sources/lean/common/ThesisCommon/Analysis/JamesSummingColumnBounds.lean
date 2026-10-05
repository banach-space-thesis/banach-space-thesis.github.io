import ThesisCommon.Analysis.JamesConstantPrefixes
import ThesisCommon.Analysis.JamesSchauderBasis

/-! Summable coordinate and summing-basis-column bounds on the actual James
space. Ordered partial sums, rather than unconditional expansions, are used. -/
noncomputable section
open Filter Topology
open scoped ENNReal BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜] (p : BanachExponent) (hp : p.val ≠ ∞)

theorem jamesUnit_norm_le_two (n : ℕ) : ‖jamesUnit (𝕜 := 𝕜) p hp n‖ ≤ 2 := by
  have h := (lpToJames (𝕜 := 𝕜) p hp).le_opNorm (lp.single p.val n (1 : 𝕜))
  have hu : ‖(lp.single p.val n (1 : 𝕜) : SequenceSum p 𝕜)‖ = 1 := by
    rw [lp.norm_single (zero_lt_one.trans_le p.property), norm_one]
  simpa only [jamesUnit, hu, mul_one] using h.trans
    (mul_le_mul_of_nonneg_right (norm_lpToJames_le (𝕜 := 𝕜) p hp) (norm_nonneg _))

include hp in
theorem james_norm_le_two_tsum_of_coordinates (x : JamesSequenceSpace 𝕜 p)
    (a : ℕ → ℝ) (ha : Summable a) (ha0 : ∀ n, 0 ≤ a n)
    (hx : ∀ n, ‖x n‖ ≤ a n) : ‖x‖ ≤ 2 * ∑' n, a n := by
  apply le_of_tendsto (james_finite_units_tendsto p hp x).norm
  apply Eventually.of_forall
  intro N
  calc
    ‖∑ n ∈ Finset.range N, x n • jamesUnit p hp n‖ ≤
        ∑ n ∈ Finset.range N, ‖x n • jamesUnit p hp n‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.range N, 2 * a n := by
      apply Finset.sum_le_sum
      intro n _
      rw [norm_smul, mul_comm (2 : ℝ)]
      exact mul_le_mul (hx n) (jamesUnit_norm_le_two p hp n) (norm_nonneg _) (ha0 n)
    _ = 2 * ∑ n ∈ Finset.range N, a n := (Finset.mul_sum _ _ _).symm
    _ ≤ 2 * ∑' n, a n := mul_le_mul_of_nonneg_left
      (ha.sum_le_tsum (Finset.range N) (fun n _ => ha0 n)) (by norm_num)

theorem james_summing_partial_sum (x : JamesSequenceSpace 𝕜 p) (N : ℕ) :
    ∑ n ∈ Finset.range (N+1), (x n - x (n+1)) • jamesConstantPrefix p hp n =
      JamesSequenceSpace.initial (𝕜 := 𝕜) (p := p) N x - x (N+1) • jamesConstantPrefix p hp N := by
  classical
  induction N with
  | zero =>
      simp only [Nat.zero_add, Finset.sum_range_one]
      ext k
      simp only [JamesSequenceSpace.smul_apply, JamesSequenceSpace.sub_apply,
        JamesSequenceSpace.initial_apply, jamesConstantPrefix_apply, smul_eq_mul]
      by_cases hk : k = 0
      · subst k; simp
      · simp [hk]
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      ext k
      simp only [JamesSequenceSpace.add_apply, JamesSequenceSpace.smul_apply,
        JamesSequenceSpace.sub_apply, JamesSequenceSpace.initial_apply,
        jamesConstantPrefix_apply, smul_eq_mul]
      by_cases hk : k ≤ N
      · simp only [if_pos hk, if_pos (hk.trans (Nat.le_succ N))]; ring
      · by_cases hk' : k ≤ N+1
        · have heq : k = N+1 := by omega
          subst k
          simp
        · simp [hk, hk']

theorem james_summing_expansion_tendsto (x : JamesSequenceSpace 𝕜 p) :
    Tendsto (fun N => ∑ n ∈ Finset.range (N+1),
      (x n - x (n+1)) • jamesConstantPrefix p hp n) atTop (𝓝 x) := by
  have hx : Tendsto (fun N => x (N+1)) atTop (𝓝 (0 : 𝕜)) :=
    (tendsto_add_atTop_iff_nat 1).mpr x.tendsto_zero
  have hz : Tendsto (fun N => x (N+1) • jamesConstantPrefix p hp N) atTop
      (𝓝 (0 : JamesSequenceSpace 𝕜 p)) := by
    apply squeeze_zero_norm (fun N => ?_) (by simpa only [norm_zero] using hx.norm)
    rw [norm_smul]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (jamesConstantPrefix_norm_le (𝕜 := 𝕜) p hp N) (norm_nonneg _)
  simpa only [james_summing_partial_sum, sub_zero] using
    (JamesSequenceSpace.initial_tendsto hp x).sub hz

theorem james_operator_norm_le_two_tsum_summing_columns
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (A : JamesSequenceSpace 𝕜 p →L[𝕜] Y)
    (hA : Summable (fun n => ‖A (jamesConstantPrefix p hp n)‖)) :
    ‖A‖ ≤ 2 * ∑' n, ‖A (jamesConstantPrefix p hp n)‖ := by
  apply ContinuousLinearMap.opNorm_le_bound A
    (mul_nonneg (by norm_num) (tsum_nonneg (fun n => norm_nonneg _)))
  intro x
  apply le_of_tendsto ((A.continuous.tendsto x).comp
    (james_summing_expansion_tendsto p hp x)).norm
  apply Eventually.of_forall
  intro N
  dsimp only [Function.comp_apply]
  rw [map_sum]
  simp only [map_smul]
  calc
    ‖∑ n ∈ Finset.range (N+1), (x n - x (n+1)) • A (jamesConstantPrefix p hp n)‖ ≤
        ∑ n ∈ Finset.range (N+1), ‖(x n - x (n+1)) • A (jamesConstantPrefix p hp n)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.range (N+1), (2 * ‖x‖) * ‖A (jamesConstantPrefix p hp n)‖ := by
      apply Finset.sum_le_sum
      intro n _
      rw [norm_smul]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact (norm_sub_le _ _).trans (by
        have h := add_le_add (x.norm_apply_le n) (x.norm_apply_le (n+1))
        simpa only [two_mul] using h)
    _ = (2 * ‖x‖) * ∑ n ∈ Finset.range (N+1), ‖A (jamesConstantPrefix p hp n)‖ :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (2 * ‖x‖) * ∑' n, ‖A (jamesConstantPrefix p hp n)‖ :=
      mul_le_mul_of_nonneg_left
        (hA.sum_le_tsum (Finset.range (N+1)) (fun n _ => norm_nonneg _)) (by positivity)
    _ = _ := by ring

end ThesisCommon

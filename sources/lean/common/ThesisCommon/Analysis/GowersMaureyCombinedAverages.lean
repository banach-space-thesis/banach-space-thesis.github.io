import ThesisCommon.Analysis.GowersMaureyNormingForms
import ThesisCommon.Analysis.GowersMaureyCompletedPairing

/-! The actual combined averaged functional used in source Lemma 9.
Its dual bound follows from the lower-f norming rule. The numerical bound
f(k*N)/f(N) ≤ 2 is proved for k ≤ N, including k = 0. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem logarithmicWeight_mul_nat_le_two {k N : ℕ} (hk : k ≤ N) :
    logarithmicWeight ((k * N : ℕ) : ℝ) ≤ 2 * logarithmicWeight N := by
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hk' : (k : ℝ) ≤ N := Nat.cast_le.mpr hk
  have harg : (k : ℝ) * N + 1 ≤ ((N : ℝ) + 1)^2 := by nlinarith
  have hlog := Real.log_le_log (by positivity : 0 < (k : ℝ) * N + 1) harg
  rw [Real.log_pow] at hlog
  unfold logarithmicWeight
  simpa only [Nat.cast_mul] using
    (div_le_div_of_nonneg_right hlog hL.le).trans_eq (by ring)

theorem successive_scaled_sum_pairing_bound (D : ConstructionData 𝕜)
    {M N : ℕ} (hM : 0 < M) (z : Fin M → C00 𝕜)
    (hz : Successive z) (hunit : ∀ i, DualUnit (implicitNorm D) (z i))
    (x : C00 𝕜) :
    ‖pairing ((logarithmicWeight N)⁻¹ • ∑ i, z i) x‖ ≤
      (logarithmicWeight M / logarithmicWeight N) * implicitNorm D x := by
  have hfM : 0 < logarithmicWeight M := zero_lt_one.trans_le (one_le_logarithmicWeight hM)
  have hfN : 0 ≤ (logarithmicWeight N)⁻¹ :=
    inv_nonneg.mpr (logarithmicWeight_nonneg N)
  have hsum := successive_pairing_sum_le D hz zero_le_one
    (fun i y => by simpa only [one_mul] using hunit i y) x
  have hi : intervalNorm D M x ≤ logarithmicWeight M * implicitNorm D x := by
    exact ((div_le_iff₀ hfM).mp (by
      simpa only [inv_mul_eq_div] using intervalNorm_lower_f D hM x)).trans_eq (mul_comm _ _)
  rw [pairing_real_smul_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hfN]
  calc
    _ ≤ (logarithmicWeight N)⁻¹ * intervalNorm D M x :=
      mul_le_mul_of_nonneg_left (by simpa only [one_mul] using hsum) hfN
    _ ≤ (logarithmicWeight N)⁻¹ * (logarithmicWeight M * implicitNorm D x) :=
      mul_le_mul_of_nonneg_left hi hfN
    _ = _ := by ring

theorem combined_average_pairing_bound (D : ConstructionData 𝕜)
    {k N : ℕ} (hN : 0 < N) (hk : k ≤ N) (z : Fin (k * N) → C00 𝕜)
    (hz : Successive z) (hunit : ∀ i, DualUnit (implicitNorm D) (z i))
    (x : C00 𝕜) :
    ‖pairing ((logarithmicWeight N)⁻¹ • ∑ i, z i) x‖ ≤ 2 * implicitNorm D x := by
  by_cases hk0 : k = 0
  · subst k
    have hsum : (∑ i, z i) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      have := i.isLt
      omega
    rw [hsum, smul_zero]
    have he : pairing (0 : C00 𝕜) = (0 : C00 𝕜 →ₗ[𝕜] 𝕜) := by
      apply Finsupp.lhom_ext
      intro i c
      simp [pairing_single]
    rw [he, LinearMap.zero_apply, norm_zero]
    exact mul_nonneg (by norm_num) (apply_nonneg _ _)
  · have hfN : 0 < logarithmicWeight N := zero_lt_one.trans_le (one_le_logarithmicWeight hN)
    have hratio : logarithmicWeight ((k * N : ℕ) : ℝ) / logarithmicWeight N ≤ 2 :=
      (div_le_iff₀ hfN).mpr (logarithmicWeight_mul_nat_le_two hk)
    exact (successive_scaled_sum_pairing_bound D
      (Nat.mul_pos (Nat.pos_of_ne_zero hk0) hN) z hz hunit x).trans
      (mul_le_mul_of_nonneg_right hratio (apply_nonneg _ _))

theorem combined_average_completedPairing_bound (D : ConstructionData 𝕜)
    {k N : ℕ} (hN : 0 < N) (hk : k ≤ N) (z : Fin (k * N) → C00 𝕜)
    (hz : Successive z) (hunit : ∀ i, DualUnit (implicitNorm D) (z i))
    (x : ShiftSpace D) :
    ‖completedPairing D ((logarithmicWeight N)⁻¹ • ∑ i, z i) x‖ ≤ 2 * ‖x‖ := by
  refine (denseEmbedding_denseRange D).induction_on x ?_ ?_
  · exact isClosed_le (completedPairing D _).continuous.norm
      (continuous_const.mul continuous_norm)
  · intro y
    rw [completedPairing_denseEmbedding, denseEmbedding_norm]
    exact combined_average_pairing_bound D hN hk z hz hunit y

theorem norm_combined_average_completedPairing_le_two (D : ConstructionData 𝕜)
    {k N : ℕ} (hN : 0 < N) (hk : k ≤ N) (z : Fin (k * N) → C00 𝕜)
    (hz : Successive z) (hunit : ∀ i, DualUnit (implicitNorm D) (z i)) :
    ‖completedPairing D ((logarithmicWeight N)⁻¹ • ∑ i, z i)‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  exact combined_average_completedPairing_bound D hN hk z hz hunit

end ThesisCommon.GowersMaurey

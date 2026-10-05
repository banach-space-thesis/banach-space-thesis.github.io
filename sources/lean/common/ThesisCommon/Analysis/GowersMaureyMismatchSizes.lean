import ThesisCommon.Analysis.GowersMaureyNPairSizes
import ThesisCommon.Analysis.GowersMaureyRapidProducts
import ThesisCommon.Analysis.GowersMaureyLogExterior

/-! Quantitative rapid-size bounds for the mismatched averages in Lemma 8.
The cutoff is an actual construction size, not an assumed growth property
of the coding map. All comparisons of source sizes are explicit. -/
noncomputable section
namespace ThesisCommon.GowersMaurey

theorem log_le_logarithmicWeight {x : ℝ} (hx : 1 ≤ x) :
    Real.log x ≤ logarithmicWeight x := by
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL1 : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hh := Real.log_le_log (zero_lt_one.trans_le hx) (show x ≤ x+1 by linarith)
  rw [logarithmicWeight, le_div_iff₀ hL]
  nlinarith [mul_nonneg (Real.log_nonneg hx) (show 0 ≤ 1-Real.log 2 by linarith)]

theorem logarithmicWeight_le_three_sqrt {x : ℝ} (hx : 1 ≤ x) :
    logarithmicWeight x ≤ 3 * Real.sqrt x := by
  have hs := Real.sqrt_nonneg x
  have hs1 : 1 ≤ Real.sqrt x := Real.one_le_sqrt.mpr hx
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : Real.log x / Real.log 2 ≤ 2*Real.sqrt x := by
    apply (div_le_iff₀ hL).mpr
    have hh := log_le_sqrt_of_pos (zero_lt_one.trans_le hx)
    nlinarith [mul_nonneg hs (show 0 ≤ 2*Real.log 2-1 by linarith [log_two_half_le])]
  have hh := logarithmicWeight_le_log_bound hx
  linarith

theorem three_logarithmicWeight_div_le_inv_square {k N : ℝ}
    (hk : 4 ≤ k) (hN : k^8 ≤ N) :
    3 * logarithmicWeight N / N ≤ 1 / k^2 := by
  have hk0 : 0 < k := by linarith
  have hN0 : 0 < N := (pow_pos hk0 8).trans_le hN
  have hN1 : 1 ≤ N := (one_le_pow₀ (by linarith : 1 ≤ k)).trans hN
  have hs : 0 ≤ Real.sqrt N := Real.sqrt_nonneg N
  have hroot : k^4 ≤ Real.sqrt N := by
    apply (sq_le_sq₀ (by positivity) hs).mp
    rw [Real.sq_sqrt hN0.le]
    simpa only [← pow_mul] using hN
  have hscale : 9*k^2 ≤ k^4 := by
    have hsq : 9 ≤ k^2 := by nlinarith
    nlinarith [mul_nonneg (sq_nonneg k) (show 0 ≤ k^2-9 by linarith)]
  have hbound : 3 * logarithmicWeight N * k^2 ≤ N := by
    calc
      _ ≤ 3 * (3*Real.sqrt N) * k^2 := by
        gcongr
        exact logarithmicWeight_le_three_sqrt hN1
      _ = Real.sqrt N * (9*k^2) := by ring
      _ ≤ Real.sqrt N * Real.sqrt N := mul_le_mul_of_nonneg_left (hscale.trans hroot) hs
      _ = N := Real.mul_self_sqrt hN0.le
  apply (div_le_div_iff₀ hN0 (sq_pos_of_pos hk0)).mpr
  simpa only [one_mul] using hbound

namespace ConstructionData
variable {𝕜 : Type*} [RCLike 𝕜] (D : ConstructionData 𝕜)

theorem size_pow_eight_le_weight {m n : ℕ} (hmn : m < n) :
    (D.j m : ℝ)^8 ≤ logarithmicWeight (D.j n) :=
  (D.size_pow_eight_lt_loglog hmn).le.trans
    ((Real.log_le_self (Real.log_nonneg (D.one_le_size n))).trans
      (log_le_logarithmicWeight (D.one_le_size n)))

theorem size_pow_eight_le_size {m n : ℕ} (hmn : m < n) :
    (D.j m : ℝ)^8 ≤ D.j n :=
  (D.size_pow_eight_le_weight hmn).trans (logarithmicWeight_le_self_real (D.one_le_size n))

theorem three_weight_div_size_le_inv_square {k n : ℕ} (hkn : k < n) :
    3 * logarithmicWeight (D.j n) / (D.j n : ℝ) ≤ 1 / (D.j k : ℝ)^2 :=
  three_logarithmicWeight_div_le_inv_square (by have h := D.size_large k; linarith)
    (D.size_pow_eight_le_size hkn)

theorem eight_div_weight_le_inv_square {k m : ℕ} (hkm : k < m) :
    8 / logarithmicWeight (D.j m) ≤ 1 / (D.j k : ℝ)^2 := by
  have hk0 : (0 : ℝ) < D.j k := by exact_mod_cast D.j_positive k
  have hM : 0 < logarithmicWeight (D.j m) := zero_lt_one.trans_le
    (one_le_logarithmicWeight (D.j_positive m))
  have hsq : (8 : ℝ) ≤ (D.j k : ℝ)^2 := by have h := D.size_large k; nlinarith
  have hfour : 8*(D.j k : ℝ)^2 ≤ (D.j k : ℝ)^4 := by
    nlinarith [mul_nonneg (sq_nonneg (D.j k : ℝ))
      (show 0 ≤ (D.j k : ℝ)^2-8 by linarith)]
  have he : (D.j k : ℝ)^4 ≤ (D.j k : ℝ)^8 :=
    pow_le_pow_right₀ (D.one_le_size k) (by norm_num)
  apply (div_le_div_iff₀ hM (sq_pos_of_pos hk0)).mpr
  simpa only [one_mul] using hfour.trans (he.trans (D.size_pow_eight_le_weight hkm))

theorem size_div_sqrt_weight_le_one {n m : ℕ} (hnm : n < m) :
    (D.j n : ℝ) / Real.sqrt (logarithmicWeight (D.j m)) ≤ 1 := by
  have hf : 0 < logarithmicWeight (D.j m) := zero_lt_one.trans_le
    (one_le_logarithmicWeight (D.j_positive m))
  apply (div_le_one (Real.sqrt_pos.mpr hf)).mpr
  apply (sq_le_sq₀ (Nat.cast_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt hf.le]
  exact (pow_le_pow_right₀ (D.one_le_size n) (by norm_num : 2 ≤ 8)).trans
    (D.size_pow_eight_le_weight hnm)

theorem size_le_sqrt_size {m n : ℕ} (hmn : m < n) :
    (D.j m : ℝ) ≤ Real.sqrt (D.j n : ℝ) := by
  apply (sq_le_sq₀ (Nat.cast_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt (Nat.cast_nonneg _)]
  exact D.size_sq_le_of_lt hmn

end ConstructionData
end ThesisCommon.GowersMaurey

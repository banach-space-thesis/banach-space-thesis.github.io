import ThesisCommon.Analysis.GowersMaureyInterpolationProfiles

/-! The upper side of the interpolation gap: a later selected size,
separated by the actual triple-logarithmic condition, has square-root
logarithmic cost above every point up to the double exponential cutoff. -/
noncomputable section
namespace ThesisCommon.GowersMaurey

theorem logarithmicWeight_le_three_exp {N x : ℝ} (hN : 0 ≤ N)
    (hx : 1 ≤ x) (hupper : x ≤ Real.exp (Real.exp N)) :
    logarithmicWeight x ≤ 3 * Real.exp N := by
  have he : 1 ≤ Real.exp N := Real.one_le_exp hN
  have hl : Real.log x ≤ Real.exp N := by
    have hh := Real.log_le_log (zero_lt_one.trans_le hx) hupper
    simpa only [Real.log_exp] using hh
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh
    linarith
  have hdiv : Real.log x / Real.log 2 ≤ 2 * Real.exp N := by
    apply (div_le_iff₀ (Real.log_pos (by norm_num))).mpr
    have hh := mul_le_mul_of_nonneg_left hlog2 (Real.exp_pos N).le
    nlinarith
  exact (logarithmicWeight_le_log_bound hx).trans (by linarith)

theorem sqrt_weight_ge_of_triple_log_gap {N k x : ℝ}
    (hN : 9 ≤ N) (hk : 16 ≤ k)
    (hsep : 2 * N < Real.log (Real.log (Real.log k)))
    (hx : 1 ≤ x) (hupper : x ≤ Real.exp (Real.exp N)) :
    logarithmicWeight x ≤ Real.sqrt (logarithmicWeight k) := by
  have hk1 : 1 < k := by linarith
  have hlogk : 0 < Real.log k := Real.log_pos hk1
  have hloglog : 0 < Real.log (Real.log k) := by
    apply Real.log_pos
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 16) hk
    have h16 : Real.log 16 = 4 * Real.log 2 := by
      rw [show (16 : ℝ) = 2^4 by norm_num, Real.log_pow]
      norm_num
    rw [h16] at hh
    have hb := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hb
    linarith
  have he1 : Real.exp (2 * N) < Real.log (Real.log k) :=
    (Real.lt_log_iff_exp_lt hloglog).mp hsep
  have he2 : Real.exp (Real.exp (2 * N)) < Real.log k :=
    (Real.lt_log_iff_exp_lt hlogk).mp he1
  have heN : 0 < Real.exp N := Real.exp_pos N
  have he2N : 18 ≤ Real.exp (2 * N) := by
    have hh := Real.add_one_le_exp (2 * N)
    linarith
  have hquad := Real.quadratic_le_exp_of_nonneg (Real.exp_pos (2 * N)).le
  have hpoly : 9 * Real.exp (2 * N) ≤ Real.exp (Real.exp (2 * N)) := by
    nlinarith [mul_nonneg (Real.exp_pos (2 * N)).le (sub_nonneg.mpr he2N)]
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2one : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh
    exact hh
  have hlogmono : Real.log k ≤ Real.log (k + 1) := Real.log_le_log (by linarith) (by linarith)
  have hf : Real.log k ≤ logarithmicWeight k := by
    unfold logarithmicWeight
    apply (le_div_iff₀ hlog2pos).mpr
    exact (mul_le_mul_of_nonneg_left hlog2one hlogk.le).trans (by simpa using hlogmono)
  have hxbound := logarithmicWeight_le_three_exp (by linarith : 0 ≤ N) hx hupper
  have hexp : Real.exp (2 * N) = (Real.exp N)^2 := by
    rw [show 2 * N = N + N by ring, Real.exp_add, pow_two]
  have hxsq : (logarithmicWeight x)^2 ≤ logarithmicWeight k := by
    rw [hexp] at hpoly
    have hxnonneg := zero_le_one.trans (one_le_logarithmicWeight_real hx)
    nlinarith [sq_nonneg (3 * Real.exp N - logarithmicWeight x)]
  exact (Real.le_sqrt (zero_le_one.trans (one_le_logarithmicWeight_real hx))
    (zero_le_one.trans (one_le_logarithmicWeight_real hk1.le))).mpr hxsq

end ThesisCommon.GowersMaurey

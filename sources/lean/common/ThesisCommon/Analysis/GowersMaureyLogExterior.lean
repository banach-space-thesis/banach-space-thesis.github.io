import ThesisCommon.Analysis.GowersMaureyLogTangentBounds
import Mathlib.Analysis.SpecialFunctions.Exp

/-! Concrete exterior comparisons for the interpolation tangent. The
thresholds are deliberately explicit, so the rapid-size hypotheses can
be checked rather than hidden in an eventual-growth assumption. -/
noncomputable section
namespace ThesisCommon.GowersMaurey

theorem log_two_half_le : (1 / 2 : ℝ) ≤ Real.log 2 := by
  have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
  norm_num at hh
  exact hh

theorem log_two_le_one : Real.log 2 ≤ 1 := by
  simpa only [show (2 : ℝ) - 1 = 1 by norm_num] using
    Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)

theorem exp_ge_sixteen_add_one_sq {t : ℝ} (ht : 64 ≤ t) :
    16 * (t + 1)^2 ≤ Real.exp t := by
  have ht0 : 0 ≤ t := by linarith
  have ht2 : 4096 ≤ t^2 := by nlinarith
  have ha : (t + 1)^2 ≤ 4 * t^2 := by nlinarith
  have hb := mul_le_mul_of_nonneg_right (show (1536 : ℝ) ≤ t^2 by linarith) (sq_nonneg t)
  have hc : 64 * t^2 ≤ t^4 / 24 := by nlinarith
  have he := Real.pow_div_factorial_le_exp t ht0 4
  norm_num [Nat.factorial] at he
  exact (show 16 * (t + 1)^2 ≤ t^4 / 24 by nlinarith).trans he

theorem exp_ge_eight_self_add_one_sq {t : ℝ} (ht : 64 ≤ t) :
    8 * t * (t + 1)^2 ≤ Real.exp t := by
  have ht0 : 0 ≤ t := by linarith
  have ht2 : 4096 ≤ t^2 := by nlinarith
  have ha : (t + 1)^2 ≤ 4 * t^2 := by nlinarith
  have hb := mul_le_mul_of_nonneg_left ha (show 0 ≤ 8 * t by positivity)
  have hc := mul_le_mul_of_nonneg_right (show (3840 : ℝ) ≤ t^2 by linarith) (pow_nonneg ht0 3)
  have hd : 8 * t * (t + 1)^2 ≤ t^5 / 120 := by nlinarith
  have he := Real.pow_div_factorial_le_exp t ht0 5
  norm_num [Nat.factorial] at he
  exact hd.trans he

theorem logarithmicWeight_le_twice_log_add_one {s : ℝ} (hs : 1 ≤ s) :
    logarithmicWeight s ≤ 2 * (Real.log s + 1) := by
  have hsp : 0 < s := zero_lt_one.trans_le hs
  have hLp : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog := Real.log_le_log (by linarith : 0 < s + 1) (show s + 1 ≤ 2 * s by linarith)
  rw [Real.log_mul (by norm_num) hsp.ne'] at hlog
  have hq : 0 ≤ Real.log s + 1 := by linarith [Real.log_nonneg hs]
  unfold logarithmicWeight
  apply (div_le_iff₀ hLp).mpr
  have hh := mul_nonneg hq (show 0 ≤ 2 * Real.log 2 - 1 by linarith [log_two_half_le])
  nlinarith [log_two_le_one]

theorem log_le_half_profile_square {s : ℝ} (hs : 1 ≤ s) (hlog : 64 ≤ Real.log s) :
    Real.log s ≤ s / (2 * (logarithmicWeight s)^2) := by
  have hsp : 0 < s := zero_lt_one.trans_le hs
  have hfp : 0 < logarithmicWeight s :=
    div_pos (Real.log_pos (by linarith)) (Real.log_pos (by norm_num))
  have hf := logarithmicWeight_le_twice_log_add_one hs
  have hfsq : (logarithmicWeight s)^2 ≤ 4 * (Real.log s + 1)^2 := by
    have hh := mul_self_le_mul_self hfp.le hf
    nlinarith
  have he := exp_ge_eight_self_add_one_sq hlog
  rw [Real.exp_log hsp] at he
  have hh := mul_le_mul_of_nonneg_left hfsq (show 0 ≤ 2 * Real.log s by linarith)
  exact (le_div_iff₀ (by positivity)).mpr (by nlinarith)

theorem log_ge_two_of_ge_sixteen {s : ℝ} (hs : 16 ≤ s) : 2 ≤ Real.log s := by
  have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 16) hs
  have h16 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2^4 by norm_num, Real.log_pow]
    norm_num
  rw [h16] at hh
  linarith [log_two_half_le]

theorem sqrtLogarithmicProfile_le_tangent_below_log_log {N s x : ℝ}
    (hN : 64 ≤ N) (hs : 1 ≤ s) (hsN : Real.log N ≤ s)
    (hlarge : 64 ≤ Real.log (Real.log N)) (hx : 1 ≤ x)
    (hxN : x ≤ Real.log (Real.log N)) :
    sqrtLogarithmicProfile x ≤ logarithmicProfileTangent s x := by
  have hNp : 1 < N := by linarith
  have hl : Real.log (Real.log N) ≤ Real.log s :=
    Real.log_le_log (Real.log_pos hNp) hsN
  exact sqrtLogarithmicProfile_le_tangent_of_small hs hx
    (hxN.trans (hl.trans (log_le_half_profile_square hs (hlarge.trans hl))))

theorem logarithmicWeight_le_twice_exp_parameter {N s : ℝ}
    (hN : 0 ≤ N) (hs : 1 ≤ s) (hsN : s ≤ Real.exp N) :
    logarithmicWeight s ≤ 2 * (N + 1) := by
  have hLp : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog := Real.log_le_log (by linarith : 0 < s + 1)
    (show s + 1 ≤ 2 * Real.exp N by linarith)
  rw [Real.log_mul (by norm_num) (Real.exp_pos N).ne', Real.log_exp] at hlog
  unfold logarithmicWeight
  apply (div_le_iff₀ hLp).mpr
  have hh := mul_nonneg (show 0 ≤ N + 1 by linarith)
    (show 0 ≤ 2 * Real.log 2 - 1 by linarith [log_two_half_le])
  nlinarith [log_two_le_one]

theorem exp_parameter_le_logarithmicWeight {N x : ℝ}
    (hx : Real.exp (Real.exp N) ≤ x) :
    Real.exp N ≤ logarithmicWeight x := by
  have hLp : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog := Real.log_le_log (Real.exp_pos (Real.exp N))
    (show Real.exp (Real.exp N) ≤ x + 1 by linarith)
  rw [Real.log_exp] at hlog
  unfold logarithmicWeight
  apply (le_div_iff₀ hLp).mpr
  exact (mul_le_mul_of_nonneg_left log_two_le_one (Real.exp_pos N).le).trans
    (by simpa only [mul_one] using hlog)

theorem sqrtLogarithmicProfile_le_tangent_above_exp_exp {N s x : ℝ}
    (hN : 64 ≤ N) (hs : 16 ≤ s) (hsN : s ≤ Real.exp N)
    (hx : Real.exp (Real.exp N) ≤ x) :
    sqrtLogarithmicProfile x ≤ logarithmicProfileTangent s x := by
  have hs1 : 1 ≤ s := by linarith
  have hx1 : 1 ≤ x :=
    (Real.one_lt_exp_iff.mpr (Real.exp_pos N)).le.trans hx
  have hf := logarithmicWeight_le_twice_exp_parameter (by linarith) hs1 hsN
  have hfp : 0 < logarithmicWeight s :=
    div_pos (Real.log_pos (by linarith)) (Real.log_pos (by norm_num))
  have hfsq : (logarithmicWeight s)^2 ≤ 4 * (N + 1)^2 := by
    have hh := mul_self_le_mul_self hfp.le hf
    nlinarith
  apply sqrtLogarithmicProfile_le_tangent_of_large hs1 hx1
    (log_ge_two_of_ge_sixteen (by linarith : 16 ≤ s + 1))
  exact (show 4 * (logarithmicWeight s)^2 ≤ 16 * (N + 1)^2 by nlinarith).trans
    ((exp_ge_sixteen_add_one_sq hN).trans (exp_parameter_le_logarithmicWeight hx))

end ThesisCommon.GowersMaurey

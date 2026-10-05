import ThesisCommon.Analysis.GowersMaureyLogTangent

/-! Explicit bounds for the true tangent of x/log₂(x+1). The exterior
criteria state only elementary size inequalities, leaving their source
rapid-sequence instantiation to the interpolation gap argument. -/
noncomputable section
namespace ThesisCommon.GowersMaurey

theorem logarithmicProfileSlope_eq_scaled {s : ℝ} (hs : 0 < s) :
    logarithmicProfileSlope s = Real.log 2 * rawLogarithmicProfileDeriv s := by
  have hsp : 0 < s + 1 := by linarith
  have hlp : 0 < Real.log (s + 1) := Real.log_pos (by linarith)
  unfold logarithmicProfileSlope rawLogarithmicProfileDeriv
  field_simp [hsp.ne', hlp.ne']

theorem logarithmicProfileSlope_nonneg {s : ℝ} (hs : 1 ≤ s) :
    0 ≤ logarithmicProfileSlope s := by
  rw [logarithmicProfileSlope_eq_scaled (zero_lt_one.trans_le hs)]
  exact mul_nonneg (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))
    (rawLogarithmicProfileDeriv_nonneg hs)

theorem logarithmicProfileSlope_le_one {s : ℝ} (hs : 1 ≤ s) :
    logarithmicProfileSlope s ≤ 1 := by
  have hsp : 0 < s + 1 := by linarith
  have hlp : 0 < Real.log (s + 1) := Real.log_pos (by linarith)
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : Real.log 2 ≤ Real.log (s + 1) :=
    Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by linarith)
  unfold logarithmicProfileSlope
  calc
    Real.log 2 / Real.log (s + 1) * (1 - s / ((s + 1) * Real.log (s + 1)))
        ≤ Real.log 2 / Real.log (s + 1) * 1 :=
      mul_le_mul_of_nonneg_left (by
        have hq : 0 ≤ s / ((s + 1) * Real.log (s + 1)) := by positivity
        linarith)
        (div_nonneg hL.le hlp.le)
    _ ≤ 1 := by rw [mul_one]; exact (div_le_one hlp).mpr hlog

theorem logarithmicProfileIntercept_nonneg {s : ℝ} (hs : 1 ≤ s) :
    0 ≤ logarithmicProfileIntercept s := by
  unfold logarithmicProfileIntercept
  positivity

theorem logarithmicProfileTangent_ge_intercept {s x : ℝ} (hs : 1 ≤ s) (hx : 0 ≤ x) :
    logarithmicProfileIntercept s ≤ logarithmicProfileTangent s x := by
  unfold logarithmicProfileTangent
  exact le_add_of_nonneg_right (mul_nonneg (logarithmicProfileSlope_nonneg hs) hx)

theorem logarithmicProfile_one : logarithmicProfile 1 = 1 := by
  have hL : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  simp only [logarithmicProfile, logarithmicWeight, one_add_one_eq_two, div_self hL, div_one]

theorem logarithmicProfileTangent_ge_identity_below_one {s x : ℝ}
    (hs : 1 ≤ s) (hx : x ≤ 1) : x ≤ logarithmicProfileTangent s x := by
  have h1 := logarithmicProfile_le_tangent hs (le_refl 1)
  rw [logarithmicProfile_one] at h1
  have hd := logarithmicProfileSlope_le_one hs
  have ha : logarithmicProfileTangent s x - x =
      (logarithmicProfileTangent s 1 - 1) + (logarithmicProfileSlope s - 1) * (x - 1) := by
    unfold logarithmicProfileTangent
    ring
  have hh := mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hd) (sub_nonpos.mpr hx)
  have hb := add_nonneg (sub_nonneg.mpr h1) hh
  rw [← ha] at hb
  exact sub_nonneg.mp hb

theorem logarithmicProfileIntercept_ge {s : ℝ} (hs : 1 ≤ s) :
    s / (2 * (logarithmicWeight s)^2) ≤ logarithmicProfileIntercept s := by
  have hsp : 0 < s + 1 := by linarith
  have hlp : 0 < Real.log (s + 1) := Real.log_pos (by linarith)
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL1 : Real.log 2 ≤ 1 := by
    simpa only [show (2 : ℝ) - 1 = 1 by norm_num] using
      Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have hfp : 0 < logarithmicWeight s := div_pos hlp hL
  have heq : logarithmicProfileIntercept s =
      s^2 / ((s + 1) * Real.log 2 * (logarithmicWeight s)^2) := by
    unfold logarithmicProfileIntercept logarithmicWeight
    field_simp [hsp.ne', hlp.ne', hL.ne']
  rw [heq]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have hbase : s * (s + 1) * Real.log 2 ≤ 2 * s^2 := by
    have hh := mul_le_mul_of_nonneg_left hL1 (show 0 ≤ s * (s + 1) by positivity)
    nlinarith [mul_nonneg (show 0 ≤ s by linarith) (sub_nonneg.mpr hs)]
  have hh := mul_le_mul_of_nonneg_right hbase (sq_nonneg (logarithmicWeight s))
  nlinarith

theorem logarithmicProfileSlope_ge_half_inverse {s : ℝ} (hs : 1 ≤ s)
    (hlog : 2 ≤ Real.log (s + 1)) :
    1 / (2 * logarithmicWeight s) ≤ logarithmicProfileSlope s := by
  have hsp : 0 < s + 1 := by linarith
  have hlp : 0 < Real.log (s + 1) := by linarith
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hq : s / ((s + 1) * Real.log (s + 1)) ≤ (1 / 2 : ℝ) := by
    apply (div_le_iff₀ (mul_pos hsp hlp)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hlog hsp.le]
  have hh := mul_le_mul_of_nonneg_left (show (1 / 2 : ℝ) ≤ 1 - s / ((s + 1) * Real.log (s + 1)) by linarith)
    (div_nonneg hL.le hlp.le)
  unfold logarithmicProfileSlope
  convert hh using 1
  unfold logarithmicWeight
  field_simp [hL.ne', hlp.ne']

theorem logarithmicProfileTangent_ge_half_linear {s x : ℝ} (hs : 1 ≤ s)
    (hlog : 2 ≤ Real.log (s + 1)) (hx : 0 ≤ x) :
    x / (2 * logarithmicWeight s) ≤ logarithmicProfileTangent s x := by
  have hh := mul_le_mul_of_nonneg_right (logarithmicProfileSlope_ge_half_inverse hs hlog) hx
  unfold logarithmicProfileTangent
  have heq : x / (2 * logarithmicWeight s) = (1 / (2 * logarithmicWeight s)) * x := by ring
  rw [heq]
  exact hh.trans (le_add_of_nonneg_left (logarithmicProfileIntercept_nonneg hs))

theorem sqrtLogarithmicProfile_le_tangent_of_small {s x : ℝ}
    (hs : 1 ≤ s) (hx : 1 ≤ x)
    (hsmall : x ≤ s / (2 * (logarithmicWeight s)^2)) :
    sqrtLogarithmicProfile x ≤ logarithmicProfileTangent s x :=
  (sqrtLogarithmicProfile_le_self hx).trans (hsmall.trans
    ((logarithmicProfileIntercept_ge hs).trans
      (logarithmicProfileTangent_ge_intercept hs (zero_le_one.trans hx))))

theorem sqrtLogarithmicProfile_le_tangent_of_large {s x : ℝ}
    (hs : 1 ≤ s) (hx : 1 ≤ x) (hlog : 2 ≤ Real.log (s + 1))
    (hlarge : 4 * (logarithmicWeight s)^2 ≤ logarithmicWeight x) :
    sqrtLogarithmicProfile x ≤ logarithmicProfileTangent s x := by
  have hfp : 0 < logarithmicWeight s :=
    div_pos (Real.log_pos (by linarith)) (Real.log_pos (by norm_num))
  have hroot : 2 * logarithmicWeight s ≤ Real.sqrt (logarithmicWeight x) := by
    apply (Real.le_sqrt (by positivity) (by nlinarith [sq_nonneg (logarithmicWeight s)])).mpr
    nlinarith
  have hden : 0 < Real.sqrt (logarithmicWeight x) := lt_of_lt_of_le (by positivity : 0 < 2 * logarithmicWeight s) hroot
  have hh : x / Real.sqrt (logarithmicWeight x) ≤ x / (2 * logarithmicWeight s) := by
    apply (div_le_div_iff₀ hden (by positivity)).mpr
    exact mul_le_mul_of_nonneg_left hroot (zero_le_one.trans hx)
  exact hh.trans (logarithmicProfileTangent_ge_half_linear hs hlog (zero_le_one.trans hx))

end ThesisCommon.GowersMaurey

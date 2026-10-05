import ThesisCommon.Analysis.GowersMaureyLogProfileCalculus

/-! Calculus of the source's lower barrier x/log₂(x+1), including its
actual affine tangent. These formulas support the interpolation contact
argument; no contact or gap equality is assumed. -/
noncomputable section
namespace ThesisCommon.GowersMaurey

def rawLogarithmicProfile (x : ℝ) : ℝ := x / Real.log (x + 1)

def rawLogarithmicProfileDeriv (x : ℝ) : ℝ :=
  1 / Real.log (x + 1) - x / ((x + 1) * (Real.log (x + 1))^2)

def rawLogarithmicProfileDeriv2 (x : ℝ) : ℝ :=
  (2 * x - (x + 2) * Real.log (x + 1)) /
    ((x + 1)^2 * (Real.log (x + 1))^3)

theorem hasDerivAt_rawLogarithmicProfile {x : ℝ} (hx : 0 < x) :
    HasDerivAt rawLogarithmicProfile (rawLogarithmicProfileDeriv x) x := by
  have hxp : 0 < x + 1 := by linarith
  have hlp : 0 < Real.log (x + 1) := Real.log_pos (by linarith)
  have hl := ((hasDerivAt_id x).add_const 1).log hxp.ne'
  convert (hasDerivAt_id x).div hl hlp.ne' using 1
  dsimp [rawLogarithmicProfileDeriv]
  field_simp [hxp.ne', hlp.ne']

theorem hasDerivAt_rawLogarithmicProfileDeriv {x : ℝ} (hx : 0 < x) :
    HasDerivAt rawLogarithmicProfileDeriv (rawLogarithmicProfileDeriv2 x) x := by
  have hxp : 0 < x + 1 := by linarith
  have hlp : 0 < Real.log (x + 1) := Real.log_pos (by linarith)
  have hl := ((hasDerivAt_id x).add_const 1).log hxp.ne'
  have hd := ((hasDerivAt_id x).add_const 1).mul (hl.pow 2)
  have hd0 : (x + 1) * (Real.log (x + 1))^2 ≠ 0 := by positivity
  convert ((hasDerivAt_const x (1 : ℝ)).div hl hlp.ne').sub
    ((hasDerivAt_id x).div hd hd0) using 1
  dsimp [rawLogarithmicProfileDeriv2]
  field_simp [hxp.ne', hlp.ne']
  ring

theorem rawLogarithmicProfileDeriv_nonneg {x : ℝ} (hx : 1 ≤ x) :
    0 ≤ rawLogarithmicProfileDeriv x := by
  have hxp : 0 < x + 1 := by linarith
  have hlp : 0 < Real.log (x + 1) := Real.log_pos (by linarith)
  have hh := Real.le_log_one_add_of_nonneg (show 0 ≤ x by linarith)
  rw [add_comm 1 x] at hh
  have hb := (div_le_iff₀ (show 0 < x + 2 by linarith)).mp hh
  have hn : x ≤ (x + 1) * Real.log (x + 1) := by
    nlinarith [mul_nonneg (show 0 ≤ x by linarith) hlp.le]
  unfold rawLogarithmicProfileDeriv
  apply sub_nonneg.mpr
  apply (div_le_div_iff₀ (by positivity) hlp).mpr
  nlinarith [mul_le_mul_of_nonneg_right hn hlp.le]

theorem rawLogarithmicProfileDeriv2_nonpos {x : ℝ} (hx : 1 ≤ x) :
    rawLogarithmicProfileDeriv2 x ≤ 0 := by
  have hlp : 0 < Real.log (x + 1) := Real.log_pos (by linarith)
  have hh := Real.le_log_one_add_of_nonneg (show 0 ≤ x by linarith)
  rw [add_comm 1 x] at hh
  have hb := (div_le_iff₀ (show 0 < x + 2 by linarith)).mp hh
  unfold rawLogarithmicProfileDeriv2
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)

theorem rawLogarithmicProfile_monotoneOn :
    MonotoneOn rawLogarithmicProfile (Set.Ici 1) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 1)
    (f' := rawLogarithmicProfileDeriv)
  · intro x hx
    exact (hasDerivAt_rawLogarithmicProfile (by change 1 ≤ x at hx; linarith)).continuousAt.continuousWithinAt
  · intro x hx
    exact (hasDerivAt_rawLogarithmicProfile (by have := interior_subset hx; change 1 ≤ x at this; linarith)).hasDerivWithinAt
  · intro x hx
    exact rawLogarithmicProfileDeriv_nonneg (interior_subset hx)

theorem rawLogarithmicProfile_concaveOn :
    ConcaveOn ℝ (Set.Ici 1) rawLogarithmicProfile := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Ici 1)
    (f' := rawLogarithmicProfileDeriv) (f'' := rawLogarithmicProfileDeriv2)
  · intro x hx
    exact (hasDerivAt_rawLogarithmicProfile (by change 1 ≤ x at hx; linarith)).continuousAt.continuousWithinAt
  · intro x hx
    exact (hasDerivAt_rawLogarithmicProfile (by have := interior_subset hx; change 1 ≤ x at this; linarith)).hasDerivWithinAt
  · intro x hx
    exact (hasDerivAt_rawLogarithmicProfileDeriv (by have := interior_subset hx; change 1 ≤ x at this; linarith)).hasDerivWithinAt
  · intro x hx
    exact rawLogarithmicProfileDeriv2_nonpos (interior_subset hx)

def logarithmicProfile (x : ℝ) : ℝ := x / logarithmicWeight x

def logarithmicProfileSlope (x : ℝ) : ℝ :=
  Real.log 2 / Real.log (x + 1) * (1 - x / ((x + 1) * Real.log (x + 1)))

def logarithmicProfileIntercept (x : ℝ) : ℝ :=
  x^2 * Real.log 2 / ((x + 1) * (Real.log (x + 1))^2)

def logarithmicProfileTangent (s x : ℝ) : ℝ :=
  logarithmicProfileIntercept s + logarithmicProfileSlope s * x

theorem logarithmicProfile_eq_scaled (x : ℝ) :
    logarithmicProfile x = Real.log 2 * rawLogarithmicProfile x := by
  unfold logarithmicProfile logarithmicWeight rawLogarithmicProfile
  rw [div_div_eq_mul_div]
  ring

theorem logarithmicProfile_concaveOn : ConcaveOn ℝ (Set.Ici 1) logarithmicProfile := by
  apply (ConcaveOn.smul (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))
    rawLogarithmicProfile_concaveOn).congr
  intro x _
  exact (logarithmicProfile_eq_scaled x).symm

theorem logarithmicProfile_monotoneOn : MonotoneOn logarithmicProfile (Set.Ici 1) := by
  intro x hx y hy hxy
  rw [logarithmicProfile_eq_scaled, logarithmicProfile_eq_scaled]
  exact mul_le_mul_of_nonneg_left (rawLogarithmicProfile_monotoneOn hx hy hxy)
    (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))

theorem hasDerivAt_logarithmicProfile {x : ℝ} (hx : 0 < x) :
    HasDerivAt logarithmicProfile (logarithmicProfileSlope x) x := by
  have hxp : 0 < x + 1 := by linarith
  have hlp : 0 < Real.log (x + 1) := Real.log_pos (by linarith)
  have hd := (hasDerivAt_rawLogarithmicProfile hx).const_mul (Real.log 2)
  have heq : (fun t => Real.log 2 * rawLogarithmicProfile t) = logarithmicProfile := by
    funext t
    exact (logarithmicProfile_eq_scaled t).symm
  rw [heq] at hd
  convert hd using 1
  unfold logarithmicProfileSlope rawLogarithmicProfileDeriv
  field_simp [hxp.ne', hlp.ne']

theorem logarithmicProfileTangent_eq {s x : ℝ} (hs : 0 < s) :
    logarithmicProfileTangent s x = logarithmicProfile s + logarithmicProfileSlope s * (x - s) := by
  have hsp : 0 < s + 1 := by linarith
  have hlp : 0 < Real.log (s + 1) := Real.log_pos (by linarith)
  rw [logarithmicProfile_eq_scaled]
  unfold logarithmicProfileTangent logarithmicProfileIntercept logarithmicProfileSlope rawLogarithmicProfile
  field_simp [hsp.ne', hlp.ne']
  ring

theorem logarithmicProfileTangent_contact {s : ℝ} (hs : 0 < s) :
    logarithmicProfileTangent s s = logarithmicProfile s := by
  rw [logarithmicProfileTangent_eq hs]
  simp

theorem logarithmicProfile_le_tangent {s x : ℝ} (hs : 1 ≤ s) (hx : 1 ≤ x) :
    logarithmicProfile x ≤ logarithmicProfileTangent s x := by
  rw [logarithmicProfileTangent_eq (zero_lt_one.trans_le hs)]
  have hd := hasDerivAt_logarithmicProfile (zero_lt_one.trans_le hs)
  rcases lt_trichotomy x s with hxs | rfl | hsx
  · have hh := logarithmicProfile_concaveOn.le_slope_of_hasDerivAt hx hs hxs hd
    rw [slope_def_field] at hh
    have hc := (le_div_iff₀ (sub_pos.mpr hxs)).mp hh
    nlinarith
  · simp
  · have hh := logarithmicProfile_concaveOn.slope_le_of_hasDerivAt hs hx hsx hd
    rw [slope_def_field] at hh
    have hc := (div_le_iff₀ (sub_pos.mpr hsx)).mp hh
    nlinarith

end ThesisCommon.GowersMaurey

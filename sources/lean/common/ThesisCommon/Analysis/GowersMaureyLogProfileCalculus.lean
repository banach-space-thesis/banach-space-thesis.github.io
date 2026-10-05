import ThesisCommon.Analysis.GowersMaureyLogSubmultiplicative
import ThesisCommon.Analysis.ConcavePerspectiveBound
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! The concrete upper barrier x/sqrt(log₂(x+1)) for the source numerical
profile construction. Derivatives and their signs are proved explicitly. -/
noncomputable section
namespace ThesisCommon.GowersMaurey

def rawSqrtLogProfile (x : ℝ) : ℝ := x / Real.sqrt (Real.log (x + 1))

def rawSqrtLogProfileDeriv (x : ℝ) : ℝ :=
  1 / Real.sqrt (Real.log (x + 1)) -
    x / (2 * (x + 1) * Real.log (x + 1) * Real.sqrt (Real.log (x + 1)))

def rawSqrtLogProfileDeriv2 (x : ℝ) : ℝ :=
  (3 * x - (2 * x + 4) * Real.log (x + 1)) /
    (4 * (x + 1)^2 * (Real.log (x + 1))^2 * Real.sqrt (Real.log (x + 1)))

theorem hasDerivAt_rawSqrtLogProfile {x : ℝ} (hx : 0 < x) :
    HasDerivAt rawSqrtLogProfile (rawSqrtLogProfileDeriv x) x := by
  have hxp : 0 < x + 1 := by linarith
  have hlp : 0 < Real.log (x + 1) := Real.log_pos (by linarith)
  have hsp : 0 < Real.sqrt (Real.log (x + 1)) := Real.sqrt_pos.mpr hlp
  have hl := ((hasDerivAt_id x).add_const 1).log hxp.ne'
  have hs := hl.sqrt hlp.ne'
  convert (hasDerivAt_id x).div hs hsp.ne' using 1
  dsimp [rawSqrtLogProfileDeriv]
  field_simp [hxp.ne', hlp.ne', hsp.ne']
  simp only [Real.sq_sqrt hlp.le]
  ring

theorem hasDerivAt_rawSqrtLogProfileDeriv {x : ℝ} (hx : 0 < x) :
    HasDerivAt rawSqrtLogProfileDeriv (rawSqrtLogProfileDeriv2 x) x := by
  have hxp : 0 < x + 1 := by linarith
  have hlp : 0 < Real.log (x + 1) := Real.log_pos (by linarith)
  have hsp : 0 < Real.sqrt (Real.log (x + 1)) := Real.sqrt_pos.mpr hlp
  have hl := ((hasDerivAt_id x).add_const 1).log hxp.ne'
  have hs := hl.sqrt hlp.ne'
  have hd := (((hasDerivAt_id x).add_const 1).const_mul 2).mul hl |>.mul hs
  have hd0 : 2 * (x + 1) * Real.log (x + 1) * Real.sqrt (Real.log (x + 1)) ≠ 0 := by positivity
  convert ((hasDerivAt_const x (1 : ℝ)).div hs hsp.ne').sub
    ((hasDerivAt_id x).div hd hd0) using 1
  dsimp [rawSqrtLogProfileDeriv2]
  field_simp [hxp.ne', hlp.ne', hsp.ne']
  ring_nf
  simp only [Real.sq_sqrt (show 0 ≤ Real.log (1 + x) by simpa only [add_comm] using hlp.le)]
  ring

theorem rawSqrtLogProfileDeriv_nonneg {x : ℝ} (hx : 1 ≤ x) :
    0 ≤ rawSqrtLogProfileDeriv x := by
  have hxp : 0 < x + 1 := by linarith
  have hlp : 0 < Real.log (x + 1) := Real.log_pos (by linarith)
  have hsp : 0 < Real.sqrt (Real.log (x + 1)) := Real.sqrt_pos.mpr hlp
  have hh := Real.le_log_one_add_of_nonneg (show 0 ≤ x by linarith)
  rw [add_comm 1 x] at hh
  have hb := (div_le_iff₀ (show 0 < x + 2 by linarith)).mp hh
  have hnum : x ≤ 2 * (x + 1) * Real.log (x + 1) := by
    nlinarith [mul_nonneg (show 0 ≤ x by linarith) hlp.le]
  unfold rawSqrtLogProfileDeriv
  apply sub_nonneg.mpr
  apply (div_le_div_iff₀ (by positivity) hsp).mpr
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hnum hsp.le

theorem rawSqrtLogProfileDeriv2_nonpos {x : ℝ} (hx : 1 ≤ x) :
    rawSqrtLogProfileDeriv2 x ≤ 0 := by
  have hlp : 0 < Real.log (x + 1) := Real.log_pos (by linarith)
  have hh := Real.le_log_one_add_of_nonneg (show 0 ≤ x by linarith)
  rw [add_comm 1 x] at hh
  have hb := (div_le_iff₀ (show 0 < x + 2 by linarith)).mp hh
  unfold rawSqrtLogProfileDeriv2
  apply div_nonpos_of_nonpos_of_nonneg
  · nlinarith
  · positivity

theorem rawSqrtLogProfile_monotoneOn : MonotoneOn rawSqrtLogProfile (Set.Ici 1) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 1)
    (f' := rawSqrtLogProfileDeriv)
  · intro x hx
    exact (hasDerivAt_rawSqrtLogProfile (by change 1 ≤ x at hx; linarith)).continuousAt.continuousWithinAt
  · intro x hx
    exact (hasDerivAt_rawSqrtLogProfile (by have := interior_subset hx; change 1 ≤ x at this; linarith)).hasDerivWithinAt
  · intro x hx
    exact rawSqrtLogProfileDeriv_nonneg (interior_subset hx)

theorem rawSqrtLogProfile_concaveOn : ConcaveOn ℝ (Set.Ici 1) rawSqrtLogProfile := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Ici 1)
    (f' := rawSqrtLogProfileDeriv) (f'' := rawSqrtLogProfileDeriv2)
  · intro x hx
    exact (hasDerivAt_rawSqrtLogProfile (by change 1 ≤ x at hx; linarith)).continuousAt.continuousWithinAt
  · intro x hx
    exact (hasDerivAt_rawSqrtLogProfile (by have := interior_subset hx; change 1 ≤ x at this; linarith)).hasDerivWithinAt
  · intro x hx
    exact (hasDerivAt_rawSqrtLogProfileDeriv (by have := interior_subset hx; change 1 ≤ x at this; linarith)).hasDerivWithinAt
  · intro x hx
    exact rawSqrtLogProfileDeriv2_nonpos (interior_subset hx)

def sqrtLogarithmicProfile (x : ℝ) : ℝ := x / Real.sqrt (logarithmicWeight x)

theorem sqrtLogarithmicProfile_eq_scaled {x : ℝ} (hx : 0 < x) :
    sqrtLogarithmicProfile x = Real.sqrt (Real.log 2) * rawSqrtLogProfile x := by
  have hlp : 0 < Real.log (x + 1) := Real.log_pos (by linarith)
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold sqrtLogarithmicProfile logarithmicWeight rawSqrtLogProfile
  rw [Real.sqrt_div hlp.le]
  field_simp [(Real.sqrt_pos.mpr hlp).ne', (Real.sqrt_pos.mpr hL).ne']

theorem sqrtLogarithmicProfile_monotoneOn : MonotoneOn sqrtLogarithmicProfile (Set.Ici 1) := by
  intro x hx y hy hxy
  rw [sqrtLogarithmicProfile_eq_scaled (by change 1 ≤ x at hx; linarith),
    sqrtLogarithmicProfile_eq_scaled (by change 1 ≤ y at hy; linarith)]
  exact mul_le_mul_of_nonneg_left (rawSqrtLogProfile_monotoneOn hx hy hxy) (Real.sqrt_nonneg _)

theorem sqrtLogarithmicProfile_concaveOn : ConcaveOn ℝ (Set.Ici 1) sqrtLogarithmicProfile := by
  apply (ConcaveOn.smul (Real.sqrt_nonneg (Real.log 2)) rawSqrtLogProfile_concaveOn).congr
  intro x hx
  exact (sqrtLogarithmicProfile_eq_scaled (by change 1 ≤ x at hx; linarith)).symm

theorem sqrtLogarithmicProfile_one : sqrtLogarithmicProfile 1 = 1 := by
  have hL : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  simp only [sqrtLogarithmicProfile, logarithmicWeight, one_add_one_eq_two,
    div_self hL, Real.sqrt_one, div_one]

theorem hasDerivAt_sqrtLogarithmicProfile {x : ℝ} (hx : 0 < x) :
    HasDerivAt sqrtLogarithmicProfile
      (Real.sqrt (Real.log 2) * rawSqrtLogProfileDeriv x) x := by
  have hd := (hasDerivAt_rawSqrtLogProfile hx).const_mul (Real.sqrt (Real.log 2))
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hx] with y hy
  exact sqrtLogarithmicProfile_eq_scaled hy

theorem hasDerivAt_sqrtLogarithmicProfile_one :
    HasDerivAt sqrtLogarithmicProfile (1 - 1 / (4 * Real.log 2)) 1 := by
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hS : 0 < Real.sqrt (Real.log 2) := Real.sqrt_pos.mpr hL
  convert hasDerivAt_sqrtLogarithmicProfile (by norm_num : (0 : ℝ) < 1) using 1
  simp only [rawSqrtLogProfileDeriv, one_add_one_eq_two]
  field_simp [hL.ne', hS.ne']
  ring

theorem sqrtLogarithmicProfile_support {x : ℝ} (hx : 1 ≤ x) :
    sqrtLogarithmicProfile x ≤ 1 + (1 - 1 / (4 * Real.log 2)) * (x - 1) :=
  ThesisCommon.concave_support_of_right_derivative sqrtLogarithmicProfile_concaveOn
    sqrtLogarithmicProfile_one hasDerivAt_sqrtLogarithmicProfile_one.hasDerivWithinAt x hx

theorem sqrtLogarithmicProfile_le_self {x : ℝ} (hx : 1 ≤ x) :
    sqrtLogarithmicProfile x ≤ x := by
  have hd : 0 ≤ 1 / (4 * Real.log 2) := by positivity
  have hs := sqrtLogarithmicProfile_support hx
  nlinarith [mul_nonneg hd (sub_nonneg.mpr hx)]

end ThesisCommon.GowersMaurey

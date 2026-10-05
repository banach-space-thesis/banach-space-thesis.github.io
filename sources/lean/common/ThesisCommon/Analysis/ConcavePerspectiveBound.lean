import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Slope
import Mathlib.Tactic

/-! The concavity inequality used in the Gowers--Maurey interval-measure
argument. The supporting slope can be supplied by an actual right derivative
at one; monotonicity and a sign condition on that derivative are unnecessary. -/
noncomputable section
namespace ThesisCommon

theorem concave_perspective_le_of_support {G : ℝ → ℝ} {d : ℝ}
    (hG : ConcaveOn ℝ (Set.Ici 1) G) (hG1 : G 1 = 1)
    (hsupport : ∀ u, 1 ≤ u → G u ≤ 1 + d * (u - 1))
    {w t : ℝ} (hw : 1 ≤ w) (ht : 0 ≤ t) (ht1 : t < 1) :
    (1 - t) * G (w / (1 - t)) + t * (1 - d) ≤ G w := by
  by_cases ht0 : t = 0
  · simp [ht0]
  have htp : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
  have hden : 0 < 1 - t := sub_pos.mpr ht1
  let u := w / (1 - t)
  have hwu : w < u := by
    dsimp [u]
    apply (lt_div_iff₀ hden).mpr
    nlinarith
  have hu : 1 < u := hw.trans_lt hwu
  have hrel : (1 - t) * u = w := by
    dsimp [u]
    field_simp
  by_cases hw1 : w = 1
  · have hrel1 : (1 - t) * u = 1 := hrel.trans hw1
    have hh := mul_le_mul_of_nonneg_left (hsupport u hu.le) hden.le
    change (1 - t) * G u + t * (1 - d) ≤ G w
    rw [hw1, hG1]
    linear_combination hh + d * hrel1
  have hwp : 1 < w := lt_of_le_of_ne hw (Ne.symm hw1)
  let k := (G u - G w) / (u - w)
  have hsec : k ≤ (G w - 1) / (w - 1) := by
    simpa only [hG1] using hG.slope_anti_adjacent (by simp) hu.le hwp hwu
  have hsec' : k * (w - 1) ≤ G w - 1 := (le_div_iff₀ (sub_pos.mpr hwp)).mp hsec
  have hk : k ≤ d := hsec.trans ((div_le_iff₀ (sub_pos.mpr hwp)).mpr (by
    have hh := hsupport w hw
    linarith))
  have hintercept : 1 - d ≤ G w - w * k := by nlinarith
  have hvalue : G u = G w + k * (u - w) := by
    dsimp [k]
    rw [div_mul_cancel₀ _ (sub_ne_zero.mpr (ne_of_gt hwu))]
    ring
  have halgebra : (1 - t) * G u + t * (1 - d) - G w =
      t * (1 - d - (G w - w * k)) := by
    rw [hvalue]
    linear_combination k * hrel
  have hh := mul_nonpos_of_nonneg_of_nonpos ht (sub_nonpos.mpr hintercept)
  rw [← halgebra] at hh
  exact sub_nonpos.mp hh

theorem concave_support_of_right_derivative {G : ℝ → ℝ} {d : ℝ}
    (hG : ConcaveOn ℝ (Set.Ici 1) G) (hG1 : G 1 = 1)
    (hd : HasDerivWithinAt G d (Set.Ioi 1) 1) :
    ∀ u, 1 ≤ u → G u ≤ 1 + d * (u - 1) := by
  intro u hu
  rcases eq_or_lt_of_le hu with rfl | hlt
  · simp [hG1]
  have hh := hG.slope_le_of_hasDerivWithinAt_Ioi (by simp) hu hlt hd
  rw [slope_def_field, hG1] at hh
  have hs := (div_le_iff₀ (sub_pos.mpr hlt)).mp hh
  linarith

theorem concave_perspective_le_of_right_derivative {G : ℝ → ℝ} {d : ℝ}
    (hG : ConcaveOn ℝ (Set.Ici 1) G) (hG1 : G 1 = 1)
    (hd : HasDerivWithinAt G d (Set.Ioi 1) 1)
    {w t : ℝ} (hw : 1 ≤ w) (ht : 0 ≤ t) (ht1 : t < 1) :
    (1 - t) * G (w / (1 - t)) + t * (1 - d) ≤ G w :=
  concave_perspective_le_of_support hG hG1
    (concave_support_of_right_derivative hG hG1 hd) hw ht ht1

end ThesisCommon

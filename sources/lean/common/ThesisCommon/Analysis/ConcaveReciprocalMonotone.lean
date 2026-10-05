import Mathlib.Analysis.Convex.Slope
import Mathlib.Tactic

/-! Strict increase of x/G(x) for a positive concave function normalized
at one and strictly below the identity above one. -/
noncomputable section
namespace ThesisCommon

theorem strictMonoOn_div_concave_of_lt_identity {G : ℝ → ℝ}
    (hG : ConcaveOn ℝ (Set.Ici 1) G) (hG1 : G 1 = 1)
    (hpos : ∀ x, 1 ≤ x → 0 < G x)
    (hlt : ∀ x, 1 < x → G x < x) :
    StrictMonoOn (fun x => x / G x) (Set.Ici 1) := by
  intro x hx y hy hxy
  apply (div_lt_div_iff₀ (hpos x hx) (hpos y hy)).mpr
  rcases (show 1 ≤ x from hx).eq_or_lt with rfl | hx1
  · simpa only [one_mul, hG1, mul_one] using hlt y hxy
  · have hsec := hG.slope_anti_adjacent (by simp) hy hx1 hxy
    have hh := (div_le_div_iff₀ (sub_pos.mpr hxy) (sub_pos.mpr hx1)).mp hsec
    rw [hG1] at hh
    by_contra hbad
    have hge : y * G x ≤ x * G y := le_of_not_gt hbad
    have hleft := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ x by linarith) (sub_nonpos.mpr hh)
    have halgebra : x * ((G y - G x) * (x - 1) - (G x - 1) * (y - x)) =
        (x - 1) * (x * G y - y * G x) + (y - x) * (x - G x) := by ring
    rw [halgebra] at hleft
    have ha := mul_nonneg (sub_pos.mpr hx1).le (sub_nonneg.mpr hge)
    have hb := mul_pos (sub_pos.mpr hxy) (sub_pos.mpr (hlt x hx1))
    linarith

end ThesisCommon

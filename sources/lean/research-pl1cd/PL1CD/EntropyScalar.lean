import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section

namespace PL1CD.Entropy

theorem hellinger_le_relativeEntropy (a b : ℝ) (ha : 0 ≤ a) (hb : 0 < b) :
    (Real.sqrt a - Real.sqrt b) ^ 2 ≤ a * Real.log (a / b) - a + b := by
  by_cases hzero : a = 0
  · subst a
    simp [Real.sq_sqrt hb.le]
  · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm hzero)
    have hsa : 0 < Real.sqrt a := Real.sqrt_pos.mpr hap
    have hsb : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
    have hlog : Real.log (Real.sqrt b / Real.sqrt a) = -Real.log (a / b) / 2 := by
      rw [Real.log_div (ne_of_gt hsb) (ne_of_gt hsa),
        Real.log_sqrt hb.le, Real.log_sqrt ha,
        Real.log_div (ne_of_gt hap) (ne_of_gt hb)]
      ring
    have h := Real.log_le_sub_one_of_pos (div_pos hsb hsa)
    rw [hlog] at h
    have hscaled := mul_le_mul_of_nonneg_left h (show 0 ≤ 2 * a by positivity)
    have hright : 2 * a * (Real.sqrt b / Real.sqrt a - 1) =
        2 * Real.sqrt a * Real.sqrt b - 2 * a := by
      calc
        _ = 2 * (Real.sqrt a) ^ 2 * (Real.sqrt b / Real.sqrt a - 1) := by
          rw [Real.sq_sqrt ha]
        _ = 2 * Real.sqrt a * Real.sqrt b - 2 * (Real.sqrt a) ^ 2 := by
          field_simp
          <;> ring
        _ = _ := by rw [Real.sq_sqrt ha]
    rw [hright] at hscaled
    nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb.le]

end PL1CD.Entropy

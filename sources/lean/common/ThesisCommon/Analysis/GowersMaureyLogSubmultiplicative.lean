import ThesisCommon.Analysis.GowersMaureyLogGrowth
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! The source logarithmic weight and its square root are submultiplicative
on [1,infinity). The proof expands the real Bernoulli inequality. -/
noncomputable section
namespace ThesisCommon.GowersMaurey

theorem logarithmicWeight_tangent_coefficient {y : ℝ} (hy : 1 ≤ y) :
    y ≤ (y + 1) * logarithmicWeight y / 2 := by
  have hyp : 0 < y + 1 := by linarith
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL1 : Real.log 2 ≤ 1 := by
    simpa only [show (2 : ℝ) - 1 = 1 by norm_num] using
      Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have hh := Real.log_le_sub_one_of_pos (div_pos (by norm_num : (0 : ℝ) < 2) hyp)
  rw [Real.log_div (by norm_num : (2 : ℝ) ≠ 0) hyp.ne'] at hh
  have hclear : (Real.log 2 - Real.log (y + 1) + 1) * (y + 1) ≤ 2 :=
    (le_div_iff₀ hyp).mp (by linarith)
  have hslack := mul_nonneg (show 0 ≤ y - 1 by linarith) (show 0 ≤ 1 - Real.log 2 by linarith)
  have hb : 2 * y * Real.log 2 ≤ (y + 1) * Real.log (y + 1) := by nlinarith
  unfold logarithmicWeight
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  rw [← mul_div_assoc]
  exact (le_div_iff₀ hL).mpr (by nlinarith)

theorem logarithmicWeight_submultiplicative {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) :
    logarithmicWeight (x * y) ≤ logarithmicWeight x * logarithmicWeight y := by
  have hxp : 0 < x + 1 := by linarith
  have hyp : 0 < y + 1 := by linarith
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ha : 1 ≤ logarithmicWeight y := by
    unfold logarithmicWeight
    exact (le_div_iff₀ hL).mpr (by
      simpa using Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by linarith : 2 ≤ y + 1))
  have hpow2 : (2 : ℝ) ^ logarithmicWeight y = y + 1 := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    unfold logarithmicWeight
    rw [mul_div_cancel₀ _ hL.ne', Real.exp_log hyp]
  have hpow : (x + 1) ^ logarithmicWeight y =
      (y + 1) * (1 + (x - 1) / 2) ^ logarithmicWeight y := by
    calc
      _ = (2 * (1 + (x - 1) / 2)) ^ logarithmicWeight y := by congr 1; ring
      _ = _ := by rw [Real.mul_rpow (by norm_num) (by linarith), hpow2]
  have hbern := one_add_mul_self_le_rpow_one_add
    (show -1 ≤ (x - 1) / 2 by linarith) ha
  have hcoeff := logarithmicWeight_tangent_coefficient hy
  have hpower : 1 + x * y ≤ (x + 1) ^ logarithmicWeight y := by
    calc
      _ = (y + 1) + y * (x - 1) := by ring
      _ ≤ (y + 1) + ((y + 1) * logarithmicWeight y / 2) * (x - 1) :=
        add_le_add_left (mul_le_mul_of_nonneg_right hcoeff (by linarith)) _
      _ = (y + 1) * (1 + logarithmicWeight y * ((x - 1) / 2)) := by ring
      _ ≤ (y + 1) * (1 + (x - 1) / 2) ^ logarithmicWeight y :=
        mul_le_mul_of_nonneg_left hbern hyp.le
      _ = _ := hpow.symm
  have hlog := Real.log_le_log (by nlinarith : 0 < 1 + x * y) hpower
  rw [Real.log_rpow hxp] at hlog
  unfold logarithmicWeight at hlog ⊢
  apply (div_le_iff₀ hL).mpr
  convert hlog using 1
  · congr 1; ring
  · field_simp

theorem sqrt_logarithmicWeight_submultiplicative {x y : ℝ}
    (hx : 1 ≤ x) (hy : 1 ≤ y) :
    Real.sqrt (logarithmicWeight (x * y)) ≤
      Real.sqrt (logarithmicWeight x) * Real.sqrt (logarithmicWeight y) := by
  have hx0 : 0 ≤ logarithmicWeight x := by
    unfold logarithmicWeight
    exact div_nonneg (Real.log_nonneg (by linarith)) (Real.log_nonneg (by norm_num))
  simpa only [Real.sqrt_mul hx0] using
    Real.sqrt_le_sqrt (logarithmicWeight_submultiplicative hx hy)

end ThesisCommon.GowersMaurey

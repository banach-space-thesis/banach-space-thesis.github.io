import PL1.KFunctionalIntegralMeasurable
import PL1.KFunctionalProperties

/-! Norm laws for the actual extended continuous interpolation integral. -/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal

namespace PL1.KFunctional
open Noise Walsh

variable (K : Type*) [RCLike K] (rates : ℕ → ℝ≥0)

@[simp] theorem continuousNorm_zero : continuousNorm K rates 0 = 0 := by
  unfold continuousNorm
  calc
    _ = ∫⁻ _t in Ioi (0 : ℝ), (0 : ℝ≥0∞) := by
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only
      rw [value_zero K rates (Set.mem_Ioi.mp ht).le, mul_zero, ENNReal.ofReal_zero]
    _ = 0 := by simp

theorem continuousNorm_smul (a : K) (f : Lp K 1 haar) :
    continuousNorm K rates (a • f) = ENNReal.ofReal ‖a‖ * continuousNorm K rates f := by
  unfold continuousNorm
  calc
    _ = ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal ‖a‖ *
        ENNReal.ofReal (t ^ (-3 / 2 : ℝ) * value K rates t f) := by
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only
      rw [value_smul K rates (Set.mem_Ioi.mp ht).le]
      rw [show t ^ (-3 / 2 : ℝ) * (‖a‖ * value K rates t f) =
        ‖a‖ * (t ^ (-3 / 2 : ℝ) * value K rates t f) by ring,
        ENNReal.ofReal_mul (norm_nonneg a)]
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

theorem continuousNorm_add_le (f g : Lp K 1 haar) :
    continuousNorm K rates (f + g) ≤ continuousNorm K rates f + continuousNorm K rates g := by
  have h : (fun t : ℝ => ENNReal.ofReal (t ^ (-3 / 2 : ℝ) * value K rates t (f + g)))
      ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun t => ENNReal.ofReal (t ^ (-3 / 2 : ℝ) * value K rates t f) +
        ENNReal.ofReal (t ^ (-3 / 2 : ℝ) * value K rates t g)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 ≤ t := (Set.mem_Ioi.mp ht).le
    have hp := Real.rpow_nonneg ht0 (-3 / 2 : ℝ)
    rw [← ENNReal.ofReal_add (mul_nonneg hp (value_nonneg K rates ht0 f))
      (mul_nonneg hp (value_nonneg K rates ht0 g)), ← mul_add]
    exact ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left (value_add_le K rates ht0 f g) hp)
  have hi := lintegral_mono_ae h
  rw [lintegral_add_left' (interpolationDensity_aemeasurable K rates f)] at hi
  exact hi

theorem two_norm_le_continuousNorm (f : Lp K 1 haar) :
    ENNReal.ofReal (2 * ‖f‖) ≤ continuousNorm K rates f := by
  change ENNReal.ofReal (2 * ‖f‖) ≤
    DyadicInterpolation.fullIntegral (fun t => value K rates t f)
  rw [DyadicInterpolation.fullIntegral_eq (norm_nonneg f)
    (fun _ ht => value_eq_norm_of_one_le K rates ht f)]
  exact le_add_self

@[simp] theorem continuousNorm_eq_zero_iff (f : Lp K 1 haar) :
    continuousNorm K rates f = 0 ↔ f = 0 := by
  constructor
  · intro hf
    have h := two_norm_le_continuousNorm K rates f
    rw [hf] at h
    have hn := ENNReal.ofReal_eq_zero.mp (le_antisymm h bot_le)
    apply norm_eq_zero.mp
    linarith [norm_nonneg f]
  · rintro rfl
    exact continuousNorm_zero K rates

end PL1.KFunctional

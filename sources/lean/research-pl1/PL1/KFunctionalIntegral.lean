import PL1.DyadicInterpolationNormComparison
import PL1.ExtendedDiscreteInterpolation

/-!
# Continuous interpolation integral for the actual generator graph

This is the usual real interpolation integral at parameters theta = 1/2
and q = 1: the Lebesgue density is t^(-3/2) times the actual K-functional.
The extended value retains infinity outside the interpolation space.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal

namespace PL1.KFunctional
open Noise Walsh ResolventEstimates DyadicInterpolation

variable (K : Type*) [RCLike K] (rates : ℕ → ℝ≥0)

def continuousNorm (f : Lp K 1 haar) : ℝ≥0∞ :=
  ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (-3 / 2 : ℝ) * value K rates t f)

theorem time_eq_dyadicTime (n : ℕ) : time n = (dyadicTime n : ℝ) := by
  simp only [time, dyadicTime, dyadicRatio_sq]

theorem weight_eq_dyadicRatio (n : ℕ) : weight n = (dyadicRatio ^ n)⁻¹ := by
  rw [weight_eq_sqrt_two_pow]
  simp [dyadicRatio, inv_pow]

theorem sample_eq_term (f : Lp K 1 haar) (n : ℕ) :
    sample (fun t => value K rates t f) (n + 1) =
      ENNReal.ofReal (DiscreteInterpolation.term K rates f n) := by
  rw [sample, weight_eq_dyadicRatio, time_eq_dyadicTime]
  rfl

theorem discreteNorm_eq_extendedNorm (f : Lp K 1 haar) :
    discreteNorm (fun t => value K rates t f) = DiscreteInterpolation.extendedNorm K rates f := by
  simp only [discreteNorm, DiscreteInterpolation.extendedNorm, sample_eq_term,
    value_eq_norm_of_one_le K rates le_rfl]

theorem tail_integral_eq (f : Lp K 1 haar) :
    (∫⁻ t in Ioi (1 : ℝ), ENNReal.ofReal (t ^ (-3 / 2 : ℝ) * value K rates t f)) =
      ENNReal.ofReal (2 * ‖f‖) :=
  tailIntegral_eq (norm_nonneg f) (fun _ ht => value_eq_norm_of_one_le K rates ht f)

theorem continuousNorm_le_four_extendedNorm (f : Lp K 1 haar) :
    continuousNorm K rates f ≤ 4 * DiscreteInterpolation.extendedNorm K rates f := by
  rw [← discreteNorm_eq_extendedNorm]
  exact fullIntegral_le_four_discreteNorm
    (fun _ ht => value_nonneg K rates ht f) (monotoneOn_value K rates f)
    (fun t ht => (value_eq_norm_of_one_le K rates ht f).trans
      (value_eq_norm_of_one_le K rates le_rfl f).symm)

theorem extendedNorm_le_five_continuousNorm (f : Lp K 1 haar) :
    DiscreteInterpolation.extendedNorm K rates f ≤ 5 * continuousNorm K rates f := by
  rw [← discreteNorm_eq_extendedNorm]
  exact discreteNorm_le_five_fullIntegral
    (fun _ ht => value_nonneg K rates ht f) (monotoneOn_value K rates f)
    (fun t ht => (value_eq_norm_of_one_le K rates ht f).trans
      (value_eq_norm_of_one_le K rates le_rfl f).symm)

theorem continuousNorm_ne_top_iff (f : Lp K 1 haar) :
    continuousNorm K rates f ≠ ⊤ ↔ DiscreteInterpolation.extendedNorm K rates f ≠ ⊤ := by
  rw [← discreteNorm_eq_extendedNorm]
  exact fullIntegral_ne_top_iff_discreteNorm
    (fun _ ht => value_nonneg K rates ht f) (monotoneOn_value K rates f)
    (fun t ht => (value_eq_norm_of_one_le K rates ht f).trans
      (value_eq_norm_of_one_le K rates le_rfl f).symm)

end PL1.KFunctional

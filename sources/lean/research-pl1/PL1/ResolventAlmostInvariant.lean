import PL1.ResolventNorms

/-!
# Quantitative almost invariance of actual resolvent images

The estimate used in the paper's tail-spike construction holds for every
coordinate-rate sequence and over either scalar field.
-/

noncomputable section
open MeasureTheory
open scoped NNReal

namespace PL1.Noise
open Walsh

variable (𝕜 : Type*) [RCLike 𝕜] (rates : ℕ → ℝ≥0)

theorem norm_noise_comp_resolvent_sub_le (t : PositiveTime) (u : ℝ≥0) :
    ‖(noiseL1 𝕜 rates u).comp (resolventL1 𝕜 rates t) - resolventL1 𝕜 rates t‖ ≤
      2 * (1 - Real.exp (-(u : ℝ) / (t : ℝ))) := by
  let α : ℝ := Real.exp (-(u : ℝ) / (t : ℝ))
  let S := (noiseL1 𝕜 rates u).comp (resolventL1 𝕜 rates t)
  have hα : 0 ≤ 1 - α := sub_nonneg.mpr (Real.exp_le_one_iff.mpr
    (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr u.coe_nonneg) t.property.le))
  have hS : ‖S‖ ≤ 1 := by
    have h := ContinuousLinearMap.opNorm_comp_le (noiseL1 𝕜 rates u) (resolventL1 𝕜 rates t)
    simpa only [norm_noiseL1_eq_one, norm_resolventL1_eq_one, mul_one] using h
  have htail : ‖resolventL1 𝕜 rates t - (α : 𝕜) • S‖ = 1 - α := by
    rw [← truncatedResolventL1_eq_noise_comp_resolvent]
    exact norm_resolventL1_sub_truncated_eq 𝕜 rates t u
  have heq : S - resolventL1 𝕜 rates t =
      ((1 - α : ℝ) : 𝕜) • S - (resolventL1 𝕜 rates t - (α : 𝕜) • S) := by
    rw [RCLike.ofReal_sub, RCLike.ofReal_one, sub_smul (1 : 𝕜) (α : 𝕜) S, one_smul]
    abel
  change ‖S - resolventL1 𝕜 rates t‖ ≤ 2 * (1 - α)
  rw [heq]
  calc
    _ ≤ ‖((1 - α : ℝ) : 𝕜) • S‖ + ‖resolventL1 𝕜 rates t - (α : 𝕜) • S‖ := norm_sub_le _ _
    _ = (1 - α) * ‖S‖ + (1 - α) := by
      rw [norm_smul, RCLike.norm_ofReal, abs_of_nonneg hα, htail]
    _ ≤ 2 * (1 - α) := by nlinarith

theorem one_sub_exp_neg_div_le (t : PositiveTime) (u : ℝ≥0) :
    1 - Real.exp (-(u : ℝ) / (t : ℝ)) ≤ (u : ℝ) / (t : ℝ) := by
  have h := Real.add_one_le_exp (-(u : ℝ) / (t : ℝ))
  simp only [neg_div] at h ⊢
  linarith

theorem norm_noise_comp_resolvent_sub_le_time (t : PositiveTime) (u : ℝ≥0) :
    ‖(noiseL1 𝕜 rates u).comp (resolventL1 𝕜 rates t) - resolventL1 𝕜 rates t‖ ≤
      2 * (u : ℝ) / (t : ℝ) :=
  (norm_noise_comp_resolvent_sub_le 𝕜 rates t u).trans (by
    have h := one_sub_exp_neg_div_le t u
    convert mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 2) using 1
    ring)

theorem norm_noise_resolvent_sub_le (t : PositiveTime) (u : ℝ≥0) (f : Lp 𝕜 1 haar) :
    ‖noiseL1 𝕜 rates u (resolventL1 𝕜 rates t f) - resolventL1 𝕜 rates t f‖ ≤
      2 * (1 - Real.exp (-(u : ℝ) / (t : ℝ))) * ‖f‖ := by
  exact ((noiseL1 𝕜 rates u |>.comp (resolventL1 𝕜 rates t)) -
    resolventL1 𝕜 rates t).le_opNorm f |>.trans
      (mul_le_mul_of_nonneg_right (norm_noise_comp_resolvent_sub_le 𝕜 rates t u) (norm_nonneg f))

theorem norm_noise_resolvent_sub_le_time (t : PositiveTime) (u : ℝ≥0) (f : Lp 𝕜 1 haar) :
    ‖noiseL1 𝕜 rates u (resolventL1 𝕜 rates t f) - resolventL1 𝕜 rates t f‖ ≤
      (2 * (u : ℝ) / (t : ℝ)) * ‖f‖ := by
  exact ((noiseL1 𝕜 rates u |>.comp (resolventL1 𝕜 rates t)) -
    resolventL1 𝕜 rates t).le_opNorm f |>.trans
      (mul_le_mul_of_nonneg_right (norm_noise_comp_resolvent_sub_le_time 𝕜 rates t u) (norm_nonneg f))

end PL1.Noise

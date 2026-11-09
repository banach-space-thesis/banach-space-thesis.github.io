import PL1.EnfloMaxMass
import PL1.NoiseHypercontractivity
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! Actual dyadic image decay and the positive hypercontractive exponent. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal ENNReal
namespace PL1.EnfloBush
open DyadicTrace NoiseHypercontractivity

section AnyTarget
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem norm_image_dyadicVector_le (S : IntervalL1 ℝ →L[ℝ] Lp ℝ 1 μ)
    (m j : ℕ) (hj : j < 2 ^ m) :
    ‖S (dyadicVector (𝕜 := ℝ) m j)‖ ≤ ‖S‖ * ((2 : ℝ)^m)⁻¹ := by
  have he : ‖dyadicVector (𝕜 := ℝ) m j‖ = ((2 : ℝ)^m)⁻¹ := by
    rw [PartitionAverages.norm_vector]
    exact intervalMeasure_cell_toReal m j hj
  simpa only [he] using S.le_opNorm (dyadicVector (𝕜 := ℝ) m j)

theorem dyadic_norm_bound_tendsto (S : IntervalL1 ℝ →L[ℝ] Lp ℝ 1 μ) :
    Tendsto (fun m : ℕ => ‖S‖ * ((2 : ℝ)^m)⁻¹) atTop (𝓝 0) := by
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)).const_mul ‖S‖
  simpa only [one_div, inv_pow, mul_zero] using h

theorem dyadic_norm_bound_rpow_tendsto (S : IntervalL1 ℝ →L[ℝ] Lp ℝ 1 μ)
    {r : ℝ} (hr : 0 < r) :
    Tendsto (fun m : ℕ => (‖S‖ * ((2 : ℝ)^m)⁻¹)^r) atTop (𝓝 0) :=
  (dyadic_norm_bound_tendsto S).rpow_const_nhds_zero hr

end AnyTarget

theorem exponent_toReal_lt_two (u : ℝ≥0) (hu : 0 < u) : (exponent u).toReal < 2 := by
  rw [exponent_toReal]
  have hur : 0 < (u : ℝ) := hu
  have h := Real.exp_lt_one_iff.mpr (by nlinarith : -2 * (u : ℝ) < 0)
  linarith

theorem decay_exponent_pos (u : ℝ≥0) (hu : 0 < u) :
    0 < 2 / (exponent u).toReal - 1 := by
  have hp : 0 < (exponent u).toReal := by rw [exponent_toReal]; positivity
  apply sub_pos.mpr
  apply (lt_div_iff₀ hp).mpr
  simpa only [one_mul] using exponent_toReal_lt_two u hu

theorem hypercontractive_dyadic_decay
    (S : IntervalL1 ℝ →L[ℝ] Lp ℝ 1 Walsh.haar) (u : ℝ≥0) (hu : 0 < u) :
    Tendsto (fun m : ℕ => (‖S‖ * ((2 : ℝ)^m)⁻¹)^(2 / (exponent u).toReal - 1)) atTop (𝓝 0) :=
  dyadic_norm_bound_rpow_tendsto S (decay_exponent_pos u hu)

#print axioms hypercontractive_dyadic_decay
end PL1.EnfloBush


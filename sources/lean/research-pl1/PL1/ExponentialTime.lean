import Mathlib.Probability.Distributions.Exponential
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The exponential time distribution in the resolvent formula

`timeMeasure t` is the actual rate-`t⁻¹` exponential distribution transported to
the nonnegative reals. For positive `t` it is a probability measure, and its
Laplace transform is `(1 + t * a)⁻¹` for every `a ≥ 0`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace PL1.ExponentialTime

/-- Exponential time with mean `t`, represented on the nonnegative reals. -/
def timeMeasure (t : ℝ) : Measure ℝ≥0 := (expMeasure t⁻¹).map Real.toNNReal

theorem isProbabilityMeasure_timeMeasure {t : ℝ} (ht : 0 < t) :
    IsProbabilityMeasure (timeMeasure t) := by
  let : IsProbabilityMeasure (expMeasure t⁻¹) :=
    isProbabilityMeasure_expMeasure (inv_pos.2 ht)
  unfold timeMeasure
  infer_instance

theorem expDensity_eq (r x : ℝ) :
    exponentialPDFReal r x = if 0 ≤ x then r * Real.exp (-(r * x)) else 0 := by
  simp [exponentialPDFReal, gammaPDFReal]

/-- Integrating against the standard exponential distribution uses its genuine density. -/
theorem integral_expMeasure_eq_density {r : ℝ} (hr : 0 < r) (f : ℝ → ℝ) :
    (∫ x, f x ∂expMeasure r) = ∫ x, exponentialPDFReal r x * f x := by
  change (∫ x, f x ∂volume.withDensity (fun x => ENNReal.ofReal (exponentialPDFReal r x))) = _
  rw [integral_withDensity_eq_integral_toReal_smul
    ((measurable_exponentialPDFReal r).ennreal_ofReal)
    (ae_of_all _ (fun x => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (exponentialPDFReal_nonneg hr _), smul_eq_mul]

theorem exp_neg_mul_norm_le_one (a : ℝ) (ha : 0 ≤ a) (u : ℝ≥0) :
    ‖Real.exp (-(u : ℝ) * a)‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_one_iff.2
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 u.coe_nonneg) ha

theorem integrable_laplace {t : ℝ} (ht : 0 < t) (a : ℝ) (ha : 0 ≤ a) :
    Integrable (fun u : ℝ≥0 => Real.exp (-(u : ℝ) * a)) (timeMeasure t) := by
  let := isProbabilityMeasure_timeMeasure ht
  apply Integrable.of_bound (by fun_prop) 1
  exact ae_of_all _ (exp_neg_mul_norm_le_one a ha)

/-- The Laplace transform of the actual exponential time law. -/
theorem integral_laplace {t : ℝ} (ht : 0 < t) (a : ℝ) (ha : 0 ≤ a) :
    (∫ u : ℝ≥0, Real.exp (-(u : ℝ) * a) ∂timeMeasure t) = (1 + t * a)⁻¹ := by
  rw [timeMeasure, integral_map_of_stronglyMeasurable measurable_real_toNNReal (by fun_prop),
    integral_expMeasure_eq_density (inv_pos.2 ht)]
  have hfun : (fun x : ℝ => exponentialPDFReal t⁻¹ x * Real.exp (-(Real.toNNReal x : ℝ) * a)) =
      (Ici (0 : ℝ)).indicator (fun x => t⁻¹ * Real.exp (-(t⁻¹ + a) * x)) := by
    funext x
    rw [expDensity_eq]
    by_cases hx : 0 ≤ x
    · simp only [Set.indicator, mem_Ici, ite_eq_left hx, Real.coe_toNNReal x hx]
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    · simp only [Set.indicator, mem_Ici, ite_eq_right hx, zero_mul]
  rw [hfun, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi, integral_const_mul,
    integral_exp_mul_Ioi (by linarith [inv_pos.2 ht] : -(t⁻¹ + a) < 0) 0]
  simp only [mul_zero, Real.exp_zero, neg_div]
  have hden : 1 + t * a ≠ 0 := ne_of_gt (by positivity)
  have hden' : t⁻¹ + a ≠ 0 := ne_of_gt (by positivity)
  field_simp [ne_of_gt ht, hden, hden']

theorem integral_laplace_ofReal {𝕜 : Type*} [RCLike 𝕜] {t : ℝ}
    (ht : 0 < t) (a : ℝ) (ha : 0 ≤ a) :
    (∫ u : ℝ≥0, (Real.exp (-(u : ℝ) * a) : 𝕜) ∂timeMeasure t) =
      ((1 + t * a)⁻¹ : ℝ) := by
  rw [integral_ofReal, integral_laplace ht a ha]

end PL1.ExponentialTime

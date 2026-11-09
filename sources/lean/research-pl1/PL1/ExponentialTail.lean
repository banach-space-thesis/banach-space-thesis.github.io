import PL1.ExponentialTime

/-! # Exact tails of the exponential Laplace transform -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace PL1.ExponentialTime

theorem integral_laplace_Ici {t : ℝ} (ht : 0 < t) (a : ℝ) (ha : 0 ≤ a)
    (ε : ℝ≥0) :
    (∫ u : ℝ≥0 in Ici ε, Real.exp (-(u : ℝ) * a) ∂timeMeasure t) =
      Real.exp (-(ε : ℝ) * (t⁻¹ + a)) * (1 + t * a)⁻¹ := by
  rw [← integral_indicator measurableSet_Ici, timeMeasure,
    integral_map_of_stronglyMeasurable measurable_real_toNNReal
      ((show StronglyMeasurable (fun u : ℝ≥0 => Real.exp (-(u : ℝ) * a)) from
        (by fun_prop)).indicator measurableSet_Ici),
    integral_expMeasure_eq_density (inv_pos.2 ht)]
  have hfun : (fun x : ℝ => exponentialPDFReal t⁻¹ x *
      ((Ici ε).indicator (fun u : ℝ≥0 => Real.exp (-(u : ℝ) * a))) (Real.toNNReal x)) =
      (Ici (ε : ℝ)).indicator (fun x => t⁻¹ * Real.exp (-(t⁻¹ + a) * x)) := by
    funext x
    rw [expDensity_eq]
    by_cases hx : 0 ≤ x
    · have he : ε ≤ Real.toNNReal x ↔ (ε : ℝ) ≤ x := by
        rw [← NNReal.coe_le_coe, Real.coe_toNNReal x hx]
      by_cases hε : (ε : ℝ) ≤ x
      · simp only [Set.indicator, mem_Ici, ite_eq_left hx, ite_eq_left (he.mpr hε),
          ite_eq_left hε, Real.coe_toNNReal x hx]
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring
      · simp only [Set.indicator, mem_Ici, ite_eq_left hx,
          ite_eq_right (show ¬ ε ≤ Real.toNNReal x from fun h => hε (he.mp h)),
          ite_eq_right hε, mul_zero]
    · rw [ite_eq_right hx, zero_mul, Set.indicator_of_notMem]
      exact fun h => hx (ε.coe_nonneg.trans h)
  rw [hfun, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi,
    integral_const_mul,
    integral_exp_mul_Ioi (by linarith [inv_pos.2 ht] : -(t⁻¹ + a) < 0) (ε : ℝ)]
  have hden : 1 + t * a ≠ 0 := ne_of_gt (by positivity)
  have hden' : t⁻¹ + a ≠ 0 := ne_of_gt (by positivity)
  rw [show -(t⁻¹ + a) * (ε : ℝ) = -(ε : ℝ) * (t⁻¹ + a) by ring]
  field_simp [ne_of_gt ht, hden, hden']

theorem integral_laplace_Ici_ofReal {𝕜 : Type*} [RCLike 𝕜] {t : ℝ}
    (ht : 0 < t) (a : ℝ) (ha : 0 ≤ a) (ε : ℝ≥0) :
    (∫ u : ℝ≥0 in Ici ε, (Real.exp (-(u : ℝ) * a) : 𝕜) ∂timeMeasure t) =
      ((Real.exp (-(ε : ℝ) * (t⁻¹ + a)) * (1 + t * a)⁻¹ : ℝ) : 𝕜) := by
  rw [integral_ofReal, integral_laplace_Ici ht a ha]

end PL1.ExponentialTime

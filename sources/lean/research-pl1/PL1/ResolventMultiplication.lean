import PL1.BochnerResolvents
import PL1.L1Multiplication

/-! # Integrating actual semigroup commutator bounds -/

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal

namespace PL1.Noise
open Walsh ExponentialTime

variable (K : Type*) [RCLike K] (rates : ℕ → ℝ≥0)

theorem resolvent_commutator_eq_integral (t : PositiveTime)
    (M : Lp K 1 haar →L[K] Lp K 1 haar) (f : Lp K 1 haar) :
    resolventL1 K rates t (M f) - M (resolventL1 K rates t f) =
      ∫ u, noiseL1 K rates u (M f) - M (noiseL1 K rates u f) ∂timeMeasure t := by
  let := isProbabilityMeasure_timeMeasure t.property
  rw [integral_sub (integrable_noiseL1 K rates _ (M f))
    (M.integrable_comp (integrable_noiseL1 K rates _ f)), M.integral_comp_comm
      (integrable_noiseL1 K rates _ f), ← resolventL1_eq_integral, ← resolventL1_eq_integral]

theorem norm_resolvent_commutator_le (t T : PositiveTime)
    (M : Lp K 1 haar →L[K] Lp K 1 haar) (f : Lp K 1 haar)
    (hstep : ∀ u : ℝ≥0,
      ‖noiseL1 K rates u (M f) - M (noiseL1 K rates u f)‖ ≤
        2 * (1 - Real.exp (-(u : ℝ) / (T : ℝ))) * ‖f‖) :
    ‖resolventL1 K rates t (M f) - M (resolventL1 K rates t f)‖ ≤
      2 * (1 - (1 + (t : ℝ) * (T : ℝ)⁻¹)⁻¹) * ‖f‖ := by
  let := isProbabilityMeasure_timeMeasure t.property
  have hf := (integrable_noiseL1 K rates (timeMeasure t) (M f)).sub
    (M.integrable_comp (integrable_noiseL1 K rates (timeMeasure t) f))
  have hExp := integrable_laplace t.property (T : ℝ)⁻¹ (inv_nonneg.mpr T.property.le)
  have hb : Integrable (fun u : ℝ≥0 => 2 * (1 - Real.exp (-(u : ℝ) / (T : ℝ))) * ‖f‖)
      (timeMeasure t) := by
    simpa only [div_eq_mul_inv, Pi.sub_apply] using
      ((integrable_const (1 : ℝ)).sub hExp).const_mul 2 |>.mul_const ‖f‖
  rw [resolvent_commutator_eq_integral]
  apply (norm_integral_le_integral_norm _).trans
  apply (integral_mono hf.norm hb hstep).trans_eq
  rw [integral_mul_const, integral_const_mul]
  simp only [div_eq_mul_inv]
  rw [integral_sub (integrable_const 1) hExp, integral_laplace t.property _ (inv_nonneg.mpr T.property.le)]
  simp

theorem norm_resolvent_commutator_le_time (t T : PositiveTime)
    (M : Lp K 1 haar →L[K] Lp K 1 haar) (f : Lp K 1 haar)
    (hstep : ∀ u : ℝ≥0,
      ‖noiseL1 K rates u (M f) - M (noiseL1 K rates u f)‖ ≤
        2 * (1 - Real.exp (-(u : ℝ) / (T : ℝ))) * ‖f‖) :
    ‖resolventL1 K rates t (M f) - M (resolventL1 K rates t f)‖ ≤
      (2 * (t : ℝ) / (T : ℝ)) * ‖f‖ := by
  apply (norm_resolvent_commutator_le K rates t T M f hstep).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg f)
  have hx : 0 ≤ (t : ℝ) * (T : ℝ)⁻¹ := mul_nonneg t.property.le (inv_nonneg.mpr T.property.le)
  have hden : 0 < 1 + (t : ℝ) * (T : ℝ)⁻¹ := by positivity
  have h : 1 - (1 + (t : ℝ) * (T : ℝ)⁻¹)⁻¹ ≤ (t : ℝ) * (T : ℝ)⁻¹ := by
    apply (le_of_mul_le_mul_right ?_ hden)
    nlinarith [mul_inv_cancel₀ hden.ne', sq_nonneg ((t : ℝ) * (T : ℝ)⁻¹)]
  simp only [div_eq_mul_inv]
  nlinarith

theorem norm_id_sub_resolvent_commutator_le_time (t T : PositiveTime)
    (M : Lp K 1 haar →L[K] Lp K 1 haar) (f : Lp K 1 haar)
    (hstep : ∀ u : ℝ≥0,
      ‖noiseL1 K rates u (M f) - M (noiseL1 K rates u f)‖ ≤
        2 * (1 - Real.exp (-(u : ℝ) / (T : ℝ))) * ‖f‖) :
    ‖(M f - resolventL1 K rates t (M f)) - M (f - resolventL1 K rates t f)‖ ≤
      (2 * (t : ℝ) / (T : ℝ)) * ‖f‖ := by
  rw [map_sub]
  have heq : M f - resolventL1 K rates t (M f) - (M f - M (resolventL1 K rates t f)) =
      -(resolventL1 K rates t (M f) - M (resolventL1 K rates t f)) := by abel
  rw [heq, norm_neg]
  exact norm_resolvent_commutator_le_time K rates t T M f hstep

end PL1.Noise

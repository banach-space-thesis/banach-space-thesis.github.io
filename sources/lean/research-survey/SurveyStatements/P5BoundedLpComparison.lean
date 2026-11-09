import SurveyStatements.P5RademacherPointwise
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-! A direct moment comparison for bounded real functions. This supplies
finite-exponent Rademacher tests without using a Khintchine theorem. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal RealInnerProductSpace

namespace SurveyStatements.P5

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem norm_le_l2_of_ae_eq (hp : p ≤ 2)
    (f : Lp ℝ p unitIntervalMeasure) (g : Lp ℝ 2 unitIntervalMeasure)
    (hfg : f =ᵐ[unitIntervalMeasure] g) : ‖f‖ ≤ ‖g‖ := by
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae hfg]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top g)
    (eLpNorm_le_eLpNorm_of_exponent_le hp (Lp.aestronglyMeasurable g))

theorem norm_le_l2_moment_of_bound (hp : 2 ≤ p) (hp_finite : p ≠ ∞)
    (f : Lp ℝ p unitIntervalMeasure) (g : Lp ℝ 2 unitIntervalMeasure)
    (hfg : f =ᵐ[unitIntervalMeasure] g)
    (hbound : ∀ᵐ x ∂unitIntervalMeasure, ‖g x‖ ≤ 1) :
    ‖f‖ ≤ (‖g‖ ^ 2) ^ p.toReal⁻¹ := by
  have hp0 : p ≠ 0 := (zero_lt_two.trans_le hp).ne'
  have hpr : (2 : ℝ) ≤ p.toReal := by
    simpa using ENNReal.toReal_mono hp_finite hp
  have hmoment : (∫⁻ x, ‖g x‖ₑ ^ p.toReal ∂unitIntervalMeasure) ≤
      ∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) ∂unitIntervalMeasure := by
    apply lintegral_mono_ae
    filter_upwards [hbound] with x hx
    apply ENNReal.rpow_le_rpow_of_exponent_ge _ hpr
    simpa only [← ofReal_norm_eq_enorm, ENNReal.ofReal_one] using
      ENNReal.ofReal_le_ofReal hx
  have hfinite : (∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) ∂unitIntervalMeasure) ≠ ∞ := by
    have h := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ∞) (Lp.eLpNorm_lt_top g)
    simpa using h.ne
  have hnorm : (∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) ∂unitIntervalMeasure).toReal = ‖g‖ ^ 2 := by
    calc
      _ = ∫ x, ⟪g x, g x⟫ ∂unitIntervalMeasure := by
        simpa only [enorm_eq_nnnorm] using (L2.integral_inner_eq_sq_eLpNorm g).symm
      _ = ⟪g, g⟫ := (L2.inner_def g g).symm
      _ = ‖g‖ ^ 2 := real_inner_self_eq_norm_sq g
  rw [Lp.norm_def, eLpNorm_congr_ae hfg,
    eLpNorm_eq_lintegral_rpow_enorm hp0 hp_finite]
  calc
    _ ≤ ((∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) ∂unitIntervalMeasure) ^
        p.toReal⁻¹).toReal := by
      apply ENNReal.toReal_mono
      · exact (ENNReal.rpow_lt_top_of_nonneg
          (inv_nonneg.mpr ENNReal.toReal_nonneg) hfinite).ne
      · simpa only [one_div] using ENNReal.rpow_le_rpow hmoment
          (inv_nonneg.mpr (ENNReal.toReal_nonneg : 0 ≤ p.toReal))
    _ = (‖g‖ ^ 2) ^ p.toReal⁻¹ := by
      rw [← ENNReal.toReal_rpow, hnorm]

end SurveyStatements.P5

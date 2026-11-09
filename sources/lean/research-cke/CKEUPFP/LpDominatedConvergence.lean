import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-! A finite-exponent dominated-convergence lemma for actual Lp elements. -/

noncomputable section

open Filter MeasureTheory
open scoped ENNReal Topology

namespace CKEUPFP

variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
  {μ : Measure α} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Pointwise almost-everywhere convergence under an Lp envelope implies
convergence of the Lp norms to zero, for every finite Banach exponent. -/
theorem lp_norm_tendsto_zero_of_dominated (f : ℕ → Lp E p μ) (hp : p ≠ ∞)
    {g : α → ℝ} (hg : MemLp g p μ)
    (hbound : ∀ n, ∀ᵐ x ∂μ, ‖f n x‖ ≤ g x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 0)) :
    Tendsto (fun n => ‖f n‖) atTop (𝓝 0) := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one Fact.out)
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hpower : Tendsto (fun n => ∫⁻ x, ‖f n x‖ₑ ^ p.toReal ∂μ) atTop (𝓝 0) := by
    have h := tendsto_lintegral_of_dominated_convergence'
      (fun x => ‖g x‖ₑ ^ p.toReal)
      (fun n => ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
        (Lp.aestronglyMeasurable (f n)).enorm)
      (fun n => ?_) (ne_of_lt (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp0 hp hg.2))
      (show ∀ᵐ x ∂μ, Tendsto (fun n => ‖f n x‖ₑ ^ p.toReal) atTop (𝓝 (0 : ℝ≥0∞)) from ?_)
    · simpa using h
    · filter_upwards [hbound n] with x hx
      apply ENNReal.rpow_le_rpow _ hpr.le
      simpa only [← ofReal_norm, Real.norm_eq_abs] using
        ENNReal.ofReal_le_ofReal (hx.trans (le_abs_self _))
    · filter_upwards [hlim] with x hx
      have he : Tendsto (fun n => ‖f n x‖ₑ) atTop (𝓝 (0 : ℝ≥0∞)) := by
        simpa only [enorm_zero, Function.comp_def] using
          (continuous_enorm.tendsto (0 : E)).comp hx
      have hr := (ENNReal.continuous_rpow_const (y := p.toReal)).tendsto (0 : ℝ≥0∞)
      simpa only [enorm_zero, ENNReal.zero_rpow_of_pos hpr] using hr.comp he
  have help : Tendsto (fun n => eLpNorm (f n) p μ) atTop (𝓝 0) := by
    have hr := (ENNReal.continuous_rpow_const (y := 1 / p.toReal)).tendsto (0 : ℝ≥0∞)
    simpa only [eLpNorm_eq_lintegral_rpow_enorm hp0 hp,
      ENNReal.zero_rpow_of_pos (one_div_pos.mpr hpr)] using hr.comp hpower
  simpa only [Lp.norm_def, ENNReal.toReal_zero] using
    (ENNReal.continuousAt_toReal ENNReal.zero_ne_top).tendsto.comp help

end CKEUPFP

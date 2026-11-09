import SurveyStatements.P5RademacherAverages

/-! The quantitative finite-exponent bounds imply genuine norm convergence
of the actual Rademacher averages. All test vectors have mean zero. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter
open scoped ENNReal BigOperators

namespace SurveyStatements.P5
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem rademacherSumLp_mean_zero (N : ℕ) :
    probabilityLpMean (𝕜 := ℝ) (rademacherSumLp p N) = 0 := by
  simp only [rademacherSumLp, dyadicRademacherLp, map_sum]
  simp only [dyadicHaar_mean_zero, Finset.sum_const_zero]

theorem rademacherAverageLp_mean_zero (N : ℕ) :
    probabilityLpMean (𝕜 := ℝ) (rademacherAverageLp p N) = 0 := by
  rw [rademacherAverageLp, map_smul, rademacherSumLp_mean_zero, smul_zero]

theorem tendsto_norm_rademacherAverageLp (hp_finite : p ≠ ∞) :
    Tendsto (fun N => ‖rademacherAverageLp p N‖) atTop (nhds 0) := by
  have hpR : 0 < p.toReal := ENNReal.toReal_pos
    (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' hp_finite
  have hmin : 0 < min (1 / 2 : ℝ) p.toReal⁻¹ := lt_min (by norm_num) (inv_pos.mpr hpR)
  have hN : Tendsto (fun N : ℕ => ((N + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hsmall := (tendsto_rpow_neg_atTop hmin).comp hN
  exact squeeze_zero (fun N => norm_nonneg _) (norm_rademacherAverageLp_le hp_finite) hsmall

theorem tendsto_rademacherAverageLp (hp_finite : p ≠ ∞) :
    Tendsto (rademacherAverageLp p) atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  exact tendsto_norm_rademacherAverageLp hp_finite

end SurveyStatements.P5

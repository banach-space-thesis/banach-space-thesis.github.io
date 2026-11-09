import SurveyStatements.P5BoundedLpComparison
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Finite dyadic Rademacher averages have norm tending to zero at every
finite Lp exponent. The proof combines the exact L2 second moment with
the pointwise bound, rather than assuming a probabilistic inequality. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal BigOperators

namespace SurveyStatements.P5

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def rademacherSumLp (p : ℝ≥0∞) [Fact (1 ≤ p)] (N : ℕ) :
    Lp ℝ p unitIntervalMeasure :=
  ∑ n ∈ Finset.range N, dyadicRademacherLp ℝ p n

def rademacherAverageLp (p : ℝ≥0∞) [Fact (1 ≤ p)] (N : ℕ) :
    Lp ℝ p unitIntervalMeasure :=
  ((N + 1 : ℕ) : ℝ)⁻¹ • rademacherSumLp p (N + 1)

theorem rademacherSumLp_ae (N : ℕ) :
    rademacherSumLp p N =ᵐ[unitIntervalMeasure]
      fun x => ∑ n ∈ Finset.range N, dyadicRademacherFunction ℝ n x := by
  filter_upwards [scalarLp_sum_ae (Finset.range N)
    (fun n => dyadicRademacherLp ℝ p n),
    ae_all_iff.mpr (dyadicRademacherLp_ae (𝕜 := ℝ) (p := p))] with x hx hh
  exact hx.trans (Finset.sum_congr rfl (fun n _ => hh n))

theorem rademacherAverageLp_ae_l2 (N : ℕ) :
    rademacherAverageLp p N =ᵐ[unitIntervalMeasure]
      rademacherAverageLp 2 N := by
  have hs : rademacherSumLp p (N + 1) =ᵐ[unitIntervalMeasure]
      rademacherSumLp 2 (N + 1) :=
    (rademacherSumLp_ae (p := p) _).trans (rademacherSumLp_ae (p := 2) _).symm
  exact (Lp.coeFn_smul _ _).trans
    (hs.const_smul _ |>.trans (Lp.coeFn_smul _ _).symm)

theorem rademacherSumLp_bound (N : ℕ) :
    ∀ᵐ x ∂unitIntervalMeasure, ‖rademacherSumLp p N x‖ ≤ (N : ℝ) := by
  filter_upwards [rademacherSumLp_ae (p := p) N] with x hx
  rw [hx]
  calc
    _ ≤ ∑ n ∈ Finset.range N, ‖dyadicRademacherFunction ℝ n x‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.range N, (1 : ℝ) :=
      Finset.sum_le_sum (fun n _ => norm_dyadicRademacherFunction_le n x)
    _ = (N : ℝ) := by simp

theorem rademacherAverageLp_bound (N : ℕ) :
    ∀ᵐ x ∂unitIntervalMeasure, ‖rademacherAverageLp p N x‖ ≤ 1 := by
  have hN : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
  filter_upwards [Lp.coeFn_smul (((N + 1 : ℕ) : ℝ)⁻¹)
    (rademacherSumLp p (N + 1)), rademacherSumLp_bound (p := p) (N + 1)] with x hx hb
  change ‖(rademacherAverageLp p N) x‖ ≤ 1
  rw [rademacherAverageLp, hx, Pi.smul_apply, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr hN.le)]
  calc
    _ ≤ ((N + 1 : ℕ) : ℝ)⁻¹ * ((N + 1 : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hN.le)
    _ = 1 := inv_mul_cancel₀ hN.ne'

theorem norm_rademacherAverageL2_sq (N : ℕ) :
    ‖rademacherAverageLp 2 N‖ ^ 2 = ((N + 1 : ℕ) : ℝ)⁻¹ := by
  have hN : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
  have hs : ‖rademacherSumLp 2 (N + 1)‖ ^ 2 = ((N + 1 : ℕ) : ℝ) :=
    norm_dyadicRademacherL2_sum_sq (N + 1)
  rw [rademacherAverageLp, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr hN.le), mul_pow, hs]
  field_simp

theorem norm_rademacherAverageLp_le (hp_finite : p ≠ ∞) (N : ℕ) :
    ‖rademacherAverageLp p N‖ ≤
      ((N + 1 : ℕ) : ℝ) ^ (-(min (1 / 2 : ℝ) p.toReal⁻¹)) := by
  have hN : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
  by_cases hp2 : p ≤ 2
  · have hr : p.toReal ≤ 2 := by simpa using ENNReal.toReal_mono (by norm_num) hp2
    have hpr : 0 < p.toReal := ENNReal.toReal_pos
      (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' hp_finite
    have hinv : (1 / 2 : ℝ) ≤ p.toReal⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le hpr hr
    rw [min_eq_left hinv]
    have hbound := norm_le_l2_of_ae_eq hp2 _ _ (rademacherAverageLp_ae_l2 (p := p) N)
    have he : ‖rademacherAverageLp 2 N‖ = ((N + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) := by
      have hs := norm_rademacherAverageL2_sq N
      have hpw : (((N + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 =
          ((N + 1 : ℕ) : ℝ)⁻¹ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]
        norm_num
        exact Real.rpow_neg_one _
      nlinarith [norm_nonneg (rademacherAverageLp 2 N), Real.rpow_pos_of_pos hN (-(1 / 2 : ℝ))]
    exact hbound.trans_eq he
  · have hp2' : 2 ≤ p := le_of_not_ge hp2
    have hr : (2 : ℝ) ≤ p.toReal := by simpa using ENNReal.toReal_mono hp_finite hp2'
    have hinv : p.toReal⁻¹ ≤ (1 / 2 : ℝ) := by
      simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hr
    rw [min_eq_right hinv]
    have hbound := norm_le_l2_moment_of_bound hp2' hp_finite
      _ _ (rademacherAverageLp_ae_l2 (p := p) N) (rademacherAverageLp_bound (p := 2) N)
    rw [norm_rademacherAverageL2_sq] at hbound
    exact hbound.trans_eq (by rw [Real.inv_rpow hN.le, Real.rpow_neg hN.le])

end SurveyStatements.P5

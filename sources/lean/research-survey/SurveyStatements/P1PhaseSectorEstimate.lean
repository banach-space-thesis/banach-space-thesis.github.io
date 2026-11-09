import SurveyStatements.P1PhaseCompactness
import Mathlib.Tactic.Ring

/-! The complex phase estimate for cross-evaluating two matched suppression
witnesses. Exact equality of their individual coefficient phases is not
needed: two fixed quarter-radius sectors give a positive half-mass bound. -/

noncomputable section
set_option autoImplicit false

namespace SurveyStatements.P1

theorem matched_phase_sector_realPart_bound
    (a b α β : ℂ) (ha : ‖a‖ = 1) (hα : ‖α‖ = 1) (hβ : ‖β‖ = 1)
    (haNear : ‖a - α‖ ≤ (1 / 4 : ℝ))
    (hbNear : ‖b - (‖b‖ : ℂ) * β‖ ≤ (1 / 4 : ℝ) * ‖b‖) :
    (1 / 2 : ℝ) * ‖b‖ ≤ (((α * β)⁻¹ * a * b).re) := by
  have hunit : ‖α * β‖ = 1 := by rw [norm_mul, hα, hβ, mul_one]
  have hnz : α * β ≠ 0 := norm_ne_zero_iff.mp (by rw [hunit]; norm_num)
  have hinv : ‖(α * β)⁻¹‖ = 1 := by rw [norm_inv, hunit, inv_one]
  have herr : ‖a * b - α * ((‖b‖ : ℂ) * β)‖ ≤ (1 / 2 : ℝ) * ‖b‖ := by
    calc
      _ = ‖a * (b - (‖b‖ : ℂ) * β) + (a - α) * ((‖b‖ : ℂ) * β)‖ := by
        congr 1
        ring
      _ ≤ ‖a * (b - (‖b‖ : ℂ) * β)‖ + ‖(a - α) * ((‖b‖ : ℂ) * β)‖ :=
        norm_add_le _ _
      _ = ‖b - (‖b‖ : ℂ) * β‖ + ‖a - α‖ * ‖b‖ := by
        rw [norm_mul, norm_mul, norm_mul, ha, hβ, one_mul, mul_one]
        simp only [Complex.norm_real, Real.norm_of_nonneg (norm_nonneg b)]
      _ ≤ (1 / 4 : ℝ) * ‖b‖ + (1 / 4 : ℝ) * ‖b‖ := by
        exact add_le_add hbNear (mul_le_mul_of_nonneg_right haNear (norm_nonneg b))
      _ = (1 / 2 : ℝ) * ‖b‖ := by ring
  have hscalar : (α * β)⁻¹ * (α * ((‖b‖ : ℂ) * β)) = (‖b‖ : ℂ) := by
    calc
      _ = (‖b‖ : ℂ) * ((α * β)⁻¹ * (α * β)) := by ring
      _ = _ := by rw [inv_mul_cancel₀ hnz, mul_one]
  have herror : ‖(α * β)⁻¹ * a * b - (‖b‖ : ℂ)‖ ≤ (1 / 2 : ℝ) * ‖b‖ := by
    calc
      _ = ‖(α * β)⁻¹ * (a * b - α * ((‖b‖ : ℂ) * β))‖ := by
        rw [mul_sub, hscalar]
        congr 1
        ring
      _ = ‖a * b - α * ((‖b‖ : ℂ) * β)‖ := by rw [norm_mul, hinv, one_mul]
      _ ≤ _ := herr
  have hre := Complex.abs_re_le_norm ((α * β)⁻¹ * a * b - (‖b‖ : ℂ))
  simp only [Complex.sub_re, Complex.ofReal_re] at hre
  have hnegative := neg_le_abs (((α * β)⁻¹ * a * b).re - ‖b‖)
  linarith

end SurveyStatements.P1

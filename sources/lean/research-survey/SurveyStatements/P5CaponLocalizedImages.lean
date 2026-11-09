import SurveyStatements.P5CaponLocalizedReaders
import SurveyStatements.P5CaponImages

/-! A fixed positive patch-area lower bound for genuine finite Capon images. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open MeasureTheory Filter
open scoped ENNReal BigOperators

namespace SurveyStatements.P5
open P5Support
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem caponLocalizedReader_image (m : ℕ) (i₀ j₀ : Fin (2 ^ m)) (N : ℕ) :
    caponLocalizedReader m j₀ p (N + 1) (caponLocalizedImage m i₀ j₀ p N) =
      ((N + 1 : ℕ) : ℝ)⁻¹ * ∑ n ∈ Finset.range (N + 1),
        intervalLpDyadicRadius m *
          unitIntervalMeasure.real ((caponLocalBranch m j₀).annulus (n + 1)) *
            ((2 : ℝ) ^ (n + 1) - 1) := by
  rw [caponLocalizedImage, map_smul, smul_eq_mul]
  congr 1
  simp_rw [map_sum, map_smul, map_sum]
  have hterm (k n : ℕ) (hn : n ∈ Finset.range (N + 1)) :
      caponLocalizedReader m j₀ p (N + 1)
        (if k ≤ n then tensorWith (dyadicHaar ℝ 1 (caponLocalInnerIndex m j₀ k))
          (caponLocalRademacher m i₀ p n) else 0) =
        if k ≤ n then intervalLpDyadicRadius m *
          unitIntervalMeasure.real ((caponLocalBranch m j₀).annulus (n + 1)) else 0 := by
    have hn' : n < N + 1 := Finset.mem_range.mp hn
    by_cases hk : k ≤ n
    · rw [if_pos hk, caponLocalizedReader_haar_level, if_pos hn',
        if_pos (by omega), mul_one, if_pos hk]
    · rw [if_neg hk, map_zero, if_neg hk]
  simp_rw [smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  calc
    _ = ∑ k ∈ Finset.range (N + 1),
        (intervalLpDyadicRadius m *
          unitIntervalMeasure.real ((caponLocalBranch m j₀).annulus (n + 1))) *
            (if k ≤ n then (2 : ℝ) ^ k else 0) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [hterm k n hn]
      split <;> simp_all only [mul_comm, zero_mul]
    _ = _ := by rw [← Finset.mul_sum, sum_two_pow_cutoff _ _ (Finset.mem_range.mp hn)]

theorem caponLocalizedReader_image_lower (m : ℕ) (i₀ j₀ : Fin (2 ^ m)) (N : ℕ) :
    intervalLpDyadicRadius m * intervalLpDyadicRadius m / 4 ≤
      caponLocalizedReader m j₀ p (N + 1) (caponLocalizedImage m i₀ j₀ p N) := by
  rw [caponLocalizedReader_image]
  have hN : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
  have hterm (n : ℕ) : intervalLpDyadicRadius m * intervalLpDyadicRadius m / 4 ≤
      intervalLpDyadicRadius m *
        unitIntervalMeasure.real ((caponLocalBranch m j₀).annulus (n + 1)) *
          ((2 : ℝ) ^ (n + 1) - 1) := by
    have h := mul_le_mul_of_nonneg_left (caponLocal_ring_contribution_le m j₀ n)
      (intervalLpDyadicRadius_pos m).le
    convert h using 1 <;> ring
  have hsum : ((N + 1 : ℕ) : ℝ) *
      (intervalLpDyadicRadius m * intervalLpDyadicRadius m / 4) ≤
        ∑ n ∈ Finset.range (N + 1), intervalLpDyadicRadius m *
          unitIntervalMeasure.real ((caponLocalBranch m j₀).annulus (n + 1)) *
            ((2 : ℝ) ^ (n + 1) - 1) := by
    simpa using Finset.sum_le_sum (s := Finset.range (N + 1)) (fun n _ => hterm n)
  have h := mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hN.le)
  simpa only [← mul_assoc, inv_mul_cancel₀ hN.ne', one_mul] using h

theorem norm_caponLocalizedImage_lower (m : ℕ) (i₀ j₀ : Fin (2 ^ m)) (N : ℕ) :
    intervalLpDyadicRadius m * intervalLpDyadicRadius m / 4 ≤
      ‖caponLocalizedImage m i₀ j₀ p N‖ := by
  calc
    _ ≤ caponLocalizedReader m j₀ p (N + 1) (caponLocalizedImage m i₀ j₀ p N) :=
      caponLocalizedReader_image_lower m i₀ j₀ N
    _ ≤ ‖caponLocalizedReader m j₀ p (N + 1) (caponLocalizedImage m i₀ j₀ p N)‖ := le_abs_self _
    _ ≤ ‖caponLocalizedReader m j₀ p (N + 1)‖ * ‖caponLocalizedImage m i₀ j₀ p N‖ :=
      (caponLocalizedReader m j₀ p (N + 1)).le_opNorm _
    _ ≤ ‖caponLocalizedImage m i₀ j₀ p N‖ := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (norm_caponLocalizedReader_le m j₀ _) (norm_nonneg _)

end SurveyStatements.P5

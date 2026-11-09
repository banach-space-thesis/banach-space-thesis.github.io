import SurveyStatements.P5L1VariationCells

/-! The finite numerical recurrence obtained by evaluating a dyadic
multiplier on the rings of a nested leaf test. -/

noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators
namespace SurveyStatements.P5L1Variation

def prefixAverage {𝕜 : Type*} [RCLike 𝕜] (d : ℕ → 𝕜) : ℕ → 𝕜
  | 0 => 0
  | j + 1 => (prefixAverage d j + d j) / 2

def defect {𝕜 : Type*} [RCLike 𝕜] (d : ℕ → 𝕜) (j : ℕ) : 𝕜 :=
  prefixAverage d j - d j

theorem prefixAverage_weighted_sum {𝕜 : Type*} [RCLike 𝕜]
    (d : ℕ → 𝕜) (r j : ℕ) :
    (2 : 𝕜) ^ (r + j) * prefixAverage d j =
      ∑ i ∈ Finset.range j, (2 : 𝕜) ^ (r + i) * d i := by
  induction j with
  | zero => simp [prefixAverage]
  | succ j ih =>
      rw [Finset.sum_range_succ, ← ih]
      change (2 : 𝕜) ^ ((r + j) + 1) * ((prefixAverage d j + d j) / 2) = _
      rw [pow_succ]
      ring

theorem defect_recurrence {𝕜 : Type*} [RCLike 𝕜] (d : ℕ → 𝕜) (j : ℕ) :
    defect d (j + 1) = defect d j / 2 + d j - d (j + 1) := by
  simp only [defect, prefixAverage]
  ring

theorem symbol_difference_of_defect {𝕜 : Type*} [RCLike 𝕜]
    (d : ℕ → 𝕜) (j : ℕ) :
    d (j + 1) - d j = defect d j / 2 - defect d (j + 1) := by
  rw [defect_recurrence]
  ring

theorem symbol_difference_norm_le {𝕜 : Type*} [RCLike 𝕜]
    (d : ℕ → 𝕜) (j : ℕ) :
    ‖d (j + 1) - d j‖ ≤ ‖defect d j‖ / 2 + ‖defect d (j + 1)‖ := by
  rw [symbol_difference_of_defect]
  have htwo : ‖(2 : 𝕜)‖ = 2 := by norm_num
  simpa only [norm_div, htwo] using norm_sub_le (defect d j / 2) (defect d (j + 1))

theorem finite_variation_le_defect_sum {𝕜 : Type*} [RCLike 𝕜]
    (d : ℕ → 𝕜) (N : ℕ) :
    (∑ j ∈ Finset.range N, ‖d (j + 1) - d j‖) ≤
      (3 / 2 : ℝ) * ∑ j ∈ Finset.range (N + 1), ‖defect d j‖ := by
  have hprev : (∑ j ∈ Finset.range N, ‖defect d j‖) ≤
      ∑ j ∈ Finset.range (N + 1), ‖defect d j‖ := by
    rw [Finset.sum_range_succ]
    exact le_add_of_nonneg_right (norm_nonneg _)
  have hnext : (∑ j ∈ Finset.range N, ‖defect d (j + 1)‖) ≤
      ∑ j ∈ Finset.range (N + 1), ‖defect d j‖ := by
    rw [Finset.sum_range_succ']
    exact le_add_of_nonneg_right (norm_nonneg _)
  calc
    _ ≤ ∑ j ∈ Finset.range N, (‖defect d j‖ / 2 + ‖defect d (j + 1)‖) :=
      Finset.sum_le_sum (fun j _ => symbol_difference_norm_le d j)
    _ = (∑ j ∈ Finset.range N, ‖defect d j‖) / 2 +
        ∑ j ∈ Finset.range N, ‖defect d (j + 1)‖ := by
      rw [Finset.sum_add_distrib, Finset.sum_div]
    _ ≤ _ := by linarith

end SurveyStatements.P5L1Variation

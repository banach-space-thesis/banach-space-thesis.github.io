import ThesisCommon.Analysis.GrothendieckMoments

/-! Quantitative truncation for a finite Rademacher linear form. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon.Grothendieck

def clip (x : ℝ) : ℝ := min 8 (max (-8) x)

theorem abs_clip_le (x : ℝ) : |clip x| ≤ 8 := by
  rw [abs_le]
  exact ⟨le_min (by norm_num) (le_max_left _ _), min_le_left _ _⟩

theorem clip_sq_le (x : ℝ) : clip x ^ 2 ≤ x ^ 2 := by
  by_cases hlo : x ≤ -8
  · have hc : clip x = -8 := by simp [clip, max_eq_left hlo]
    rw [hc]
    nlinarith
  · by_cases hhi : 8 ≤ x
    · have hc : clip x = 8 := by simp [clip, max_eq_right (by linarith : -8 ≤ x), hhi]
      rw [hc]
      nlinarith
    · have hc : clip x = x := by simp [clip, max_eq_right (by linarith : -8 ≤ x),
        min_eq_right (by linarith : x ≤ 8)]
      rw [hc]

theorem clip_error_sq_le (x : ℝ) : (x - clip x) ^ 2 ≤ x ^ 4 / 64 := by
  by_cases hlo : x ≤ -8
  · have hc : clip x = -8 := by simp [clip, max_eq_left hlo]
    rw [hc]
    have hxx : 64 ≤ x ^ 2 := by nlinarith
    have hm := mul_le_mul_of_nonneg_left hxx (sq_nonneg x)
    nlinarith [sq_nonneg (x + 8)]
  · by_cases hhi : 8 ≤ x
    · have hc : clip x = 8 := by simp [clip, max_eq_right (by linarith : -8 ≤ x), hhi]
      rw [hc]
      have hxx : 64 ≤ x ^ 2 := by nlinarith
      have hm := mul_le_mul_of_nonneg_left hxx (sq_nonneg x)
      nlinarith [sq_nonneg (x - 8)]
    · have hc : clip x = x := by simp [clip, max_eq_right (by linarith : -8 ≤ x),
        min_eq_right (by linarith : x ≤ 8)]
      rw [hc, sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
      positivity

theorem clipped_second_le {Ω : Type*} [Fintype Ω] [Nonempty Ω] (f : Ω → ℝ) :
    mean (fun ω => clip (f ω) ^ 2) ≤ mean (fun ω => f ω ^ 2) :=
  mean_mono fun ω => clip_sq_le (f ω)

theorem clip_error_second_le {Ω : Type*} [Fintype Ω] [Nonempty Ω] (f : Ω → ℝ)
    (hfour : mean (fun ω => f ω ^ 4) ≤ 3) :
    mean (fun ω => (f ω - clip (f ω)) ^ 2) ≤ (1 / 4 : ℝ) ^ 2 := by
  have h := mean_mono fun ω => clip_error_sq_le (f ω)
  have heq : (fun ω => f ω ^ 4 / 64) = (fun ω => (1 / 64 : ℝ) * f ω ^ 4) := by
    funext ω
    ring
  rw [heq, mean_mul_left] at h
  linarith

theorem clipped_rademacher_bounds {n : ℕ} (a : Fin n → ℝ)
    (ha : ∑ i, a i ^ 2 ≤ 1) :
    mean (fun ε => rademacher a ε ^ 2) ≤ 1 ∧
    mean (fun ε => clip (rademacher a ε) ^ 2) ≤ 1 ∧
    mean (fun ε => (rademacher a ε - clip (rademacher a ε)) ^ 2) ≤ (1/4 : ℝ)^2 := by
  have hsecond : mean (fun ε => rademacher a ε ^ 2) ≤ 1 := by
    rw [rademacher_second]
    exact ha
  refine ⟨hsecond, (clipped_second_le _).trans hsecond, clip_error_second_le _ ?_⟩
  have hnon : 0 ≤ ∑ i, a i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hfour := rademacher_fourth_le a
  nlinarith

end ThesisCommon.Grothendieck

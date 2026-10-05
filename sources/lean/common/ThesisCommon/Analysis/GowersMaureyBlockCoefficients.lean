import ThesisCommon.Analysis.GowersMaureyBlockSums
import ThesisCommon.Analysis.GowersMaureyIntervalMeasureScaled

/-! Coefficient estimates on genuine successive finite blocks. Interval
restriction recovers each coefficient exactly; its contractivity gives the
bound needed to transfer summable approximation errors to a block span. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem successive_support_intervals_disjoint_nat {u : ℕ → C00 𝕜}
    (hu : ∀ i j, i < j → Before (u i) (u j)) {i j : ℕ} (hij : i ≠ j) :
    Disjoint (supportInterval (u i)).set (supportInterval (u j)).set := by
  apply Finset.disjoint_left.mpr
  intro k hki hkj
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact (lt_irrefl k) (supportInterval_successive (hu i j hlt) k hki k hkj)
  · exact (lt_irrefl k) (supportInterval_successive (hu j i hgt) k hkj k hki)

theorem restrict_finite_real_block_sum {u : ℕ → C00 𝕜}
    (hu : ∀ i j, i < j → Before (u i) (u j)) (s : Finset ℕ) (c : ℕ → ℝ)
    {i : ℕ} (hi : i ∈ s) :
    restrict (supportInterval (u i)) (∑ j ∈ s, c j • u j) = c i • u i := by
  classical
  rw [map_sum]
  simp_rw [restrict_real_smul]
  rw [Finset.sum_eq_single i]
  · rw [restrict_supportInterval]
  · intro j hj hji
    rw [restrict_eq_zero_of_disjoint_supportInterval
      (successive_support_intervals_disjoint_nat hu hji.symm), smul_zero]
  · exact fun h => (h hi).elim

theorem real_block_coefficient_norm_le (D : ConstructionData 𝕜)
    {u : ℕ → C00 𝕜} (hu : ∀ i j, i < j → Before (u i) (u j))
    (s : Finset ℕ) (c : ℕ → ℝ) {i : ℕ} (hi : i ∈ s) :
    |c i| * implicitNorm D (u i) ≤ implicitNorm D (∑ j ∈ s, c j • u j) := by
  have h := implicitNorm_restrict_le D (supportInterval (u i)) (∑ j ∈ s, c j • u j)
  rw [restrict_finite_real_block_sum hu s c hi, seminorm_real_smul] at h
  exact h

theorem abs_real_block_coefficient_le_twice (D : ConstructionData 𝕜)
    {u : ℕ → C00 𝕜} (hu : ∀ i j, i < j → Before (u i) (u j))
    (s : Finset ℕ) (c : ℕ → ℝ) {i : ℕ} (hi : i ∈ s)
    (hiNorm : (1 : ℝ) / 2 ≤ implicitNorm D (u i)) :
    |c i| ≤ 2 * implicitNorm D (∑ j ∈ s, c j • u j) := by
  have h := real_block_coefficient_norm_le D hu s c hi
  have hmul := mul_le_mul_of_nonneg_left hiNorm (abs_nonneg (c i))
  linarith

end ThesisCommon.GowersMaurey

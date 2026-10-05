import ThesisCommon.Analysis.MatrixAlmostDiagonalMaps

/-! Finite past and full tail decompositions of arbitrary bounded vectors.
Only the past is written as a finite sum. -/
noncomputable section
open scoped ENNReal BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜] {p : BanachExponent}
variable {T : FiniteMatrixSum 𝕜 p →L[𝕜] FiniteMatrixSum 𝕜 p} {b : ℕ → ℝ}
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

theorem matrixSumMask_Iio_eq_sum (x : FiniteMatrixSum 𝕜 p) (k : ℕ) :
    matrixSumMask p (Set.Iio k) x = ∑ j ∈ Finset.range k, matrixSumSingle p j (x j) := by
  classical
  apply lp.ext
  funext j
  simp only [matrixSumMask_apply, Set.mem_Iio, matrixSumSingle,
    lp.singleContinuousLinearMap_apply, lp.coeFn_sum, lp.coeFn_single, Finset.sum_apply,
    Finset.sum_pi_single, Finset.mem_range]

theorem matrixSum_past_single_tail (x : FiniteMatrixSum 𝕜 p) (k : ℕ) :
    x = matrixSumMask p (Set.Iio k) x + matrixSumSingle p k (x k) +
      matrixSumMask p (Set.Ioi k) x := by
  classical
  apply lp.ext
  funext j
  change x j = ((matrixSumMask p (Set.Iio k) x) j + (matrixSumSingle p k (x k)) j) +
    (matrixSumMask p (Set.Ioi k) x) j
  rcases lt_trichotomy j k with hj | rfl | hj
  · simp [matrixSumMask_apply, Set.mem_Iio, Set.mem_Ioi, hj, not_lt.mpr hj.le,
      matrixSumSingle, hj.ne]
  · simp [matrixSumMask_apply, matrixSumSingle]
  · simp [matrixSumMask_apply, Set.mem_Iio, Set.mem_Ioi, hj, not_lt.mpr hj.le,
      matrixSumSingle, hj.ne']

theorem norm_matrixSumMask_apply_le (I : Set ℕ) (x : FiniteMatrixSum 𝕜 p) :
    ‖matrixSumMask p I x‖ ≤ ‖x‖ :=
  ((matrixSumMask (𝕜 := 𝕜) p I).le_opNorm x).trans
    (by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (norm_matrixSumMask_le (𝕜 := 𝕜) p I) (norm_nonneg x))

namespace MatrixAlmostDiagonalData
variable (d : MatrixAlmostDiagonalData p T b)

theorem insert_past_mem (x : FiniteMatrixSum 𝕜 p) (k : ℕ) :
    d.insert (matrixSumMask p (Set.Iio k) x) ∈ d.past k := by
  rw [matrixSumMask_Iio_eq_sum, map_sum]
  apply Submodule.sum_mem
  intro j hj
  rw [d.insert_single]
  exact d.past_monotone (Nat.succ_le_iff.mpr (Finset.mem_range.mp hj))
    (d.single_mem_past j (x j))

theorem insert_tail_band (x : FiniteMatrixSum 𝕜 p) (k : ℕ) :
    matrixSumMask p (d.band (k + 1)) (d.insert (matrixSumMask p (Set.Ioi k) x)) =
      d.insert (matrixSumMask p (Set.Ioi k) x) := by
  classical
  apply lp.ext
  funext j
  rw [matrixSumMask_apply]
  by_cases hj : j ∈ d.band (k + 1)
  · exact if_pos hj
  rw [if_neg hj]
  by_cases hn : j ∈ Set.range d.n
  · obtain ⟨i, rfl⟩ := hn
    rw [d.insert_apply_image, matrixSumMask_apply]
    have hi : ¬ k < i := fun h => hj (d.band_antitone (Nat.succ_le_iff.mpr h) (d.n_mem_band i))
    simp only [Set.mem_Ioi, if_neg hi, map_zero]
  · exact (d.insert_apply_of_not_mem _ _ hn).symm

theorem norm_insert_mask_le (I : Set ℕ) (x : FiniteMatrixSum 𝕜 p) :
    ‖d.insert (matrixSumMask p I x)‖ ≤ ‖x‖ :=
  (d.insert.le_opNorm _).trans ((mul_le_mul_of_nonneg_right d.norm_insert_le
    (norm_nonneg (matrixSumMask p I x))).trans
      (by simpa only [one_mul] using norm_matrixSumMask_apply_le I x))

end MatrixAlmostDiagonalData
end ThesisCommon

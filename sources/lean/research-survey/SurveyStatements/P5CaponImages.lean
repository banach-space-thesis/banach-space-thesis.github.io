import SurveyStatements.P5CaponInput
import SurveyStatements.P5CaponRingReaders

/-! Exact finite Capon calculations on the actual Bochner tensors. Capon's
symbol is one precisely when the outer Haar level is at least the inner one. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open MeasureTheory Filter
open scoped ENNReal BigOperators

namespace SurveyStatements.P5
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def IsCaponOperator (T : MixedNorm ℝ p →L[ℝ] MixedNorm ℝ p) : Prop :=
  ∀ I J, T (productHaar ℝ p I J) =
    if J.1 ≤ I.1 then productHaar ℝ p I J else 0

theorem IsCaponOperator.tensor_level
    {T : MixedNorm ℝ p →L[ℝ] MixedNorm ℝ p} (hT : IsCaponOperator T) (k n : ℕ) :
    T (tensorWith (dyadicHaar ℝ 1 (leftDyadicIndex k)) (dyadicRademacherLp ℝ p n)) =
      if k ≤ n then tensorWith (dyadicHaar ℝ 1 (leftDyadicIndex k))
        (dyadicRademacherLp ℝ p n) else 0 := by
  rw [dyadicRademacherLp, map_sum, map_sum]
  change (∑ l : Fin (2 ^ n), T (productHaar ℝ p ⟨n, l⟩ (leftDyadicIndex k))) = _
  have hhaar (I J : DyadicIndex) : T (productHaar ℝ p I J) =
      if J.1 ≤ I.1 then productHaar ℝ p I J else 0 := hT I J
  simp_rw [hhaar]
  by_cases hkn : k ≤ n
  · simp only [leftDyadicIndex, hkn, if_true, productHaar]
  · simp only [leftDyadicIndex, hkn, if_false, Finset.sum_const_zero]

theorem sum_two_pow_cutoff (N n : ℕ) (hn : n < N) :
    (∑ k ∈ Finset.range N, if k ≤ n then (2 : ℝ) ^ k else 0) =
      (2 : ℝ) ^ (n + 1) - 1 := by
  rw [← sum_two_pow_range]
  symm
  calc
    (∑ k ∈ Finset.range (n + 1), (2 : ℝ) ^ k) =
        ∑ k ∈ Finset.range (n + 1), if k ≤ n then (2 : ℝ) ^ k else 0 := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [if_pos (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk)]
    _ = ∑ k ∈ Finset.range N, if k ≤ n then (2 : ℝ) ^ k else 0 := by
      apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_of_lt hn))
      intro k _ hk
      exact if_neg (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk)

theorem IsCaponOperator.ring_reader_input
    {T : MixedNorm ℝ p →L[ℝ] MixedNorm ℝ p} (hT : IsCaponOperator T) (N : ℕ) :
    caponRingReader p (N + 1) (T (caponInput p N)) =
      ((N + 1 : ℕ) : ℝ)⁻¹ * ∑ n ∈ Finset.range (N + 1),
        unitIntervalMeasure.real (leftDyadicBranch.annulus (n + 1)) *
          ((2 : ℝ) ^ (n + 1) - 1) := by
  rw [caponInput_eq_level_sum, map_smul, map_smul, smul_eq_mul]
  congr 1
  simp_rw [map_sum, map_smul, map_sum, hT.tensor_level]
  have hterm (k n : ℕ) (hn : n ∈ Finset.range (N + 1)) :
      caponRingReader p (N + 1)
        (if k ≤ n then tensorWith (dyadicHaar ℝ 1 (leftDyadicIndex k))
          (dyadicRademacherLp ℝ p n) else 0) =
        if k ≤ n then unitIntervalMeasure.real (leftDyadicBranch.annulus (n + 1)) else 0 := by
    have hn' : n < N + 1 := Finset.mem_range.mp hn
    by_cases hk : k ≤ n
    · rw [if_pos hk, caponRingReader_haar_level, if_pos hn', if_pos (by omega), mul_one,
        if_pos hk]
    · rw [if_neg hk, map_zero, if_neg hk]
  simp_rw [smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  calc
    _ = ∑ k ∈ Finset.range (N + 1),
        unitIntervalMeasure.real (leftDyadicBranch.annulus (n + 1)) *
          (if k ≤ n then (2 : ℝ) ^ k else 0) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [hterm k n hn]
      split <;> simp_all only [mul_comm, zero_mul]
    _ = _ := by rw [← Finset.mul_sum, sum_two_pow_cutoff _ _ (Finset.mem_range.mp hn)]

theorem IsCaponOperator.ring_reader_input_lower
    {T : MixedNorm ℝ p →L[ℝ] MixedNorm ℝ p} (hT : IsCaponOperator T) (N : ℕ) :
    (1 / 4 : ℝ) ≤ caponRingReader p (N + 1) (T (caponInput p N)) := by
  rw [hT.ring_reader_input]
  have hN : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
  have hsum : ((N + 1 : ℕ) : ℝ) * (1 / 4 : ℝ) ≤
      ∑ n ∈ Finset.range (N + 1),
        unitIntervalMeasure.real (leftDyadicBranch.annulus (n + 1)) *
          ((2 : ℝ) ^ (n + 1) - 1) := by
    simpa using Finset.sum_le_sum (s := Finset.range (N + 1))
      (fun n _ => capon_ring_contribution_le n)
  have h := mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hN.le)
  simpa only [← mul_assoc, inv_mul_cancel₀ hN.ne', one_mul] using h

end SurveyStatements.P5

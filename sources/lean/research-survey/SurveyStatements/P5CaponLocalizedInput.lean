import SurveyStatements.P5CaponLocalizedAverages
import SurveyStatements.P5CaponLocalizedLeaves
import SurveyStatements.P5CaponInput

/-! Actual small tensors and their finite Capon images on square dyadic patches. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter Set
open scoped ENNReal BigOperators

namespace SurveyStatements.P5
open P5Support
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def caponLocalizedInput (m : ℕ) (i₀ j₀ : Fin (2 ^ m))
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (N : ℕ) : MixedNorm ℝ p :=
  tensorWith (caponLocalLeaf m j₀ (N + 1)) (caponLocalAverage m i₀ p N)

theorem norm_caponLocalizedInput_le (m : ℕ) (i₀ j₀ : Fin (2 ^ m)) (N : ℕ) :
    ‖caponLocalizedInput m i₀ j₀ p N‖ ≤
      (2 * intervalLpDyadicRadius m) * ‖caponLocalAverage m i₀ p N‖ := by
  rw [caponLocalizedInput, norm_tensorWith]
  exact mul_le_mul_of_nonneg_right (norm_caponLocalLeaf_le _ _ _) (norm_nonneg _)

theorem tendsto_caponLocalizedInput (hp_finite : p ≠ ∞)
    (m : ℕ) (i₀ j₀ : Fin (2 ^ m)) :
    Tendsto (caponLocalizedInput m i₀ j₀ p) atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hsmall := ((tendsto_caponLocalAverage hp_finite m i₀).norm).const_mul
    (2 * intervalLpDyadicRadius m)
  exact squeeze_zero (fun N => norm_nonneg _) (norm_caponLocalizedInput_le m i₀ j₀)
    (by simpa using hsmall)

theorem caponLocalizedInput_mem_doublyZeroMean (m : ℕ) (i₀ j₀ : Fin (2 ^ m)) (N : ℕ) :
    caponLocalizedInput m i₀ j₀ p N ∈ DoublyZeroMean ℝ p :=
  tensor_mem_doublyZeroMean _ _ (caponLocalLeaf_mean_zero _ _ _) (caponLocalAverage_mean_zero _ _ _)

theorem caponLocalizedInput_eq_level_sum (m : ℕ) (i₀ j₀ : Fin (2 ^ m)) (N : ℕ) :
    caponLocalizedInput m i₀ j₀ p N = ((N + 1 : ℕ) : ℝ)⁻¹ •
      ∑ k ∈ Finset.range (N + 1), (2 : ℝ) ^ k •
        ∑ n ∈ Finset.range (N + 1),
          tensorWith (dyadicHaar ℝ 1 (caponLocalInnerIndex m j₀ k))
            (caponLocalRademacher m i₀ p n) := by
  rw [caponLocalizedInput, caponLocalAverage, map_smul, caponLocalLeaf_eq_sum,
    tensorWith_sum_left]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [tensorWith_smul_left, map_sum]

def caponLocalizedImage (m : ℕ) (i₀ j₀ : Fin (2 ^ m))
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (N : ℕ) : MixedNorm ℝ p :=
  ((N + 1 : ℕ) : ℝ)⁻¹ •
    ∑ k ∈ Finset.range (N + 1), (2 : ℝ) ^ k •
      ∑ n ∈ Finset.range (N + 1),
        if k ≤ n then tensorWith (dyadicHaar ℝ 1 (caponLocalInnerIndex m j₀ k))
          (caponLocalRademacher m i₀ p n) else 0

theorem caponLocalizedImage_mem_doublyZeroMean (m : ℕ) (i₀ j₀ : Fin (2 ^ m)) (N : ℕ) :
    caponLocalizedImage m i₀ j₀ p N ∈ DoublyZeroMean ℝ p := by
  unfold caponLocalizedImage
  apply Submodule.smul_mem
  apply Submodule.sum_mem
  intro k _
  apply Submodule.smul_mem
  apply Submodule.sum_mem
  intro n _
  split
  · exact tensor_mem_doublyZeroMean _ _ (dyadicHaar_mean_zero _ _ _)
      (caponLocalRademacher_mean_zero _ _ _)
  · exact Submodule.zero_mem _

def IsLocalizedCaponOperator (m : ℕ) (i₀ j₀ : Fin (2 ^ m))
    (T : MixedNorm ℝ p →L[ℝ] MixedNorm ℝ p) : Prop :=
  ∀ I J : DyadicIndex, m ≤ I.1 → lpHaarCell I.1 I.2 ⊆ lpHaarCell m i₀ →
    m ≤ J.1 → lpHaarCell J.1 J.2 ⊆ lpHaarCell m j₀ →
      T (productHaar ℝ p I J) = if J.1 ≤ I.1 then productHaar ℝ p I J else 0

theorem IsLocalizedCaponOperator.tensor_level
    (m : ℕ) (i₀ j₀ : Fin (2 ^ m))
    {T : MixedNorm ℝ p →L[ℝ] MixedNorm ℝ p} (hT : IsLocalizedCaponOperator m i₀ j₀ T)
    (k n : ℕ) :
    T (tensorWith (dyadicHaar ℝ 1 (caponLocalInnerIndex m j₀ k))
      (caponLocalRademacher m i₀ p n)) =
      if k ≤ n then tensorWith (dyadicHaar ℝ 1 (caponLocalInnerIndex m j₀ k))
        (caponLocalRademacher m i₀ p n) else 0 := by
  rw [caponLocalRademacher, map_sum, map_sum]
  change (∑ l ∈ caponLocalCells m i₀ n,
    T (productHaar ℝ p ⟨m + n, l⟩ (caponLocalInnerIndex m j₀ k))) = _
  have hterm (l : Fin (2 ^ (m + n))) (hl : l ∈ caponLocalCells m i₀ n) :=
    hT ⟨m + n, l⟩ (caponLocalInnerIndex m j₀ k) (by change m ≤ m + n; omega)
      (caponLocalCells_contained m i₀ n l hl) (by change m ≤ m + k; omega)
      (caponLocalInnerIndex_contained m j₀ k)
  by_cases hkn : k ≤ n
  · rw [if_pos hkn]
    apply Finset.sum_congr rfl
    intro l hl
    exact (hterm l hl).trans (if_pos (Nat.add_le_add_left hkn m))
  · rw [if_neg hkn]
    apply Finset.sum_eq_zero
    intro l hl
    exact (hterm l hl).trans (if_neg (fun h => hkn (Nat.le_of_add_le_add_left h)))

theorem IsLocalizedCaponOperator.input_image
    (m : ℕ) (i₀ j₀ : Fin (2 ^ m))
    {T : MixedNorm ℝ p →L[ℝ] MixedNorm ℝ p} (hT : IsLocalizedCaponOperator m i₀ j₀ T)
    (N : ℕ) : T (caponLocalizedInput m i₀ j₀ p N) = caponLocalizedImage m i₀ j₀ p N := by
  rw [caponLocalizedInput_eq_level_sum, map_smul]
  simp only [map_sum, map_smul,
    IsLocalizedCaponOperator.tensor_level m i₀ j₀ hT, caponLocalizedImage]

end SurveyStatements.P5

import SurveyStatements.P5MixedDyadicMeans
import SurveyStatements.P5TensorBilinearity

/-! Exact product-Haar actions of rectangular level and tail operators. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal

namespace SurveyStatements.P5
variable {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem mixedOuterDyadicMean_productHaar (hp : p ≠ ∞) (n : ℕ)
    (I J : DyadicIndex) :
    mixedOuterDyadicMean hp n (productHaar 𝕜 p I J) =
      if I.1 < n then productHaar 𝕜 p I J else 0 := by
  rw [productHaar, mixedOuterDyadicMean_tensor, scalarDyadicMean_haar]
  split_ifs <;> simp only [map_zero]

theorem mixedInnerDyadicMean_productHaar (n : ℕ) (I J : DyadicIndex) :
    mixedInnerDyadicMean n (productHaar 𝕜 p I J) =
      if J.1 < n then productHaar 𝕜 p I J else 0 := by
  rw [productHaar, mixedInnerDyadicMean_tensor, scalarDyadicMean_haar (by norm_num)]
  split_ifs
  · rfl
  · exact map_zero (tensorInnerMap (dyadicHaar 𝕜 p I))

theorem mixedInnerDyadicLevel_productHaar (j : ℕ) (I J : DyadicIndex) :
    ((mixedInnerDyadicMean (𝕜 := 𝕜) (p := p) (j + 1) - mixedInnerDyadicMean j) :
      MixedNorm 𝕜 p →L[𝕜] MixedNorm 𝕜 p)
      (productHaar 𝕜 p I J) = if J.1 = j then productHaar 𝕜 p I J else 0 := by
  simp only [ContinuousLinearMap.sub_apply, mixedInnerDyadicMean_productHaar]
  by_cases hlow : J.1 < j
  · have hnext : J.1 < j + 1 := by omega
    have hne : J.1 ≠ j := by omega
    simp [hlow, hnext, hne]
  · by_cases heq : J.1 = j
    · simp [heq]
    · have hnext : ¬ J.1 < j + 1 := by omega
      simp [hlow, hnext, heq]

theorem mixedOuterDyadicLevel_productHaar (hp : p ≠ ∞) (i : ℕ)
    (I J : DyadicIndex) :
    ((mixedOuterDyadicMean (𝕜 := 𝕜) hp (i + 1) - mixedOuterDyadicMean hp i) :
      MixedNorm 𝕜 p →L[𝕜] MixedNorm 𝕜 p)
      (productHaar 𝕜 p I J) = if I.1 = i then productHaar 𝕜 p I J else 0 := by
  simp only [ContinuousLinearMap.sub_apply, mixedOuterDyadicMean_productHaar]
  by_cases hlow : I.1 < i
  · have hnext : I.1 < i + 1 := by omega
    have hne : I.1 ≠ i := by omega
    simp [hlow, hnext, hne]
  · by_cases heq : I.1 = i
    · simp [heq]
    · have hnext : ¬ I.1 < i + 1 := by omega
      simp [hlow, hnext, heq]

theorem mixedLowerStrip_productHaar (hp : p ≠ ∞) (n j : ℕ)
    (I J : DyadicIndex) :
    mixedLowerStrip hp n j (productHaar 𝕜 p I J) =
      if n ≤ I.1 ∧ J.1 = j then productHaar 𝕜 p I J else 0 := by
  rw [mixedLowerStrip, ContinuousLinearMap.comp_apply]
  rw [mixedInnerDyadicLevel_productHaar (𝕜 := 𝕜) (p := p)]
  by_cases hj : J.1 = j
  · rw [if_pos hj, ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
      mixedOuterDyadicMean_productHaar]
    by_cases hI : I.1 < n
    · have hn : ¬ n ≤ I.1 := by omega
      simp [hI, hn, hj]
    · have hn : n ≤ I.1 := by omega
      simp [hI, hn, hj]
  · rw [if_neg hj, map_zero, if_neg (by simp [hj])]

def mixedUpperStrip (hp : p ≠ ∞) (i n : ℕ) :
    MixedNorm 𝕜 p →L[𝕜] MixedNorm 𝕜 p :=
  (ContinuousLinearMap.id 𝕜 (MixedNorm 𝕜 p) - mixedInnerDyadicMean n).comp
    (mixedOuterDyadicMean hp (i + 1) - mixedOuterDyadicMean hp i)

theorem norm_mixedUpperStrip_le (hp : p ≠ ∞) (i n : ℕ) :
    ‖mixedUpperStrip (𝕜 := 𝕜) hp i n‖ ≤ 4 := by
  have htail : ‖ContinuousLinearMap.id 𝕜 (MixedNorm 𝕜 p) -
      mixedInnerDyadicMean n‖ ≤ 2 :=
    (norm_sub_le _ _).trans (by
      have hid : ‖ContinuousLinearMap.id 𝕜 (MixedNorm 𝕜 p)‖ ≤ 1 :=
        ContinuousLinearMap.norm_id_le
      linarith [norm_mixedInnerDyadicMean_le (𝕜 := 𝕜) (p := p) n])
  have hlevel : ‖mixedOuterDyadicMean (𝕜 := 𝕜) hp (i + 1) -
      mixedOuterDyadicMean hp i‖ ≤ 2 :=
    (norm_sub_le _ _).trans (by
      linarith [norm_mixedOuterDyadicMean_le (𝕜 := 𝕜) hp (i + 1),
        norm_mixedOuterDyadicMean_le (𝕜 := 𝕜) hp i])
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (by nlinarith [mul_le_mul htail hlevel (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)])

theorem mixedUpperStrip_productHaar (hp : p ≠ ∞) (i n : ℕ)
    (I J : DyadicIndex) :
    mixedUpperStrip hp i n (productHaar 𝕜 p I J) =
      if I.1 = i ∧ n ≤ J.1 then productHaar 𝕜 p I J else 0 := by
  rw [mixedUpperStrip, ContinuousLinearMap.comp_apply]
  rw [mixedOuterDyadicLevel_productHaar (𝕜 := 𝕜) (p := p)]
  by_cases hi : I.1 = i
  · rw [if_pos hi, ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
      mixedInnerDyadicMean_productHaar]
    by_cases hJ : J.1 < n
    · have hn : ¬ n ≤ J.1 := by omega
      simp [hJ, hn, hi]
    · have hn : n ≤ J.1 := by omega
      simp [hJ, hn, hi]
  · rw [if_neg hi, map_zero, if_neg (by simp [hi])]

end SurveyStatements.P5

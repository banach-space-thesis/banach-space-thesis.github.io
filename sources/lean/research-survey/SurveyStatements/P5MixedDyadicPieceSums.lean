import SurveyStatements.P5MixedDyadicPieces

/-! Finite sums of rectangular pieces have exactly one possible nonzero
term on a product-Haar vector. -/

noncomputable section
set_option autoImplicit false
open scoped ENNReal BigOperators

namespace SurveyStatements.P5
variable {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem sum_lowerStrips_productHaar (hp : p ≠ ∞) (r : ℕ) (n : ℕ → ℕ)
    (L : ℕ → MixedNorm 𝕜 p →L[𝕜] MixedNorm 𝕜 p) (I J : DyadicIndex) :
    (∑ j ∈ Finset.range r, (L j).comp (mixedLowerStrip (𝕜 := 𝕜) (p := p) hp (n j) j))
        (productHaar 𝕜 p I J) =
      if J.1 < r ∧ n J.1 ≤ I.1 then L J.1 (productHaar 𝕜 p I J) else 0 := by
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply,
    mixedLowerStrip_productHaar]
  have hterm (j : ℕ) :
      L j (if n j ≤ I.1 ∧ J.1 = j then productHaar 𝕜 p I J else 0) =
        if j = J.1 then
          (if n J.1 ≤ I.1 then L J.1 (productHaar 𝕜 p I J) else 0) else 0 := by
    by_cases hj : j = J.1
    · subst j
      by_cases hn : n J.1 ≤ I.1 <;> simp [hn]
    · simp [hj, Ne.symm hj]
  simp_rw [hterm]
  by_cases hJ : J.1 < r <;> by_cases hn : n J.1 ≤ I.1 <;>
    simp [Finset.sum_ite_eq', hJ, hn]

theorem sum_upperStrips_productHaar (hp : p ≠ ∞) (r : ℕ) (n : ℕ → ℕ)
    (L : ℕ → MixedNorm 𝕜 p →L[𝕜] MixedNorm 𝕜 p) (I J : DyadicIndex) :
    (∑ i ∈ Finset.range r, (L i).comp (mixedUpperStrip (𝕜 := 𝕜) (p := p) hp i (n i)))
        (productHaar 𝕜 p I J) =
      if I.1 < r ∧ n I.1 ≤ J.1 then L I.1 (productHaar 𝕜 p I J) else 0 := by
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply,
    mixedUpperStrip_productHaar]
  have hterm (i : ℕ) :
      L i (if I.1 = i ∧ n i ≤ J.1 then productHaar 𝕜 p I J else 0) =
        if i = I.1 then
          (if n I.1 ≤ J.1 then L I.1 (productHaar 𝕜 p I J) else 0) else 0 := by
    by_cases hi : i = I.1
    · subst i
      by_cases hn : n I.1 ≤ J.1 <;> simp [hn]
    · simp [hi, Ne.symm hi]
  simp_rw [hterm]
  by_cases hI : I.1 < r <;> by_cases hn : n I.1 ≤ J.1 <;>
    simp [Finset.sum_ite_eq', hI, hn]

end SurveyStatements.P5


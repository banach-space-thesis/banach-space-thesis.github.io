import SurveyStatements.P5LowerBiTreeErrorActions
import SurveyStatements.P5SeriesTelescopes

/-! Genuine bounded lower error and its exact product-Haar identity. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open Filter Topology
open scoped ENNReal BigOperators

namespace SurveyStatements.P5
open BiTree
variable {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

def lowerBiTreeError (hp : p ≠ ∞) (d : DyadicIndex → DyadicIndex → 𝕜) :
    MixedNorm 𝕜 p →L[𝕜] MixedNorm 𝕜 p :=
  (∑' k, lowerDiagonalErrorTerm (𝕜 := 𝕜) (p := p) hp d k) + (∑' k, lowerCoordinateErrorTerm (𝕜 := 𝕜) (p := p) hp d k)

theorem norm_lowerBiTreeError_le (hp : p ≠ ∞)
    (d : DyadicIndex → DyadicIndex → 𝕜) (η : ℕ → ℕ → ℝ)
    {δ : ℝ} (hs : SemiStable d η δ) (hη : ∀ i j, 0 ≤ η i j)
    (hdiag : Summable (fun k => 4 * (k + 1 : ℕ) * η k k))
    (hcoord : Summable (fun k => 4 * ∑ j ∈ Finset.range (k + 1), η k j)) :
    ‖lowerBiTreeError (𝕜 := 𝕜) (p := p) hp d‖ ≤
      (∑' k, 4 * (k + 1 : ℕ) * η k k) +
        ∑' k, 4 * ∑ j ∈ Finset.range (k + 1), η k j :=
  (norm_add_le _ _).trans (add_le_add
    (norm_operator_tsum_le (lowerDiagonalErrorTerm (𝕜 := 𝕜) (p := p) hp d) _ hdiag
      (norm_lowerDiagonalErrorTerm_le hp d η hs hη))
    (norm_operator_tsum_le (lowerCoordinateErrorTerm (𝕜 := 𝕜) (p := p) hp d) _ hcoord
      (norm_lowerCoordinateErrorTerm_le hp d η hs hη)))

theorem lowerDiagonalErrorSeries_productHaar (hp : p ≠ ∞)
    (d : DyadicIndex → DyadicIndex → 𝕜) (η : ℕ → ℕ → ℝ)
    {δ : ℝ} (hs : SemiStable d η δ) (hη : ∀ i j, 0 ≤ η i j)
    (hdiag : Summable (fun k => 4 * (k + 1 : ℕ) * η k k))
    (M : MixedNorm 𝕜 p →L[𝕜] MixedNorm 𝕜 p)
    (hM : Tendsto (diagonalGrid (p := p) d) atTop (𝓝 M)) (I J : DyadicIndex) :
    (∑' k, lowerDiagonalErrorTerm (𝕜 := 𝕜) (p := p) hp d k) (productHaar 𝕜 p I J) =
      if J.1 ≤ I.1 then
        diagonalGrid (p := p) d J.1 (productHaar 𝕜 p I J) - M (productHaar 𝕜 p I J) else 0 := by
  let H := productHaar 𝕜 p I J
  have hbound := norm_lowerDiagonalErrorTerm_le hp d η hs hη
  have hsum : Summable (lowerDiagonalErrorTerm (𝕜 := 𝕜) (p := p) hp d) :=
    summable_operators_of_norm_bound _ _ hdiag hbound
  rw [operator_tsum_apply _ _ hdiag hbound]
  by_cases hji : J.1 ≤ I.1
  · rw [if_pos hji]
    have hact : (fun k => lowerDiagonalErrorTerm (𝕜 := 𝕜) (p := p) hp d k H) =
        (fun k => if J.1 ≤ k then diagonalGrid (p := p) d k H - diagonalGrid (p := p) d (k + 1) H else 0) := by
      funext k
      simp only [H, lowerDiagonalErrorTerm_productHaar, hji, and_true]
    change (∑' k, lowerDiagonalErrorTerm (𝕜 := 𝕜) (p := p) hp d k H) = _
    rw [hact]
    apply tsum_tail_differences
    · exact ((ContinuousLinearMap.apply 𝕜 (MixedNorm 𝕜 p) H).continuous.tendsto M).comp hM
    · have heval := (ContinuousLinearMap.apply 𝕜 (MixedNorm 𝕜 p) H).summable hsum
      change Summable (fun k => lowerDiagonalErrorTerm (𝕜 := 𝕜) (p := p) hp d k H) at heval
      rw [hact] at heval
      exact heval
  · rw [if_neg hji]
    simp only [lowerDiagonalErrorTerm_productHaar, hji, and_false, if_false, tsum_zero]

theorem lowerCoordinateErrorSeries_productHaar (hp : p ≠ ∞)
    (d : DyadicIndex → DyadicIndex → 𝕜) (η : ℕ → ℕ → ℝ)
    {δ : ℝ} (hs : SemiStable d η δ) (hη : ∀ i j, 0 ≤ η i j)
    (hcoord : Summable (fun k => 4 * ∑ j ∈ Finset.range (k + 1), η k j))
    (I J : DyadicIndex) :
    (∑' k, lowerCoordinateErrorTerm (𝕜 := 𝕜) (p := p) hp d k) (productHaar 𝕜 p I J) =
      if J.1 ≤ I.1 then
        d I J • productHaar 𝕜 p I J - diagonalGrid (p := p) d J.1 (productHaar 𝕜 p I J) else 0 := by
  rw [operator_tsum_apply _ _ hcoord (norm_lowerCoordinateErrorTerm_le hp d η hs hη)]
  simp only [lowerCoordinateErrorTerm_productHaar]
  by_cases hji : J.1 ≤ I.1
  · rw [if_pos hji, tsum_window_differences
      (fun k => symbolGrid (p := p) d k J.1 (productHaar 𝕜 p I J)) J.1 I.1 hji,
      symbolGrid_productHaar] <;> rfl
  · rw [if_neg hji]
    have hzero (k : ℕ) : ¬ (J.1 ≤ k ∧ k < I.1) := by omega
    simp only [hzero, if_false, tsum_zero]

theorem lowerBiTreeError_productHaar (hp : p ≠ ∞)
    (d : DyadicIndex → DyadicIndex → 𝕜) (η : ℕ → ℕ → ℝ)
    {δ : ℝ} (hs : SemiStable d η δ) (hη : ∀ i j, 0 ≤ η i j)
    (hdiag : Summable (fun k => 4 * (k + 1 : ℕ) * η k k))
    (hcoord : Summable (fun k => 4 * ∑ j ∈ Finset.range (k + 1), η k j))
    (M : MixedNorm 𝕜 p →L[𝕜] MixedNorm 𝕜 p)
    (hM : Tendsto (diagonalGrid (p := p) d) atTop (𝓝 M)) (I J : DyadicIndex) :
    lowerBiTreeError (𝕜 := 𝕜) (p := p) hp d (productHaar 𝕜 p I J) =
      if J.1 ≤ I.1 then d I J • productHaar 𝕜 p I J - M (productHaar 𝕜 p I J) else 0 := by
  unfold lowerBiTreeError
  rw [ContinuousLinearMap.add_apply,
    lowerDiagonalErrorSeries_productHaar hp d η hs hη hdiag M hM,
    lowerCoordinateErrorSeries_productHaar hp d η hs hη hcoord]
  split_ifs <;> abel

end SurveyStatements.P5


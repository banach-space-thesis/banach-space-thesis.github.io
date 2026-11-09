import SurveyStatements.P5UpperBiTreeErrorActions
import SurveyStatements.P5SeriesTelescopes

/-! Actual bounded upper error series and their exact telescoping Haar action. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter Topology
open scoped ENNReal BigOperators

namespace SurveyStatements.P5
open P5Support BiTree
variable {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

def upperDiagonalErrorBudget (η : ℕ → ℕ → ℝ) (k : ℕ) : ℝ :=
  4 * (k + 1 : ℕ) * η k (k + 1)

def upperCoordinateErrorBudget (η : ℕ → ℕ → ℝ) (k : ℕ) : ℝ :=
  4 * ∑ i ∈ Finset.range k, η i k

def upperBiTreeError (hp : p ≠ ∞) (d : DyadicIndex → DyadicIndex → 𝕜) :
    MixedNorm 𝕜 p →L[𝕜] MixedNorm 𝕜 p :=
  (∑' k, upperDiagonalErrorTerm (𝕜 := 𝕜) (p := p) hp d k) + (∑' k, upperCoordinateErrorTerm (𝕜 := 𝕜) (p := p) hp d k)

theorem summable_upperDiagonalErrorTerm (hp : p ≠ ∞)
    (d : DyadicIndex → DyadicIndex → 𝕜) (η : ℕ → ℕ → ℝ)
    {δ : ℝ} (hs : SemiStable d η δ) (hη : ∀ i j, 0 ≤ η i j)
    (hb : Summable (upperDiagonalErrorBudget η)) :
    Summable (upperDiagonalErrorTerm (𝕜 := 𝕜) (p := p) hp d) :=
  summable_operators_of_norm_bound (upperDiagonalErrorTerm (𝕜 := 𝕜) (p := p) hp d)
    (upperDiagonalErrorBudget η) hb (norm_upperDiagonalErrorTerm_le (𝕜 := 𝕜) (p := p) hp d η hs hη)

theorem summable_upperCoordinateErrorTerm (hp : p ≠ ∞)
    (d : DyadicIndex → DyadicIndex → 𝕜) (η : ℕ → ℕ → ℝ)
    {δ : ℝ} (hs : SemiStable d η δ) (hη : ∀ i j, 0 ≤ η i j)
    (hb : Summable (upperCoordinateErrorBudget η)) :
    Summable (upperCoordinateErrorTerm (𝕜 := 𝕜) (p := p) hp d) :=
  summable_operators_of_norm_bound (upperCoordinateErrorTerm (𝕜 := 𝕜) (p := p) hp d)
    (upperCoordinateErrorBudget η) hb (norm_upperCoordinateErrorTerm_le (𝕜 := 𝕜) (p := p) hp d η hs hη)

theorem upperDiagonalErrorSeries_productHaar (hp : p ≠ ∞)
    (d : DyadicIndex → DyadicIndex → 𝕜) (η : ℕ → ℕ → ℝ)
    {δ : ℝ} (hs : SemiStable d η δ) (hη : ∀ i j, 0 ≤ η i j)
    (hb : Summable (upperDiagonalErrorBudget η))
    (M : MixedNorm 𝕜 p →L[𝕜] MixedNorm 𝕜 p)
    (hM : Tendsto (superdiagonalGrid (𝕜 := 𝕜) (p := p) d) atTop (𝓝 M))
    (I J : DyadicIndex) :
    (∑' k, upperDiagonalErrorTerm (𝕜 := 𝕜) (p := p) hp d k) (productHaar 𝕜 p I J) =
      if I.1 < J.1 then superdiagonalGrid (𝕜 := 𝕜) (p := p) d I.1 (productHaar 𝕜 p I J) -
        M (productHaar 𝕜 p I J) else 0 := by
  rw [operator_tsum_apply (upperDiagonalErrorTerm (𝕜 := 𝕜) (p := p) hp d) (upperDiagonalErrorBudget η)
    hb (norm_upperDiagonalErrorTerm_le (𝕜 := 𝕜) (p := p) hp d η hs hη)]
  by_cases hIJ : I.1 < J.1
  · rw [if_pos hIJ]
    have hseq : (fun k => upperDiagonalErrorTerm (𝕜 := 𝕜) (p := p) hp d k (productHaar 𝕜 p I J)) =
        (fun k => if I.1 ≤ k then superdiagonalGrid (𝕜 := 𝕜) (p := p) d k (productHaar 𝕜 p I J) -
          superdiagonalGrid (𝕜 := 𝕜) (p := p) d (k + 1) (productHaar 𝕜 p I J) else 0) := by
      funext k
      simp only [upperDiagonalErrorTerm_productHaar, hIJ, true_and]
    let ev : (MixedNorm 𝕜 p →L[𝕜] MixedNorm 𝕜 p) →L[𝕜] MixedNorm 𝕜 p :=
      ContinuousLinearMap.apply 𝕜 (MixedNorm 𝕜 p) (productHaar 𝕜 p I J)
    have hsapply : Summable (fun k => upperDiagonalErrorTerm (𝕜 := 𝕜) (p := p) hp d k
        (productHaar 𝕜 p I J)) :=
      ((summable_upperDiagonalErrorTerm (𝕜 := 𝕜) (p := p) hp d η hs hη hb).hasSum.map ev ev.continuous).summable
    have hlim : Tendsto (fun k => superdiagonalGrid (𝕜 := 𝕜) (p := p) d k (productHaar 𝕜 p I J))
        atTop (𝓝 (M (productHaar 𝕜 p I J))) :=
      (ev.continuous.tendsto M).comp hM
    rw [hseq]
    exact tsum_tail_differences
      (fun k => superdiagonalGrid (𝕜 := 𝕜) (p := p) d k (productHaar 𝕜 p I J))
      (M (productHaar 𝕜 p I J)) I.1 hlim (hseq ▸ hsapply)
  · rw [if_neg hIJ]
    simp only [upperDiagonalErrorTerm_productHaar, hIJ, false_and, if_false, tsum_zero]

theorem upperCoordinateErrorSeries_productHaar (hp : p ≠ ∞)
    (d : DyadicIndex → DyadicIndex → 𝕜) (η : ℕ → ℕ → ℝ)
    {δ : ℝ} (hs : SemiStable d η δ) (hη : ∀ i j, 0 ≤ η i j)
    (hb : Summable (upperCoordinateErrorBudget η)) (I J : DyadicIndex) :
    (∑' k, upperCoordinateErrorTerm (𝕜 := 𝕜) (p := p) hp d k) (productHaar 𝕜 p I J) =
      if I.1 < J.1 then d I J • productHaar 𝕜 p I J -
        superdiagonalGrid (𝕜 := 𝕜) (p := p) d I.1 (productHaar 𝕜 p I J) else 0 := by
  rw [operator_tsum_apply (upperCoordinateErrorTerm (𝕜 := 𝕜) (p := p) hp d) (upperCoordinateErrorBudget η)
    hb (norm_upperCoordinateErrorTerm_le (𝕜 := 𝕜) (p := p) hp d η hs hη)]
  by_cases hIJ : I.1 < J.1
  · rw [if_pos hIJ]
    have hseq : (fun k => upperCoordinateErrorTerm (𝕜 := 𝕜) (p := p) hp d k (productHaar 𝕜 p I J)) =
        (fun k => if I.1 + 1 ≤ k ∧ k < J.1 then
          symbolGrid (𝕜 := 𝕜) (p := p) d I.1 (k + 1) (productHaar 𝕜 p I J) -
            symbolGrid (𝕜 := 𝕜) (p := p) d I.1 k (productHaar 𝕜 p I J) else 0) := by
      funext k
      exact upperCoordinateErrorTerm_productHaar (𝕜 := 𝕜) (p := p) hp d k I J
    rw [hseq]
    simpa only [symbolGrid_productHaar_own_levels, symbolGrid_superdiagonal] using
      tsum_window_differences
        (fun n => symbolGrid (𝕜 := 𝕜) (p := p) d I.1 n (productHaar 𝕜 p I J)) (I.1 + 1) J.1 (by omega)
  · rw [if_neg hIJ]
    have hzero (k : ℕ) : ¬ (I.1 + 1 ≤ k ∧ k < J.1) := by omega
    simp only [upperCoordinateErrorTerm_productHaar, hzero, if_false, tsum_zero]

theorem upperBiTreeError_productHaar (hp : p ≠ ∞)
    (d : DyadicIndex → DyadicIndex → 𝕜) (η : ℕ → ℕ → ℝ)
    {δ : ℝ} (hs : SemiStable d η δ) (hη : ∀ i j, 0 ≤ η i j)
    (hdiag : Summable (upperDiagonalErrorBudget η))
    (hcoord : Summable (upperCoordinateErrorBudget η))
    (M : MixedNorm 𝕜 p →L[𝕜] MixedNorm 𝕜 p)
    (hM : Tendsto (superdiagonalGrid (𝕜 := 𝕜) (p := p) d) atTop (𝓝 M))
    (I J : DyadicIndex) :
    upperBiTreeError (𝕜 := 𝕜) (p := p) hp d (productHaar 𝕜 p I J) =
      if I.1 < J.1 then d I J • productHaar 𝕜 p I J -
        M (productHaar 𝕜 p I J) else 0 := by
  rw [upperBiTreeError, ContinuousLinearMap.add_apply,
    upperDiagonalErrorSeries_productHaar (𝕜 := 𝕜) (p := p) hp d η hs hη hdiag M hM I J,
    upperCoordinateErrorSeries_productHaar (𝕜 := 𝕜) (p := p) hp d η hs hη hcoord I J]
  split_ifs <;> abel

theorem norm_upperBiTreeError_le (hp : p ≠ ∞)
    (d : DyadicIndex → DyadicIndex → 𝕜) (η : ℕ → ℕ → ℝ)
    {δ : ℝ} (hs : SemiStable d η δ) (hη : ∀ i j, 0 ≤ η i j)
    (hdiag : Summable (upperDiagonalErrorBudget η))
    (hcoord : Summable (upperCoordinateErrorBudget η)) :
    ‖upperBiTreeError (𝕜 := 𝕜) (p := p) hp d‖ ≤
      (∑' k, upperDiagonalErrorBudget η k) + (∑' k, upperCoordinateErrorBudget η k) := by
  exact (norm_add_le _ _).trans (add_le_add
    (norm_operator_tsum_le (upperDiagonalErrorTerm (𝕜 := 𝕜) (p := p) hp d) (upperDiagonalErrorBudget η)
      hdiag (norm_upperDiagonalErrorTerm_le (𝕜 := 𝕜) (p := p) hp d η hs hη))
    (norm_operator_tsum_le (upperCoordinateErrorTerm (𝕜 := 𝕜) (p := p) hp d) (upperCoordinateErrorBudget η)
      hcoord (norm_upperCoordinateErrorTerm_le (𝕜 := 𝕜) (p := p) hp d η hs hη)))

end SurveyStatements.P5

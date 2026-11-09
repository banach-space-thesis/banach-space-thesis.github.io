import SurveyStatements.P5BiTreeErrorOperators
import SurveyStatements.P5MixedDyadicPieceSums
import SurveyStatements.P5GridLocalizedAction

/-! Exact actions of the upper error terms on genuine product Haar vectors.
The strip selector leaves one possible outer-level term in each finite sum. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory
open scoped ENNReal BigOperators

namespace SurveyStatements.P5
open P5Support
variable {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem upperDiagonalErrorTerm_productHaar (hp : p ≠ ∞)
    (d : DyadicIndex → DyadicIndex → 𝕜) (k : ℕ) (I J : DyadicIndex) :
    upperDiagonalErrorTerm (𝕜 := 𝕜) (p := p) hp d k (productHaar 𝕜 p I J) =
      if I.1 < J.1 ∧ I.1 ≤ k then
        superdiagonalGrid (𝕜 := 𝕜) (p := p) d k (productHaar 𝕜 p I J) -
          superdiagonalGrid (𝕜 := 𝕜) (p := p) d (k + 1) (productHaar 𝕜 p I J) else 0 := by
  have hc : (I.1 < k + 1 ∧ I.1 + 1 ≤ J.1) ↔ (I.1 < J.1 ∧ I.1 ≤ k) := by omega
  simpa only [upperDiagonalErrorTerm, hc, ContinuousLinearMap.sub_apply] using
    sum_upperStrips_productHaar (𝕜 := 𝕜) (p := p) hp (k + 1) (fun i => i + 1)
      (fun _ => superdiagonalGrid (𝕜 := 𝕜) (p := p) d k - superdiagonalGrid (𝕜 := 𝕜) (p := p) d (k + 1)) I J

theorem upperCoordinateErrorTerm_productHaar (hp : p ≠ ∞)
    (d : DyadicIndex → DyadicIndex → 𝕜) (k : ℕ) (I J : DyadicIndex) :
    upperCoordinateErrorTerm (𝕜 := 𝕜) (p := p) hp d k (productHaar 𝕜 p I J) =
      if I.1 + 1 ≤ k ∧ k < J.1 then
        symbolGrid (𝕜 := 𝕜) (p := p) d I.1 (k + 1) (productHaar 𝕜 p I J) -
          symbolGrid (𝕜 := 𝕜) (p := p) d I.1 k (productHaar 𝕜 p I J) else 0 := by
  have hc : (I.1 < k ∧ k + 1 ≤ J.1) ↔ (I.1 + 1 ≤ k ∧ k < J.1) := by omega
  simpa only [upperCoordinateErrorTerm, hc, ContinuousLinearMap.sub_apply] using
    sum_upperStrips_productHaar (𝕜 := 𝕜) (p := p) hp k (fun _ => k + 1)
      (fun i => symbolGrid (𝕜 := 𝕜) (p := p) d i (k + 1) - symbolGrid (𝕜 := 𝕜) (p := p) d i k) I J

theorem symbolGrid_productHaar_own_levels
    (d : DyadicIndex → DyadicIndex → 𝕜) (I J : DyadicIndex) :
    symbolGrid (𝕜 := 𝕜) (p := p) d I.1 J.1 (productHaar 𝕜 p I J) = d I J • productHaar 𝕜 p I J := by
  exact mixedDyadicGridOperator_local_productHaar (𝕜 := 𝕜) (p := p) I.1 J.1
    (fun i j => d ⟨I.1, i⟩ ⟨J.1, j⟩) I.2 J.2 I J Set.Subset.rfl Set.Subset.rfl

theorem symbolGrid_superdiagonal (d : DyadicIndex → DyadicIndex → 𝕜) (n : ℕ) :
    symbolGrid (𝕜 := 𝕜) (p := p) d n (n + 1) = superdiagonalGrid (𝕜 := 𝕜) (p := p) d n := rfl

end SurveyStatements.P5

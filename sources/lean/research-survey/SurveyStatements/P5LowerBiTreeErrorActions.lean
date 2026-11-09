import SurveyStatements.P5BiTreeErrorOperators
import SurveyStatements.P5MixedDyadicPieceSums
import SurveyStatements.P5GridLocalizedAction

/-! Exact finite lower-error actions, before taking their operator series. -/

noncomputable section
set_option autoImplicit false
open scoped ENNReal

namespace SurveyStatements.P5
variable {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem symbolGrid_productHaar (d : DyadicIndex → DyadicIndex → 𝕜)
    (I J : DyadicIndex) :
    symbolGrid (p := p) d I.1 J.1 (productHaar 𝕜 p I J) =
      d I J • productHaar 𝕜 p I J :=
  mixedDyadicGridOperator_local_productHaar I.1 J.1
    (fun i j => d ⟨I.1, i⟩ ⟨J.1, j⟩) I.2 J.2 I J Set.Subset.rfl Set.Subset.rfl

theorem lowerDiagonalErrorTerm_productHaar (hp : p ≠ ∞)
    (d : DyadicIndex → DyadicIndex → 𝕜) (k : ℕ) (I J : DyadicIndex) :
    lowerDiagonalErrorTerm (𝕜 := 𝕜) (p := p) hp d k (productHaar 𝕜 p I J) =
      if J.1 ≤ k ∧ J.1 ≤ I.1 then
        diagonalGrid (p := p) d k (productHaar 𝕜 p I J) -
          diagonalGrid (p := p) d (k + 1) (productHaar 𝕜 p I J) else 0 := by
  simpa only [lowerDiagonalErrorTerm, Nat.lt_succ_iff, ContinuousLinearMap.sub_apply] using
    sum_lowerStrips_productHaar hp (k + 1) (fun j => j)
      (fun _ => diagonalGrid (p := p) d k - diagonalGrid (p := p) d (k + 1)) I J

theorem lowerCoordinateErrorTerm_productHaar (hp : p ≠ ∞)
    (d : DyadicIndex → DyadicIndex → 𝕜) (k : ℕ) (I J : DyadicIndex) :
    lowerCoordinateErrorTerm (𝕜 := 𝕜) (p := p) hp d k (productHaar 𝕜 p I J) =
      if J.1 ≤ k ∧ k < I.1 then
        symbolGrid (p := p) d (k + 1) J.1 (productHaar 𝕜 p I J) -
          symbolGrid (p := p) d k J.1 (productHaar 𝕜 p I J) else 0 := by
  simpa only [lowerCoordinateErrorTerm, Nat.lt_succ_iff, Nat.succ_le_iff,
    ContinuousLinearMap.sub_apply] using
    sum_lowerStrips_productHaar hp (k + 1) (fun _ => k + 1)
      (fun j => symbolGrid (p := p) d (k + 1) j - symbolGrid (p := p) d k j) I J

end SurveyStatements.P5


import SurveyStatements.P5UpperBiTreeErrorSeries
import SurveyStatements.P5BiTreeGeometricBudget

/-! The displayed geometric accuracy array supplies both upper operator
series budgets, with a quantitative bound for their actual sum. -/

noncomputable section
set_option autoImplicit false
open scoped ENNReal BigOperators

namespace SurveyStatements.P5
open BiTree
variable {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem upperError_geometric_budgets {ε : ℝ} (hε : 0 ≤ ε) :
    Summable (upperDiagonalErrorBudget (biTreeAccuracy ε)) ∧
    Summable (upperCoordinateErrorBudget (biTreeAccuracy ε)) ∧
    (∑' k, upperDiagonalErrorBudget (biTreeAccuracy ε) k) ≤ ε / 128 ∧
    (∑' k, upperCoordinateErrorBudget (biTreeAccuracy ε) k) ≤ ε / 128 := by
  have hd := biTree_budget_summable_bound hε
    (upperDiagonalErrorBudget (biTreeAccuracy ε))
    (fun k => by unfold upperDiagonalErrorBudget biTreeAccuracy; positivity)
    (biTreeAccuracy_superdiagonal_budget_le hε)
  have hc := biTree_budget_summable_bound hε
    (upperCoordinateErrorBudget (biTreeAccuracy ε))
    (fun k => by
      apply mul_nonneg (by norm_num : (0 : ℝ) ≤ 4)
      apply Finset.sum_nonneg
      intro i _
      unfold biTreeAccuracy
      positivity)
    (biTreeAccuracy_upper_budget_le hε)
  exact ⟨hd.1, hc.1, hd.2, hc.2⟩

theorem norm_upperBiTreeError_geometric_le (hp : p ≠ ∞)
    (d : DyadicIndex → DyadicIndex → 𝕜) {ε δ : ℝ} (hε : 0 ≤ ε)
    (hs : SemiStable d (biTreeAccuracy ε) δ) :
    ‖upperBiTreeError (𝕜 := 𝕜) (p := p) hp d‖ ≤ ε / 64 := by
  obtain ⟨hd, hc, hdb, hcb⟩ := upperError_geometric_budgets hε
  have hη (i j : ℕ) : 0 ≤ biTreeAccuracy ε i j := by unfold biTreeAccuracy; positivity
  calc
    _ ≤ (∑' k, upperDiagonalErrorBudget (biTreeAccuracy ε) k) +
        (∑' k, upperCoordinateErrorBudget (biTreeAccuracy ε) k) :=
      norm_upperBiTreeError_le (𝕜 := 𝕜) (p := p) hp d (biTreeAccuracy ε) hs hη hd hc
    _ ≤ ε / 128 + ε / 128 := add_le_add hdb hcb
    _ = ε / 64 := by ring

end SurveyStatements.P5

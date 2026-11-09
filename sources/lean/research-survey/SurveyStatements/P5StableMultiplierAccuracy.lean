import SurveyStatements.P5BiTreeGeometricBudget
import SurveyStatements.P5StableMultiplierScalarClosure

/-! Quantitative scalar norm bound with an arbitrary stabilized symbol.
Keeping this estimate separate prevents the finite-tree construction from
being repeatedly unfolded in the numerical budget argument. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
open MeasureTheory Filter Topology
open scoped ENNReal BigOperators

namespace SurveyStatements.P5
open BiTree
attribute [local irreducible] probabilityLpIntegral probabilityLpMean
  outerExpectation innerExpectation DoublyZeroMean
variable {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

structure StableMultiplierAccuracyBudgets (ε : ℝ) : Prop where
  nonneg : ∀ i j, 0 ≤ biTreeAccuracy ε i j
  diagonalSummable : Summable (fun k => biTreeAccuracy ε k k)
  superdiagonalSummable : Summable (fun k => biTreeAccuracy ε k (k + 1))
  lowerDiagonalSummable : Summable (fun k => 4 * (k + 1 : ℕ) * biTreeAccuracy ε k k)
  lowerCoordinateSummable : Summable
    (fun k => 4 * ∑ j ∈ Finset.range (k + 1), biTreeAccuracy ε k j)
  upperDiagonalSummable : Summable (upperDiagonalErrorBudget (biTreeAccuracy ε))
  upperCoordinateSummable : Summable (upperCoordinateErrorBudget (biTreeAccuracy ε))
  diagonalBound : (∑' k, biTreeAccuracy ε k k) ≤ ε / 128
  lowerDiagonalBound : (∑' k, 4 * (k + 1 : ℕ) * biTreeAccuracy ε k k) ≤ ε / 128
  lowerCoordinateBound :
    (∑' k, 4 * ∑ j ∈ Finset.range (k + 1), biTreeAccuracy ε k j) ≤ ε / 128
  upperDiagonalBound : (∑' k, upperDiagonalErrorBudget (biTreeAccuracy ε) k) ≤ ε / 128
  upperCoordinateBound : (∑' k, upperCoordinateErrorBudget (biTreeAccuracy ε) k) ≤ ε / 128

theorem stable_multiplier_accuracy_budgets {ε : ℝ} (hε : 0 < ε) :
    StableMultiplierAccuracyBudgets ε := by
  have hη (i j : ℕ) : 0 ≤ biTreeAccuracy ε i j := (biTreeAccuracy_pos hε i j).le
  obtain ⟨hdiag, hdiag_bound⟩ := biTreeAccuracy_diagonal_summable_bound hε.le
  obtain ⟨hsuper, _⟩ := biTreeAccuracy_superdiagonal_summable_bound hε.le
  obtain ⟨hld, hld_bound⟩ := biTree_budget_summable_bound hε.le
    (fun k => 4 * (k + 1 : ℕ) * biTreeAccuracy ε k k)
    (fun k => mul_nonneg (by positivity) (hη k k))
    (biTreeAccuracy_diagonal_budget_le hε.le)
  obtain ⟨hlc, hlc_bound⟩ := biTree_budget_summable_bound hε.le
    (fun k => 4 * ∑ j ∈ Finset.range (k + 1), biTreeAccuracy ε k j)
    (fun k => mul_nonneg (by norm_num) (Finset.sum_nonneg (fun j _ => hη k j)))
    (biTreeAccuracy_lower_budget_le hε.le)
  obtain ⟨hud, hud_bound⟩ := biTree_budget_summable_bound hε.le
    (upperDiagonalErrorBudget (biTreeAccuracy ε))
    (fun k => by unfold upperDiagonalErrorBudget
                 exact mul_nonneg (by positivity) (hη k (k + 1)))
    (biTreeAccuracy_superdiagonal_budget_le hε.le)
  obtain ⟨huc, huc_bound⟩ := biTree_budget_summable_bound hε.le
    (upperCoordinateErrorBudget (biTreeAccuracy ε))
    (fun k => by unfold upperCoordinateErrorBudget
                 exact mul_nonneg (by norm_num) (Finset.sum_nonneg (fun i _ => hη i k)))
    (biTreeAccuracy_upper_budget_le hε.le)
  exact ⟨hη, hdiag, hsuper, hld, hlc, hud, huc, hdiag_bound,
    hld_bound, hlc_bound, hud_bound, huc_bound⟩

theorem exists_stable_accuracy_grid_limits
    (d : DyadicIndex → DyadicIndex → 𝕜) {ε : ℝ}
    (hs : SemiStable d (biTreeAccuracy ε) (ε / 4))
    (b : StableMultiplierAccuracyBudgets ε) :
    ∃ M1 M2 : MixedNorm 𝕜 p →L[𝕜] MixedNorm 𝕜 p,
      Tendsto (diagonalGrid (p := p) d) atTop (𝓝 M1) ∧
      Tendsto (superdiagonalGrid (p := p) d) atTop (𝓝 M2) := by
  obtain ⟨M1, hM1, _⟩ := exists_diagonalGrid_norm_limit (𝕜 := 𝕜) (p := p)
    d (biTreeAccuracy ε) hs (fun k => b.nonneg k k) b.diagonalSummable
  obtain ⟨M2, hM2, _⟩ := exists_superdiagonalGrid_norm_limit (𝕜 := 𝕜) (p := p)
    d (biTreeAccuracy ε) hs (fun k => b.nonneg k (k + 1)) b.superdiagonalSummable
  exact ⟨M1, M2, hM1, hM2⟩

theorem stable_multiplier_accuracy_norm_lt_of_budget (hp : p ≠ ∞)
    (T : DoublyZeroMean 𝕜 p →L[𝕜] DoublyZeroMean 𝕜 p)
    (d : DyadicIndex → DyadicIndex → 𝕜) (hT : IsProductHaarMultiplier T d)
    (η : ℕ → ℕ → ℝ) {δ : ℝ} (hs : SemiStable d η δ)
    (hη : ∀ i j, 0 ≤ η i j)
    (hdiag : Summable (fun k => η k k))
    (hld : Summable (fun k => 4 * (k + 1 : ℕ) * η k k))
    (hlc : Summable (fun k => 4 * ∑ j ∈ Finset.range (k + 1), η k j))
    (hud : Summable (upperDiagonalErrorBudget η))
    (huc : Summable (upperCoordinateErrorBudget η))
    (M1 M2 : MixedNorm 𝕜 p →L[𝕜] MixedNorm 𝕜 p)
    (hM1 : Tendsto (diagonalGrid (p := p) d) atTop (𝓝 M1))
    (hM2 : Tendsto (superdiagonalGrid (p := p) d) atTop (𝓝 M2))
    (lam : 𝕜) (ε : ℝ)
    (hsmall : ((∑' k, 4 * (k + 1 : ℕ) * η k k) +
        (∑' k, 4 * ∑ j ∈ Finset.range (k + 1), η k j)) +
      ((∑' k, upperDiagonalErrorBudget η k) +
        (∑' k, upperCoordinateErrorBudget η k)) +
      ((∑' k, η k k) + ‖d root root - lam‖) < ε) :
    ‖T - lam • ContinuousLinearMap.id 𝕜 (DoublyZeroMean 𝕜 p)‖ < ε := by
  letI : NormedAddCommGroup (MixedNorm 𝕜 p) := inferInstance
  letI : NormedSpace 𝕜 (MixedNorm 𝕜 p) := inferInstance
  letI : NormedAddCommGroup (DoublyZeroMean 𝕜 p) := inferInstance
  letI : NormedSpace 𝕜 (DoublyZeroMean 𝕜 p) := inferInstance
  have hnorm := stable_multiplier_norm_sub_scalar_le (𝕜 := 𝕜) (p := p)
    hp T d hT η hs hη hld hlc hud huc M1 M2 hM1 hM2 lam
  have hlower := norm_lowerBiTreeError_le (𝕜 := 𝕜) (p := p) hp d η hs hη hld hlc
  have hupper := norm_upperBiTreeError_le (𝕜 := 𝕜) (p := p) hp d η hs hη hud huc
  have hscalar := norm_diagonalGrid_limit_sub_scalar_le (𝕜 := 𝕜) (p := p)
    d η hs (fun k => hη k k) hdiag M1 hM1 lam
  exact hnorm.trans_lt ((add_le_add (add_le_add hlower hupper) hscalar).trans_lt hsmall)

theorem stable_multiplier_accuracy_norm_lt (hp : p ≠ ∞)
    (T : DoublyZeroMean 𝕜 p →L[𝕜] DoublyZeroMean 𝕜 p)
    (d : DyadicIndex → DyadicIndex → 𝕜) (hT : IsProductHaarMultiplier T d)
    {ε : ℝ} (hε : 0 < ε) (hs : SemiStable d (biTreeAccuracy ε) (ε / 4))
    (lam : 𝕜) (hroot : ‖d root root - lam‖ < ε / 4) :
    ‖T - lam • ContinuousLinearMap.id 𝕜 (DoublyZeroMean 𝕜 p)‖ < ε := by
  let b := stable_multiplier_accuracy_budgets hε
  obtain ⟨M1, M2, hM1, hM2⟩ :=
    exists_stable_accuracy_grid_limits (𝕜 := 𝕜) (p := p) d hs b
  apply stable_multiplier_accuracy_norm_lt_of_budget (𝕜 := 𝕜) (p := p)
    hp T d hT (biTreeAccuracy ε) hs b.nonneg b.diagonalSummable
    b.lowerDiagonalSummable b.lowerCoordinateSummable b.upperDiagonalSummable
    b.upperCoordinateSummable M1 M2 hM1 hM2 lam ε
  exact (add_lt_add_of_le_of_lt
    (add_le_add (add_le_add b.lowerDiagonalBound b.lowerCoordinateBound)
      (add_le_add b.upperDiagonalBound b.upperCoordinateBound))
    (add_lt_add_of_le_of_lt b.diagonalBound hroot)).trans (by linarith only [hε])

end SurveyStatements.P5

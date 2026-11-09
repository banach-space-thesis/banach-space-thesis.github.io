import SurveyStatements.P5DyadicGridRefinement
import SurveyStatements.P5DyadicGridLinear
import SurveyStatements.P5BiTreeStabilizationDefinitions
import SurveyStatements.P5OperatorSeriesBounds
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! Actual operator norm limits of the diagonal and superdiagonal grids.
The estimates use the corresponding child conditions of SemiStable. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open MeasureTheory Filter Topology
open scoped ENNReal

namespace SurveyStatements.P5
open P5Support BiTree
variable {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem dyadicIndex_eq_child_parent (n : ℕ) (k : Fin (2 ^ (n + 1))) :
    ∃ b, child ⟨n, lpHaarParentIndex n k⟩ b = ⟨n + 1, k⟩ := by
  have hk : k.val = 2 * (k.val / 2) ∨ k.val = 2 * (k.val / 2) + 1 := by omega
  rcases hk with hk | hk
  · refine ⟨true, ?_⟩
    change (⟨n + 1, lpHaarLeftIndex n (lpHaarParentIndex n k)⟩ : DyadicIndex) = _
    congr 1
    apply Fin.ext
    exact hk.symm
  · refine ⟨false, ?_⟩
    change (⟨n + 1, lpHaarRightIndex n (lpHaarParentIndex n k)⟩ : DyadicIndex) = _
    congr 1
    apply Fin.ext
    exact hk.symm

def diagonalGrid (d : DyadicIndex → DyadicIndex → 𝕜) (n : ℕ) :
    MixedNorm 𝕜 p →L[𝕜] MixedNorm 𝕜 p :=
  mixedDyadicGridOperator n n (fun i j => d ⟨n, i⟩ ⟨n, j⟩)

def superdiagonalGrid (d : DyadicIndex → DyadicIndex → 𝕜) (n : ℕ) :
    MixedNorm 𝕜 p →L[𝕜] MixedNorm 𝕜 p :=
  mixedDyadicGridOperator n (n + 1) (fun i j => d ⟨n, i⟩ ⟨n + 1, j⟩)

theorem norm_diagonalGrid_step_le (d : DyadicIndex → DyadicIndex → 𝕜)
    (η : ℕ → ℕ → ℝ) {δ : ℝ} (hs : SemiStable d η δ)
    (hη : ∀ n, 0 ≤ η n n) (n : ℕ) :
    ‖diagonalGrid (p := p) d (n + 1) - diagonalGrid d n‖ ≤ η n n := by
  have href : mixedDyadicGridOperator (p := p) (n + 1) (n + 1)
      (fun i j => d ⟨n, lpHaarParentIndex n i⟩ ⟨n, lpHaarParentIndex n j⟩) =
      diagonalGrid d n := by
    rw [mixedDyadicGridOperator_refine_inner (𝕜 := 𝕜) (p := p) (n + 1) n
      (fun i j => d ⟨n, lpHaarParentIndex n i⟩ ⟨n, j⟩)]
    exact mixedDyadicGridOperator_refine_outer (𝕜 := 𝕜) (p := p) n n
      (fun i j => d ⟨n, i⟩ ⟨n, j⟩)
  rw [← href]
  unfold diagonalGrid
  apply norm_mixedDyadicGridOperator_sub_le (p := p) _ _ _ _ (hη n)
  intro i j
  obtain ⟨b, hb⟩ := dyadicIndex_eq_child_parent n i
  obtain ⟨c, hc⟩ := dyadicIndex_eq_child_parent n j
  simpa only [hb, hc] using hs.diagonal
    ⟨n, lpHaarParentIndex n i⟩ ⟨n, lpHaarParentIndex n j⟩ b c rfl

theorem norm_superdiagonalGrid_step_le (d : DyadicIndex → DyadicIndex → 𝕜)
    (η : ℕ → ℕ → ℝ) {δ : ℝ} (hs : SemiStable d η δ)
    (hη : ∀ n, 0 ≤ η n (n + 1)) (n : ℕ) :
    ‖superdiagonalGrid (p := p) d (n + 1) - superdiagonalGrid d n‖ ≤ η n (n + 1) := by
  have href : mixedDyadicGridOperator (p := p) (n + 1) ((n + 1) + 1)
      (fun i j => d ⟨n, lpHaarParentIndex n i⟩
        ⟨n + 1, lpHaarParentIndex (n + 1) j⟩) = superdiagonalGrid d n := by
    rw [mixedDyadicGridOperator_refine_inner (𝕜 := 𝕜) (p := p) (n + 1) (n + 1)
      (fun i j => d ⟨n, lpHaarParentIndex n i⟩ ⟨n + 1, j⟩)]
    exact mixedDyadicGridOperator_refine_outer (𝕜 := 𝕜) (p := p) n (n + 1)
      (fun i j => d ⟨n, i⟩ ⟨n + 1, j⟩)
  rw [← href]
  unfold superdiagonalGrid
  apply norm_mixedDyadicGridOperator_sub_le (p := p) _ _ _ _ (hη n)
  intro i j
  obtain ⟨b, hb⟩ := dyadicIndex_eq_child_parent n i
  obtain ⟨c, hc⟩ := dyadicIndex_eq_child_parent (n + 1) j
  simpa only [hb, hc] using hs.superdiagonal
    ⟨n, lpHaarParentIndex n i⟩ ⟨n + 1, lpHaarParentIndex (n + 1) j⟩ b c rfl

theorem exists_operator_norm_limit_of_summable_steps
    {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
    (G : ℕ → X →L[𝕜] X) (b : ℕ → ℝ) (hb : Summable b)
    (hG : ∀ n, ‖G (n + 1) - G n‖ ≤ b n) :
    ∃ M, Tendsto G atTop (𝓝 M) ∧
      ∀ n, ‖M - G n‖ ≤ ∑' k, b (n + k) := by
  have hdist (n : ℕ) : dist (G n) (G n.succ) ≤ b n := by
    rw [dist_comm, dist_eq_norm]
    exact hG n
  obtain ⟨M, hM⟩ := cauchySeq_tendsto_of_complete
    (cauchySeq_of_dist_le_of_summable b hdist hb)
  refine ⟨M, hM, fun n => ?_⟩
  calc
    ‖M - G n‖ = dist (G n) M := by rw [dist_eq_norm, norm_sub_rev]
    _ ≤ ∑' k, b (n + k) := dist_le_tsum_of_dist_le_of_tendsto b hdist hb hM n

theorem exists_diagonalGrid_norm_limit (d : DyadicIndex → DyadicIndex → 𝕜)
    (η : ℕ → ℕ → ℝ) {δ : ℝ} (hs : SemiStable d η δ)
    (hη : ∀ n, 0 ≤ η n n) (hsum : Summable (fun n => η n n)) :
    ∃ M, Tendsto (diagonalGrid (p := p) d) atTop (𝓝 M) ∧
      ∀ n, ‖M - diagonalGrid d n‖ ≤ ∑' k, η (n + k) (n + k) :=
  exists_operator_norm_limit_of_summable_steps (diagonalGrid d) _ hsum
    (norm_diagonalGrid_step_le d η hs hη)

theorem exists_superdiagonalGrid_norm_limit (d : DyadicIndex → DyadicIndex → 𝕜)
    (η : ℕ → ℕ → ℝ) {δ : ℝ} (hs : SemiStable d η δ)
    (hη : ∀ n, 0 ≤ η n (n + 1)) (hsum : Summable (fun n => η n (n + 1))) :
    ∃ M, Tendsto (superdiagonalGrid (p := p) d) atTop (𝓝 M) ∧
      ∀ n, ‖M - superdiagonalGrid d n‖ ≤ ∑' k, η (n + k) (n + k + 1) :=
  exists_operator_norm_limit_of_summable_steps (superdiagonalGrid d) _ hsum
    (norm_superdiagonalGrid_step_le d η hs hη)

end SurveyStatements.P5

import SurveyStatements.P5OperatorReductionEdgeMultipliers
import SurveyStatements.P5Support.LpHaarGeometricEdgeBudget

/-! Total geometric trace budgets construct small actual strip multipliers.
The root value is included explicitly in the operator norm estimate. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open MeasureTheory Set
open scoped ENNReal BigOperators

namespace SurveyStatements.P5OperatorReduction
open SurveyStatements.P5Support
variable {𝕜 : Type*} [RCLike 𝕜]
local instance balancedIntervalProbability :
    IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) := ⟨by simp⟩

def edgeTreeRoot : LpHaarTreeIndex := ⟨0, ⟨0, by decide⟩⟩

theorem edgeTreeRoot_mem_ancestors (n : ℕ) (k : Fin (2 ^ n)) :
    edgeTreeRoot ∈ lpHaarAncestors n k := by
  induction n with
  | zero =>
      have hk : k = ⟨0, by decide⟩ := by
        apply Fin.ext
        have hlt := k.isLt
        simp only [pow_zero] at hlt
        omega
      simp only [hk, lpHaarAncestors, edgeTreeRoot, Finset.mem_singleton]
  | succ n ih =>
      exact Finset.mem_insert_of_mem (ih (lpHaarParentIndex n k))

theorem edgeRootProjection_haar (p : BanachExponent) (hp : p.val ≠ ∞)
    (n : ℕ) (k : Fin (2 ^ n)) :
    lpHaarSubtreeProjection 𝕜 p hp 0 0 (lpHaarDyadic 𝕜 p n k) =
      lpHaarDyadic 𝕜 p n k := by
  change lpHaarSubtreeProjection 𝕜 p hp edgeTreeRoot.1 edgeTreeRoot.2
    (lpHaarDyadic 𝕜 p n k) = _
  rw [lpHaarSubtreeProjection_haar 𝕜 p hp edgeTreeRoot n k,
    if_pos (edgeTreeRoot_mem_ancestors n k)]

def traceBalancedMultiplier (p : BanachExponent) (hp : p.val ≠ ∞)
    (d : LpHaarTreeIndex → 𝕜) (c : 𝕜) :
    IntervalLp 𝕜 p →L[𝕜] IntervalLp 𝕜 p :=
  lpHaarSubtreeSeries 𝕜 p hp (lpHaarEdgeDifference d c) +
    c • lpHaarSubtreeProjection 𝕜 p hp 0 0

theorem traceBalancedMultiplier_haar (p : BanachExponent) (hp : p.val ≠ ∞)
    (d : LpHaarTreeIndex → 𝕜) (c : 𝕜)
    (hd : Summable (fun i => ‖lpHaarEdgeDifference d c i‖))
    (n : ℕ) (k : Fin (2 ^ n)) :
    traceBalancedMultiplier p hp d c (lpHaarDyadic 𝕜 p n k) =
      d ⟨n, k⟩ • lpHaarDyadic 𝕜 p n k := by
  rw [traceBalancedMultiplier, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, lpHaarSubtreeSeries_haar 𝕜 p hp _ hd,
    lpHaarEdgeDifference_path, edgeRootProjection_haar p hp]
  module

theorem traceBalancedMultiplier_const (p : BanachExponent) (hp : p.val ≠ ∞)
    (d : LpHaarTreeIndex → 𝕜) (c : 𝕜)
    (hd : Summable (fun i => ‖lpHaarEdgeDifference d c i‖)) :
    traceBalancedMultiplier p hp d c
      (Lp.const p.val (volume.restrict (Icc (0 : ℝ) 1)) (1 : 𝕜)) = 0 := by
  rw [traceBalancedMultiplier, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, lpHaarSubtreeSeries_const 𝕜 p hp _ hd,
    lpHaarSubtreeProjection_const, smul_zero, add_zero]

theorem norm_traceBalancedMultiplier_le (p : BanachExponent) (hp : p.val ≠ ∞)
    (d : LpHaarTreeIndex → 𝕜) (c : 𝕜)
    (hd : Summable (fun i => ‖lpHaarEdgeDifference d c i‖)) :
    ‖traceBalancedMultiplier p hp d c‖ ≤
      2 * (∑' i, ‖lpHaarEdgeDifference d c i‖) + 2 * ‖c‖ := by
  apply (norm_add_le _ _).trans
  apply add_le_add (norm_lpHaarSubtreeSeries_le 𝕜 p hp _ hd)
  rw [norm_smul, mul_comm]
  exact mul_le_mul_of_nonneg_right
    (norm_lpHaarSubtreeProjection_le 𝕜 p hp 0 0) (norm_nonneg c)

theorem exists_small_geometric_trace_multiplier (p : BanachExponent) (hp : p.val ≠ ∞)
    (g t : ℕ → 𝕜) {δ : ℝ} (hδ : 0 ≤ δ)
    (hg : ∀ j, ‖g j - t j‖ ≤ lpHaarTraceErrorBudget δ j)
    (ht : ∀ j, j ≠ 0 → ‖t j - t ((j - 1) / 2)‖ ≤
      lpHaarTraceErrorBudget δ ((j - 1) / 2))
    (hroot : ‖t 0‖ ≤ δ) :
    ∃ Q : IntervalLp 𝕜 p →L[𝕜] IntervalLp 𝕜 p,
      ‖Q‖ ≤ 14 * δ ∧
      (∀ n (k : Fin (2 ^ n)), Q (lpHaarDyadic 𝕜 p n k) =
        g (lpHaarHeapIndex n k) • lpHaarDyadic 𝕜 p n k) ∧
      Q (Lp.const p.val (volume.restrict (Icc (0 : ℝ) 1)) (1 : 𝕜)) = 0 := by
  let d (i : LpHaarTreeIndex) : 𝕜 := g (lpHaarHeapIndex i.1 i.2)
  obtain ⟨hd, hsum⟩ := lpHaar_geometric_edge_budget g t hδ hg ht
  refine ⟨traceBalancedMultiplier p hp d (t 0), ?_, ?_,
    traceBalancedMultiplier_const p hp d (t 0) hd⟩
  · exact (norm_traceBalancedMultiplier_le p hp d (t 0) hd).trans (by linarith)
  · exact traceBalancedMultiplier_haar p hp d (t 0) hd

end SurveyStatements.P5OperatorReduction

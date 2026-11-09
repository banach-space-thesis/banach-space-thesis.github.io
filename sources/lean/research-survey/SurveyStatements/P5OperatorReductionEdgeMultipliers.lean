import SurveyStatements.P5Support.LpHaarEdgeVariation

/-! Actual scalar Haar multipliers constructed from total summable edge
changes. These operators, rather than bounded coefficient assertions,
supply the coordinate strip errors in the arbitrary-operator reduction. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open MeasureTheory Set
open scoped ENNReal BigOperators

namespace SurveyStatements.P5OperatorReduction
open SurveyStatements.P5Support
variable {𝕜 : Type*} [RCLike 𝕜]
local instance edgeIntervalProbability :
    IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) := ⟨by simp⟩

def edgeTraceMultiplier (p : BanachExponent) (hp : p.val ≠ ∞)
    (d : LpHaarTreeIndex → 𝕜) : IntervalLp 𝕜 p →L[𝕜] IntervalLp 𝕜 p :=
  lpHaarSubtreeSeries 𝕜 p hp (lpHaarEdgeDifference d 0)

theorem norm_edgeTraceMultiplier_le (p : BanachExponent) (hp : p.val ≠ ∞)
    (d : LpHaarTreeIndex → 𝕜)
    (hd : Summable (fun i => ‖lpHaarEdgeDifference d 0 i‖)) :
    ‖edgeTraceMultiplier p hp d‖ ≤ 2 * ∑' i, ‖lpHaarEdgeDifference d 0 i‖ :=
  norm_lpHaarSubtreeSeries_le 𝕜 p hp _ hd

theorem edgeTraceMultiplier_haar (p : BanachExponent) (hp : p.val ≠ ∞)
    (d : LpHaarTreeIndex → 𝕜)
    (hd : Summable (fun i => ‖lpHaarEdgeDifference d 0 i‖))
    (n : ℕ) (k : Fin (2 ^ n)) :
    edgeTraceMultiplier p hp d (lpHaarDyadic 𝕜 p n k) =
      d ⟨n, k⟩ • lpHaarDyadic 𝕜 p n k := by
  rw [edgeTraceMultiplier, lpHaarSubtreeSeries_haar 𝕜 p hp _ hd,
    lpHaarEdgeDifference_path, sub_zero]

theorem edgeTraceMultiplier_const (p : BanachExponent) (hp : p.val ≠ ∞)
    (d : LpHaarTreeIndex → 𝕜)
    (hd : Summable (fun i => ‖lpHaarEdgeDifference d 0 i‖)) :
    edgeTraceMultiplier p hp d
      (Lp.const p.val (volume.restrict (Icc (0 : ℝ) 1)) (1 : 𝕜)) = 0 :=
  lpHaarSubtreeSeries_const 𝕜 p hp _ hd

theorem edgeTraceMultiplier_raw_integral (p : BanachExponent) (hp : p.val ≠ ∞)
    (d : LpHaarTreeIndex → 𝕜)
    (hd : Summable (fun i => ‖lpHaarEdgeDifference d 0 i‖))
    (i : Option LpHaarTreeIndex) :
    lpHaarIntegral (edgeTraceMultiplier p hp d (lpHaarRawVector 𝕜 p i)) = 0 := by
  cases i with
  | none =>
      rw [lpHaarRawVector, edgeTraceMultiplier_const p hp d hd, map_zero]
  | some i =>
      rcases i with ⟨n, k⟩
      rw [lpHaarRawVector, edgeTraceMultiplier_haar p hp d hd, map_smul,
        lpHaarIntegral_apply, lpHaarDyadic_integral_zero 𝕜 p n k k.isLt, smul_zero]

theorem edgeTraceMultiplier_integral_comp (p : BanachExponent) (hp : p.val ≠ ∞)
    (d : LpHaarTreeIndex → 𝕜)
    (hd : Summable (fun i => ‖lpHaarEdgeDifference d 0 i‖)) :
    (lpHaarIntegral (𝕜 := 𝕜) (p := p.val)
      (μ := volume.restrict (Icc (0 : ℝ) 1))).comp
        (edgeTraceMultiplier p hp d) = 0 := by
  apply (intervalLpHaarBasis 𝕜 p hp).operator_ext
  intro j
  change lpHaarIntegral (edgeTraceMultiplier p hp d
    (lpHaarNormalizedVector 𝕜 p (lpHaarIndexEquiv j))) = 0
  simp only [lpHaarNormalizedVector, map_smul,
    edgeTraceMultiplier_raw_integral p hp d hd, smul_zero]

theorem edgeTraceMultiplier_integral (p : BanachExponent) (hp : p.val ≠ ∞)
    (d : LpHaarTreeIndex → 𝕜)
    (hd : Summable (fun i => ‖lpHaarEdgeDifference d 0 i‖))
    (f : IntervalLp 𝕜 p) :
    lpHaarIntegral (edgeTraceMultiplier p hp d f) = 0 :=
  congrArg (fun L : IntervalLp 𝕜 p →L[𝕜] 𝕜 => L f)
    (edgeTraceMultiplier_integral_comp p hp d hd)

end SurveyStatements.P5OperatorReduction

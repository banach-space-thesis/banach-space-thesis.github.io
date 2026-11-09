import SurveyStatements.P5OperatorReductionTraceSystem
import SurveyStatements.P5OperatorReductionNormalizedTraceBalances

/-! Both actual normalized trace families satisfy the two child balance
moment limits required by the concrete alternating construction. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal Classical BigOperators Topology
namespace SurveyStatements.P5OperatorReduction
open SurveyStatements.P5 SurveyStatements.P5Support SurveyStatements.P5Support.Grothendieck
variable {𝕜 : Type*} [RCLike 𝕜]

theorem actualNormalizedOuterTrace_balance_moment_tendsto_zero (p : BanachExponent)
    (T : MixedNorm 𝕜 p.val →L[𝕜] MixedNorm 𝕜 p.val) {r : ℕ → ℕ}
    (a : UniversalInnerPairRegisteredTraces p T r)
    (pair : LpHaarFiniteSplit × LpHaarFiniteSplit) (P : LpHaarFiniteParent) (s : Bool) :
    Tendsto (fun n => mean (fun θ : Fin (2 ^ n) → Bool =>
      ‖actualNormalizedOuterTrace p T a pair ((candidateRefinedSplit P n θ).child s) -
        actualNormalizedOuterTrace p T a pair (candidateRefinedSplit P n θ).parent‖ ^ 2))
      atTop (𝓝 0) :=
  normalized_registered_trace_balance_moment_tendsto_zero (a pair)
    (mul_nonneg (by norm_num) (norm_nonneg _)) P s

theorem actualNormalizedInnerTrace_balance_moment_tendsto_zero (p : BanachExponent)
    (T : MixedNorm 𝕜 p.val →L[𝕜] MixedNorm 𝕜 p.val)
    (pair : LpHaarFiniteSplit × LpHaarFiniteSplit) (P : LpHaarFiniteParent) (s : Bool) :
    Tendsto (fun n => mean (fun θ : Fin (2 ^ n) → Bool =>
      ‖actualNormalizedInnerTrace p T pair ((candidateRefinedSplit P n θ).child s) -
        actualNormalizedInnerTrace p T pair (candidateRefinedSplit P n θ).parent‖ ^ 2))
      atTop (𝓝 0) := by
  let a := actualInnerSliceRegisteredTrace p T (pair.2.vector 𝕜 p)
    (splitRawWeight pair.1) (splitRawWeight_measurable pair.1) (splitRawWeight_bound pair.1)
  have ht := normalized_registered_trace_balance_moment_tendsto_zero a
    (mul_nonneg (norm_nonneg T) (norm_nonneg _)) P s
  simpa only [actualNormalizedInnerTrace, ← mul_sub] using
    signed_second_moment_const_mul_tendsto_zero _
      ((unitIntervalMeasure.real pair.1.parent.set : 𝕜)⁻¹) ht

end SurveyStatements.P5OperatorReduction

import SurveyStatements.P5OperatorReductionTraceSystem
import SurveyStatements.P5OperatorReductionBlockReaderWeights

/-! The actual inner trace is the scalar limit of the actual outer
shadow tested by the parent-normalized finite block reader. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal Classical BigOperators Topology
namespace SurveyStatements.P5OperatorReduction
open SurveyStatements.P5 SurveyStatements.P5Support
variable {𝕜 : Type*} [RCLike 𝕜]

theorem outerShadow_blockReader_tendsto (p : BanachExponent)
    (T : MixedNorm 𝕜 p.val →L[𝕜] MixedNorm 𝕜 p.val)
    (pair : LpHaarFiniteSplit × LpHaarFiniteSplit) (B : LpHaarFiniteParent) :
    Tendsto (fun m => pair.1.reader 𝕜 p
      (outerHaarPacketShadow p T (B.level + m)
        (shadowDescendants B.level B.atoms m) (pair.2.vector 𝕜 p)))
      atTop (𝓝 (actualNormalizedInnerTrace p T pair B)) := by
  have h := (outerHaarPacketShadow_localTrace_tendsto p T (pair.2.vector 𝕜 p)
    (splitRawWeight pair.1) (splitRawWeight_measurable pair.1)
    (splitRawWeight_bound pair.1) B.level B.atoms).const_mul
      (unitIntervalMeasure.real pair.1.parent.set : 𝕜)⁻¹
  rw [← actualNormalizedInnerTrace_eq_local p T pair B] at h
  convert h using 1
  funext m
  rw [LpHaarFiniteSplit.reader, lpHaarSignedBlockReader_eq_rawWeightedReader,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  rfl

end SurveyStatements.P5OperatorReduction

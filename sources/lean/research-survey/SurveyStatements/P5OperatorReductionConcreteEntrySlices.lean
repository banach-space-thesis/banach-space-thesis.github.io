import SurveyStatements.P5OperatorReductionConcreteSteps
import SurveyStatements.P5OperatorReductionOuterSlices
import SurveyStatements.P5OperatorReductionTraceSystem
import SurveyStatements.P5OperatorReductionBlockReaderWeights
import SurveyStatements.P5TensorBilinearity

/-! In each genuinely off-diagonal birth entry, the one fresh block is
tested against an actual fixed vector or a fixed bounded functional. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory
open scoped ENNReal Classical
namespace SurveyStatements.P5OperatorReduction
open SurveyStatements.P5 SurveyStatements.P5Support
variable {𝕜 : Type*} [RCLike 𝕜]

def concreteOuterInputFunctional (p : BanachExponent)
    (T : MixedNorm 𝕜 p.val →L[𝕜] MixedNorm 𝕜 p.val)
    (Ot It Is : LpHaarFiniteSplit) : IntervalLp 𝕜 p →L[𝕜] 𝕜 :=
  (Ot.reader 𝕜 p).comp
    (outerSliceOperator T (Is.vector 𝕜 concreteInnerExponent)
      (It.reader 𝕜 concreteInnerExponent))

theorem concreteMixedEntry_outerInput (p : BanachExponent)
    (T : MixedNorm 𝕜 p.val →L[𝕜] MixedNorm 𝕜 p.val)
    (Ot It Os Is : LpHaarFiniteSplit) :
    concreteMixedEntry p T Ot It Os Is =
      concreteOuterInputFunctional p T Ot It Is (Os.vector 𝕜 p) := rfl

def concreteInnerInputFunctional (p : BanachExponent)
    (T : MixedNorm 𝕜 p.val →L[𝕜] MixedNorm 𝕜 p.val)
    (Ot It Os : LpHaarFiniteSplit) :
    Lp 𝕜 1 unitIntervalMeasure →L[𝕜] 𝕜 :=
  (Ot.reader 𝕜 p).comp
    (((It.reader 𝕜 concreteInnerExponent).compLpL p.val unitIntervalMeasure).comp
      (T.comp (tensorInnerMap (Os.vector 𝕜 p))))

theorem concreteMixedEntry_innerInput (p : BanachExponent)
    (T : MixedNorm 𝕜 p.val →L[𝕜] MixedNorm 𝕜 p.val)
    (Ot It Os Is : LpHaarFiniteSplit) :
    concreteMixedEntry p T Ot It Os Is =
      concreteInnerInputFunctional p T Ot It Os (Is.vector 𝕜 concreteInnerExponent) := rfl

def concreteOuterOutputVector (p : BanachExponent)
    (T : MixedNorm 𝕜 p.val →L[𝕜] MixedNorm 𝕜 p.val)
    (It Os Is : LpHaarFiniteSplit) : IntervalLp 𝕜 p :=
  ((It.reader 𝕜 concreteInnerExponent).compLpL p.val unitIntervalMeasure)
    (T (tensorWith (Is.vector 𝕜 concreteInnerExponent) (Os.vector 𝕜 p)))

theorem concreteMixedEntry_outerOutput (p : BanachExponent)
    (T : MixedNorm 𝕜 p.val →L[𝕜] MixedNorm 𝕜 p.val)
    (Ot It Os Is : LpHaarFiniteSplit) :
    concreteMixedEntry p T Ot It Os Is = Ot.reader 𝕜 p
      (concreteOuterOutputVector p T It Os Is) := rfl

def concreteInnerOutputVector (p : BanachExponent)
    (T : MixedNorm 𝕜 p.val →L[𝕜] MixedNorm 𝕜 p.val)
    (Ot Os Is : LpHaarFiniteSplit) : Lp 𝕜 1 unitIntervalMeasure :=
  (unitIntervalMeasure.real Ot.parent.set : 𝕜)⁻¹ •
    weightedOuterReader (𝕜 := 𝕜) (E := Lp 𝕜 1 unitIntervalMeasure) (p := p.val)
      (splitRawWeight Ot) (splitRawWeight_measurable Ot) (splitRawWeight_bound Ot)
      (T (tensorWith (Is.vector 𝕜 concreteInnerExponent) (Os.vector 𝕜 p)))

theorem concreteMixedEntry_innerOutput (p : BanachExponent)
    (T : MixedNorm 𝕜 p.val →L[𝕜] MixedNorm 𝕜 p.val)
    (Ot It Os Is : LpHaarFiniteSplit) :
    concreteMixedEntry p T Ot It Os Is = It.reader 𝕜 concreteInnerExponent
      (concreteInnerOutputVector p T Ot Os Is) := by
  unfold concreteMixedEntry
  rw [LpHaarFiniteSplit.reader,
    lpHaarSignedBlockReader_eq_rawWeightedReader p Ot.level Ot.atoms Ot.signs,
    ContinuousLinearMap.smul_apply]
  change (unitIntervalMeasure.real Ot.parent.set : 𝕜)⁻¹ •
    weightedOuterReader (𝕜 := 𝕜) (E := 𝕜) (p := p.val)
      (splitRawWeight Ot) (splitRawWeight_measurable Ot) (splitRawWeight_bound Ot)
      (((It.reader 𝕜 concreteInnerExponent).compLpL p.val unitIntervalMeasure)
        (T (tensorWith (Is.vector 𝕜 concreteInnerExponent) (Os.vector 𝕜 p)))) = _
  calc
    _ = (unitIntervalMeasure.real Ot.parent.set : 𝕜)⁻¹ •
        (It.reader 𝕜 concreteInnerExponent)
          (weightedOuterReader (𝕜 := 𝕜) (E := Lp 𝕜 1 unitIntervalMeasure) (p := p.val)
            (splitRawWeight Ot) (splitRawWeight_measurable Ot) (splitRawWeight_bound Ot)
            (T (tensorWith (Is.vector 𝕜 concreteInnerExponent) (Os.vector 𝕜 p)))) := by
      exact congrArg (fun z : 𝕜 => (unitIntervalMeasure.real Ot.parent.set : 𝕜)⁻¹ • z)
        (weightedOuterReader_natural (𝕜 := 𝕜) (E := Lp 𝕜 1 unitIntervalMeasure)
          (F := 𝕜) (p := p.val) (splitRawWeight Ot) (splitRawWeight_measurable Ot)
          (splitRawWeight_bound Ot) (It.reader 𝕜 concreteInnerExponent)
          (T (tensorWith (Is.vector 𝕜 concreteInnerExponent) (Os.vector 𝕜 p))))
    _ = _ := by
      unfold concreteInnerOutputVector
      rw [map_smul]

end SurveyStatements.P5OperatorReduction

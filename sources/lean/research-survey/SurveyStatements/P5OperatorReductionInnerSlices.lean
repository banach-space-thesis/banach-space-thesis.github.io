import SurveyStatements.P5L1VariationTraceFunctional
import SurveyStatements.P5OperatorReductionReaders
import SurveyStatements.P5TensorBilinearity

/-! Actual one-coordinate slices of an arbitrary mixed operator. The
trace is applied to a genuine operator on the mean-zero L1 subspace. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory
open scoped ENNReal
namespace SurveyStatements.P5OperatorReduction
open SurveyStatements.P5 SurveyStatements.P5Support SurveyStatements.P5L1Variation
variable {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem contraction_apply_bound {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (R : X →L[𝕜] Y) (hR : ‖R‖ ≤ 1) (x : X) : ‖R x‖ ≤ ‖x‖ := by
  exact (R.le_opNorm x).trans (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hR (norm_nonneg x))

def innerSliceOperator (T : MixedNorm 𝕜 p →L[𝕜] MixedNorm 𝕜 p)
    (f : Lp 𝕜 p unitIntervalMeasure) (η : ℝ → 𝕜)
    (hη : StronglyMeasurable η) (hb : ∀ x, ‖η x‖ ≤ 1) :
    Lp 𝕜 1 unitIntervalMeasure →L[𝕜] Lp 𝕜 1 unitIntervalMeasure :=
  (weightedOuterReader η hη hb).comp (T.comp (tensorInnerMap f))

theorem innerSliceOperator_apply (T : MixedNorm 𝕜 p →L[𝕜] MixedNorm 𝕜 p)
    (f : Lp 𝕜 p unitIntervalMeasure) (η : ℝ → 𝕜)
    (hη : StronglyMeasurable η) (hb : ∀ x, ‖η x‖ ≤ 1)
    (g : Lp 𝕜 1 unitIntervalMeasure) :
    innerSliceOperator T f η hη hb g =
      weightedOuterReader η hη hb (T (tensorWith g f)) := rfl

theorem norm_innerSliceOperator_le (T : MixedNorm 𝕜 p →L[𝕜] MixedNorm 𝕜 p)
    (f : Lp 𝕜 p unitIntervalMeasure) (η : ℝ → 𝕜)
    (hη : StronglyMeasurable η) (hb : ∀ x, ‖η x‖ ≤ 1) :
    ‖innerSliceOperator T f η hη hb‖ ≤ ‖T‖ * ‖f‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  intro g
  rw [innerSliceOperator_apply]
  calc
    _ ≤ ‖T (tensorWith g f)‖ :=
      contraction_apply_bound (𝕜 := 𝕜) (X := MixedNorm 𝕜 p)
        (Y := Lp 𝕜 1 unitIntervalMeasure)
        (weightedOuterReader (𝕜 := 𝕜) (p := p)
          (E := Lp 𝕜 1 unitIntervalMeasure) η hη hb)
        (norm_weightedOuterReader_le (𝕜 := 𝕜) (p := p)
          (E := Lp 𝕜 1 unitIntervalMeasure) η hη hb) (T (tensorWith g f))
    _ ≤ ‖T‖ * ‖tensorWith g f‖ := T.le_opNorm _
    _ = (‖T‖ * ‖f‖) * ‖g‖ := by rw [norm_tensorWith 𝕜 p]; ring

def meanZeroInnerSlice (T : MixedNorm 𝕜 p →L[𝕜] MixedNorm 𝕜 p)
    (f : Lp 𝕜 p unitIntervalMeasure) (η : ℝ → 𝕜)
    (hη : StronglyMeasurable η) (hb : ∀ x, ‖η x‖ ≤ 1) :
    MeanZeroL1 𝕜 →L[𝕜] MeanZeroL1 𝕜 :=
  (intervalLpMeanZeroProjection 𝕜 ⟨1, le_rfl⟩).comp
    ((innerSliceOperator T f η hη hb).comp
      (intervalLpMeanZeroSubmodule 𝕜 ⟨1, le_rfl⟩).subtypeL)

theorem norm_meanZeroInnerSlice_le (T : MixedNorm 𝕜 p →L[𝕜] MixedNorm 𝕜 p)
    (f : Lp 𝕜 p unitIntervalMeasure) (η : ℝ → 𝕜)
    (hη : StronglyMeasurable η) (hb : ∀ x, ‖η x‖ ≤ 1) :
    ‖meanZeroInnerSlice T f η hη hb‖ ≤ 2 * ‖T‖ * ‖f‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro g
  change ‖intervalLpMeanZeroProjection 𝕜 ⟨1, le_rfl⟩
    (innerSliceOperator T f η hη hb g.val)‖ ≤ _
  calc
    _ ≤ 2 * ‖innerSliceOperator T f η hη hb g.val‖ :=
      meanZeroProjection_norm_le 𝕜 _
    _ ≤ 2 * (‖innerSliceOperator T f η hη hb‖ * ‖g.val‖) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (by norm_num)
    _ ≤ 2 * ((‖T‖ * ‖f‖) * ‖g‖) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (norm_innerSliceOperator_le T f η hη hb)
          (norm_nonneg g)) (by norm_num)
    _ = _ := by ring

end SurveyStatements.P5OperatorReduction

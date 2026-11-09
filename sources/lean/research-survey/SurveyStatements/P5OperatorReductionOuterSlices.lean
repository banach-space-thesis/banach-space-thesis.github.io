import SurveyStatements.P5OperatorReductionRegisteredTraces
import SurveyStatements.P5HaarNorm

/-! Actual outer operators determined by arbitrary inner input vectors
and bounded inner readers. Every possible pair of finite inner splits has
a simultaneous dyadic trace along one fixed outer reservoir. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal Classical
namespace SurveyStatements.P5OperatorReduction
open SurveyStatements.P5 SurveyStatements.P5Support
variable {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

def outerSliceOperator (T : MixedNorm 𝕜 p →L[𝕜] MixedNorm 𝕜 p)
    (g : Lp 𝕜 1 unitIntervalMeasure)
    (φ : Lp 𝕜 1 unitIntervalMeasure →L[𝕜] 𝕜) :
    Lp 𝕜 p unitIntervalMeasure →L[𝕜] Lp 𝕜 p unitIntervalMeasure :=
  (φ.compLpL p unitIntervalMeasure).comp (T.comp (tensorWith g))

theorem outerSliceOperator_apply (T : MixedNorm 𝕜 p →L[𝕜] MixedNorm 𝕜 p)
    (g : Lp 𝕜 1 unitIntervalMeasure)
    (φ : Lp 𝕜 1 unitIntervalMeasure →L[𝕜] 𝕜)
    (f : Lp 𝕜 p unitIntervalMeasure) :
    outerSliceOperator T g φ f = φ.compLpL p unitIntervalMeasure (T (tensorWith g f)) := rfl

theorem norm_outerSliceOperator_le (T : MixedNorm 𝕜 p →L[𝕜] MixedNorm 𝕜 p)
    (g : Lp 𝕜 1 unitIntervalMeasure)
    (φ : Lp 𝕜 1 unitIntervalMeasure →L[𝕜] 𝕜) :
    ‖outerSliceOperator T g φ‖ ≤ ‖φ‖ * ‖T‖ * ‖g‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro f
  rw [outerSliceOperator_apply]
  calc
    _ ≤ ‖φ.compLpL p unitIntervalMeasure‖ * ‖T (tensorWith g f)‖ :=
      (φ.compLpL p unitIntervalMeasure).le_opNorm (T (tensorWith g f))
    _ ≤ ‖φ‖ * ‖T (tensorWith g f)‖ := mul_le_mul_of_nonneg_right
      (ContinuousLinearMap.norm_compLpL_le (p := p) (μ := unitIntervalMeasure) φ)
      (norm_nonneg _)
    _ ≤ ‖φ‖ * (‖T‖ * ‖tensorWith g f‖) :=
      mul_le_mul_of_nonneg_left (T.le_opNorm _) (norm_nonneg _)
    _ = (‖φ‖ * ‖T‖ * ‖g‖) * ‖f‖ := by rw [norm_tensorWith 𝕜 p]; ring

abbrev innerSplitExponent : BanachExponent := ⟨1, le_rfl⟩

def innerPairOuterSlice (p : BanachExponent)
    (T : MixedNorm 𝕜 p.val →L[𝕜] MixedNorm 𝕜 p.val)
    (pair : LpHaarFiniteSplit × LpHaarFiniteSplit) :
    IntervalLp 𝕜 p →L[𝕜] IntervalLp 𝕜 p :=
  outerSliceOperator T (pair.2.vector 𝕜 innerSplitExponent)
    (pair.1.reader 𝕜 innerSplitExponent)

theorem exists_universal_inner_pair_traces (p : BanachExponent) (hp : p.val ≠ ∞)
    (T : MixedNorm 𝕜 p.val →L[𝕜] MixedNorm 𝕜 p.val) :
    ∃ r : ℕ → ℕ, StrictMono r ∧
      Nonempty (∀ pair : LpHaarFiniteSplit × LpHaarFiniteSplit,
        RegisteredDyadicTrace
          (fun n k => lpHaarDyadicCoefficient 𝕜 p n k
            (innerPairOuterSlice p T pair (lpHaarDyadic 𝕜 p n k)))
          r (6 * ‖innerPairOuterSlice p T pair‖)) :=
  exists_universal_operator_trace_reservoir p hp (innerPairOuterSlice p T)

end SurveyStatements.P5OperatorReduction

import SurveyStatements.P5GeneralMixedErrorCancellativeStrips

/-! Summable outer and inner strip errors. Each summand is the actual strip
operator, and its full canonical normalization factor occurs in the budget. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
open MeasureTheory
open scoped ENNReal Classical

namespace SurveyStatements.P5
attribute [local irreducible] probabilityLpIntegral probabilityLpMean
  outerExpectation innerExpectation DoublyZeroMean
open P5Support
variable {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

def generalMixedOuterStripSeries {ι : Type*}
    (S : ι → Lp 𝕜 p unitIntervalMeasure →L[𝕜] Lp 𝕜 p unitIntervalMeasure)
    (target source : ι → DyadicIndex) :
    DoublyZeroMean 𝕜 p →L[𝕜] DoublyZeroMean 𝕜 p :=
  ∑' i, generalMixedOuterStrip (S i) (target i) (source i)

def generalMixedInnerStripSeries {ι : Type*}
    (N : ι → Lp 𝕜 1 unitIntervalMeasure →L[𝕜] Lp 𝕜 1 unitIntervalMeasure)
    (target source : ι → DyadicIndex) :
    DoublyZeroMean 𝕜 p →L[𝕜] DoublyZeroMean 𝕜 p :=
  ∑' i, generalMixedInnerStrip (p := p) (N i) (target i) (source i)

theorem generalMixedOuterStripSeries_summable {ι : Type*}
    (S : ι → Lp 𝕜 p unitIntervalMeasure →L[𝕜] Lp 𝕜 p unitIntervalMeasure)
    (target source : ι → DyadicIndex) (b : ι → ℝ) (hb : Summable b)
    (hbudget : ∀ i, 4 * (‖dyadicHaar 𝕜 1 (target i)‖ *
      (‖S i‖ * ‖dyadicHaarCoordinate 𝕜 1 (source i)‖)) ≤ b i) :
    Summable (fun i => generalMixedOuterStrip (S i) (target i) (source i)) := by
  letI : NormedSpace 𝕜 (DoublyZeroMean 𝕜 p) := inferInstance
  exact summable_operators_of_norm_bound
    (fun i => generalMixedOuterStrip (𝕜 := 𝕜) (p := p) (S i) (target i) (source i))
    b hb (fun i => (norm_generalMixedOuterStrip_le (𝕜 := 𝕜) (p := p)
      (S i) (target i) (source i)).trans (hbudget i))

theorem generalMixedInnerStripSeries_summable {ι : Type*}
    (N : ι → Lp 𝕜 1 unitIntervalMeasure →L[𝕜] Lp 𝕜 1 unitIntervalMeasure)
    (target source : ι → DyadicIndex) (b : ι → ℝ) (hb : Summable b)
    (hbudget : ∀ i, 4 * (‖dyadicHaar 𝕜 p (target i)‖ *
      (‖N i‖ * (intervalLpDyadicRadius (source i).1)⁻¹)) ≤ b i) :
    Summable (fun i => generalMixedInnerStrip (p := p) (N i) (target i) (source i)) := by
  letI : NormedSpace 𝕜 (DoublyZeroMean 𝕜 p) := inferInstance
  exact summable_operators_of_norm_bound
    (fun i => generalMixedInnerStrip (𝕜 := 𝕜) (p := p) (N i) (target i) (source i))
    b hb (fun i => (norm_generalMixedInnerStrip_le (𝕜 := 𝕜) (p := p)
      (N i) (target i) (source i)).trans (hbudget i))

theorem norm_generalMixedOuterStripSeries_le {ι : Type*}
    (S : ι → Lp 𝕜 p unitIntervalMeasure →L[𝕜] Lp 𝕜 p unitIntervalMeasure)
    (target source : ι → DyadicIndex) (b : ι → ℝ) (hb : Summable b)
    (hbudget : ∀ i, 4 * (‖dyadicHaar 𝕜 1 (target i)‖ *
      (‖S i‖ * ‖dyadicHaarCoordinate 𝕜 1 (source i)‖)) ≤ b i) :
    ‖generalMixedOuterStripSeries S target source‖ ≤ ∑' i, b i :=
  norm_operator_tsum_le _ b hb
    (fun i => (norm_generalMixedOuterStrip_le _ _ _).trans (hbudget i))

theorem norm_generalMixedInnerStripSeries_le {ι : Type*}
    (N : ι → Lp 𝕜 1 unitIntervalMeasure →L[𝕜] Lp 𝕜 1 unitIntervalMeasure)
    (target source : ι → DyadicIndex) (b : ι → ℝ) (hb : Summable b)
    (hbudget : ∀ i, 4 * (‖dyadicHaar 𝕜 p (target i)‖ *
      (‖N i‖ * (intervalLpDyadicRadius (source i).1)⁻¹)) ≤ b i) :
    ‖generalMixedInnerStripSeries (p := p) N target source‖ ≤ ∑' i, b i :=
  norm_operator_tsum_le _ b hb
    (fun i => (norm_generalMixedInnerStrip_le _ _ _).trans (hbudget i))

theorem generalMixedOuterStripSeries_haar {ι : Type*} (hp : p ≠ ∞)
    (S : ι → Lp 𝕜 p unitIntervalMeasure →L[𝕜] Lp 𝕜 p unitIntervalMeasure)
    (target source : ι → DyadicIndex) (d : ι → DyadicIndex → 𝕜)
    (hS : ∀ i I, S i (dyadicHaar 𝕜 p I) = d i I • dyadicHaar 𝕜 p I)
    (b : ι → ℝ) (hb : Summable b)
    (hbudget : ∀ i, 4 * (‖dyadicHaar 𝕜 1 (target i)‖ *
      (‖S i‖ * ‖dyadicHaarCoordinate 𝕜 1 (source i)‖)) ≤ b i)
    (I R : DyadicIndex) :
    generalMixedOuterStripSeries S target source (cancellativeHaar 𝕜 p I R) =
      ∑' i, if source i = R then d i I • cancellativeHaar 𝕜 p I (target i) else 0 := by
  calc
    _ = ∑' i, generalMixedOuterStrip (S i) (target i) (source i)
        (cancellativeHaar 𝕜 p I R) :=
      (ContinuousLinearMap.apply 𝕜 (DoublyZeroMean 𝕜 p)
        (cancellativeHaar 𝕜 p I R)).map_tsum
        (generalMixedOuterStripSeries_summable S target source b hb hbudget)
    _ = _ := tsum_congr (fun i =>
      generalMixedOuterStrip_haar hp (S i) (d i) (hS i) _ _ _ _)

theorem generalMixedInnerStripSeries_haar {ι : Type*} (hp : p ≠ ∞)
    (N : ι → Lp 𝕜 1 unitIntervalMeasure →L[𝕜] Lp 𝕜 1 unitIntervalMeasure)
    (target source : ι → DyadicIndex) (e : ι → DyadicIndex → 𝕜)
    (hN : ∀ i J, N i (dyadicHaar 𝕜 1 J) = e i J • dyadicHaar 𝕜 1 J)
    (b : ι → ℝ) (hb : Summable b)
    (hbudget : ∀ i, 4 * (‖dyadicHaar 𝕜 p (target i)‖ *
      (‖N i‖ * (intervalLpDyadicRadius (source i).1)⁻¹)) ≤ b i)
    (L J : DyadicIndex) :
    generalMixedInnerStripSeries (p := p) N target source (cancellativeHaar 𝕜 p L J) =
      ∑' i, if source i = L then e i J • cancellativeHaar 𝕜 p (target i) J else 0 := by
  calc
    _ = ∑' i, generalMixedInnerStrip (p := p) (N i) (target i) (source i)
        (cancellativeHaar 𝕜 p L J) :=
      (ContinuousLinearMap.apply 𝕜 (DoublyZeroMean 𝕜 p)
        (cancellativeHaar 𝕜 p L J)).map_tsum
        (generalMixedInnerStripSeries_summable N target source b hb hbudget)
    _ = _ := tsum_congr (fun i =>
      generalMixedInnerStrip_haar hp (N i) (e i) (hN i) _ _ _ _)

end SurveyStatements.P5

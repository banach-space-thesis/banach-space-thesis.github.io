import SurveyStatements.P5GeneralMixedErrorStripSeries

/-! Exact product-Haar matrices of the actual summable one-coordinate strip
errors, obtained by applying continuous coordinates to the operator series. -/

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

theorem generalMixedOuterStripSeries_coordinate {ι : Type*} (hp : p ≠ ∞)
    (S : ι → Lp 𝕜 p unitIntervalMeasure →L[𝕜] Lp 𝕜 p unitIntervalMeasure)
    (target source : ι → DyadicIndex) (d : ι → DyadicIndex → 𝕜)
    (hS : ∀ i I, S i (dyadicHaar 𝕜 p I) = d i I • dyadicHaar 𝕜 p I)
    (b : ι → ℝ) (hb : Summable b)
    (hbudget : ∀ i, 4 * (‖dyadicHaar 𝕜 1 (target i)‖ *
      (‖S i‖ * ‖dyadicHaarCoordinate 𝕜 1 (source i)‖)) ≤ b i)
    (A B I R : DyadicIndex) :
    cancellativeHaarCoordinate 𝕜 p A B
      (generalMixedOuterStripSeries S target source (cancellativeHaar 𝕜 p I R)) =
      ∑' i, if source i = R then d i I *
        (if (A, B) = (I, target i) then 1 else 0) else 0 := by
  let ops := fun i => generalMixedOuterStrip (S i) (target i) (source i)
  have hops : Summable ops := generalMixedOuterStripSeries_summable
    S target source b hb hbudget
  have hvalues := (ContinuousLinearMap.apply 𝕜 (DoublyZeroMean 𝕜 p)
    (cancellativeHaar 𝕜 p I R)).summable hops
  change cancellativeHaarCoordinate 𝕜 p A B
    ((∑' i, ops i) (cancellativeHaar 𝕜 p I R)) = _
  have hsum : cancellativeHaarCoordinate 𝕜 p A B
      ((∑' i, ops i) (cancellativeHaar 𝕜 p I R)) =
      ∑' i, cancellativeHaarCoordinate 𝕜 p A B
        (ops i (cancellativeHaar 𝕜 p I R)) := by
    calc
      _ = cancellativeHaarCoordinate 𝕜 p A B
          (∑' i, ops i (cancellativeHaar 𝕜 p I R)) :=
        congrArg (cancellativeHaarCoordinate 𝕜 p A B)
          ((ContinuousLinearMap.apply 𝕜 (DoublyZeroMean 𝕜 p)
            (cancellativeHaar 𝕜 p I R)).map_tsum hops)
      _ = _ := (cancellativeHaarCoordinate 𝕜 p A B).map_tsum hvalues
  rw [hsum]
  apply tsum_congr
  intro i
  rw [generalMixedOuterStrip_haar hp (S i) (d i) (hS i)]
  by_cases hs : source i = R
  · rw [if_pos hs, if_pos hs, map_smul,
      cancellativeHaarCoordinate_biorthogonal 𝕜 p hp]
    rfl
  · rw [if_neg hs, if_neg hs, map_zero]

theorem generalMixedInnerStripSeries_coordinate {ι : Type*} (hp : p ≠ ∞)
    (N : ι → Lp 𝕜 1 unitIntervalMeasure →L[𝕜] Lp 𝕜 1 unitIntervalMeasure)
    (target source : ι → DyadicIndex) (e : ι → DyadicIndex → 𝕜)
    (hN : ∀ i J, N i (dyadicHaar 𝕜 1 J) = e i J • dyadicHaar 𝕜 1 J)
    (b : ι → ℝ) (hb : Summable b)
    (hbudget : ∀ i, 4 * (‖dyadicHaar 𝕜 p (target i)‖ *
      (‖N i‖ * (intervalLpDyadicRadius (source i).1)⁻¹)) ≤ b i)
    (A B L J : DyadicIndex) :
    cancellativeHaarCoordinate 𝕜 p A B
      (generalMixedInnerStripSeries (p := p) N target source (cancellativeHaar 𝕜 p L J)) =
      ∑' i, if source i = L then e i J *
        (if (A, B) = (target i, J) then 1 else 0) else 0 := by
  let ops := fun i => generalMixedInnerStrip (p := p) (N i) (target i) (source i)
  have hops : Summable ops := generalMixedInnerStripSeries_summable
    N target source b hb hbudget
  have hvalues := (ContinuousLinearMap.apply 𝕜 (DoublyZeroMean 𝕜 p)
    (cancellativeHaar 𝕜 p L J)).summable hops
  change cancellativeHaarCoordinate 𝕜 p A B
    ((∑' i, ops i) (cancellativeHaar 𝕜 p L J)) = _
  have hsum : cancellativeHaarCoordinate 𝕜 p A B
      ((∑' i, ops i) (cancellativeHaar 𝕜 p L J)) =
      ∑' i, cancellativeHaarCoordinate 𝕜 p A B
        (ops i (cancellativeHaar 𝕜 p L J)) := by
    calc
      _ = cancellativeHaarCoordinate 𝕜 p A B
          (∑' i, ops i (cancellativeHaar 𝕜 p L J)) :=
        congrArg (cancellativeHaarCoordinate 𝕜 p A B)
          ((ContinuousLinearMap.apply 𝕜 (DoublyZeroMean 𝕜 p)
            (cancellativeHaar 𝕜 p L J)).map_tsum hops)
      _ = _ := (cancellativeHaarCoordinate 𝕜 p A B).map_tsum hvalues
  rw [hsum]
  apply tsum_congr
  intro i
  rw [generalMixedInnerStrip_haar hp (N i) (e i) (hN i)]
  by_cases hs : source i = L
  · rw [if_pos hs, if_pos hs, map_smul,
      cancellativeHaarCoordinate_biorthogonal 𝕜 p hp]
    rfl
  · rw [if_neg hs, if_neg hs, map_zero]

end SurveyStatements.P5

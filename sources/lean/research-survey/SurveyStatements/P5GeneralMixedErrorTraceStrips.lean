import SurveyStatements.P5GeneralMixedErrorStripCoordinates
import SurveyStatements.P5OperatorReductionTraceBalancedMultipliers

/-! Genuine balanced trace data construct the one-coordinate error series.
The budgets include the actual Haar norms, coordinate norms, and the
doubly-zero-mean projection factor. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
open MeasureTheory
open scoped ENNReal Classical

namespace SurveyStatements.P5
attribute [local irreducible] probabilityLpIntegral probabilityLpMean
  outerExpectation innerExpectation DoublyZeroMean
open P5Support P5OperatorReduction
variable {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem exists_generalMixed_scalar_trace_multiplier (hp : p ≠ ∞)
    (g t : ℕ → 𝕜) {δ : ℝ} (hδ : 0 ≤ δ)
    (hg : ∀ j, ‖g j - t j‖ ≤ lpHaarTraceErrorBudget δ j)
    (ht : ∀ j, j ≠ 0 → ‖t j - t ((j - 1) / 2)‖ ≤
      lpHaarTraceErrorBudget δ ((j - 1) / 2))
    (hroot : ‖t 0‖ ≤ δ) :
    ∃ Q : Lp 𝕜 p unitIntervalMeasure →L[𝕜] Lp 𝕜 p unitIntervalMeasure,
      ‖Q‖ ≤ 14 * δ ∧ ∀ I : DyadicIndex,
        Q (dyadicHaar 𝕜 p I) =
          g (lpHaarHeapIndex I.1 I.2) • dyadicHaar 𝕜 p I := by
  obtain ⟨Q, hnorm, hhaar, _⟩ :=
    exists_small_geometric_trace_multiplier ⟨p, Fact.out⟩ hp g t hδ hg ht hroot
  refine ⟨Q, hnorm, ?_⟩
  intro I
  simpa only [dyadicHaar_eq_support] using hhaar I.1 I.2

theorem exists_generalMixedOuterTraceStripSeries {ι : Type*} (hp : p ≠ ∞)
    (g t : ι → ℕ → 𝕜) (δ : ι → ℝ) (hδ : ∀ i, 0 ≤ δ i)
    (hg : ∀ i j, ‖g i j - t i j‖ ≤ lpHaarTraceErrorBudget (δ i) j)
    (ht : ∀ i j, j ≠ 0 → ‖t i j - t i ((j - 1) / 2)‖ ≤
      lpHaarTraceErrorBudget (δ i) ((j - 1) / 2))
    (hroot : ∀ i, ‖t i 0‖ ≤ δ i)
    (target source : ι → DyadicIndex) (b : ι → ℝ) (hb : Summable b)
    (hbudget : ∀ i, 4 * (‖dyadicHaar 𝕜 1 (target i)‖ *
      ((14 * δ i) * ‖dyadicHaarCoordinate 𝕜 1 (source i)‖)) ≤ b i) :
    ∃ E : DoublyZeroMean 𝕜 p →L[𝕜] DoublyZeroMean 𝕜 p,
      ‖E‖ ≤ ∑' i, b i ∧ ∀ A B I R : DyadicIndex,
        cancellativeHaarCoordinate 𝕜 p A B (E (cancellativeHaar 𝕜 p I R)) =
          ∑' i, if source i = R then g i (lpHaarHeapIndex I.1 I.2) *
            (if (A, B) = (I, target i) then 1 else 0) else 0 := by
  letI : NormedSpace 𝕜 (DoublyZeroMean 𝕜 p) := inferInstance
  have hQ : ∀ i, ∃ Q : Lp 𝕜 p unitIntervalMeasure →L[𝕜] Lp 𝕜 p unitIntervalMeasure,
      ‖Q‖ ≤ 14 * δ i ∧ ∀ I : DyadicIndex,
        Q (dyadicHaar 𝕜 p I) = g i (lpHaarHeapIndex I.1 I.2) • dyadicHaar 𝕜 p I :=
    fun i => exists_generalMixed_scalar_trace_multiplier (𝕜 := 𝕜) (p := p)
      hp (g i) (t i)
      (hδ i) (hg i) (ht i) (hroot i)
  choose S hSn hSh using hQ
  have hactual : ∀ i, 4 * (‖dyadicHaar 𝕜 1 (target i)‖ *
      (‖S i‖ * ‖dyadicHaarCoordinate 𝕜 1 (source i)‖)) ≤ b i := by
    intro i
    apply LE.le.trans _ (hbudget i)
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 4)
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact mul_le_mul_of_nonneg_right (hSn i) (norm_nonneg _)
  refine ⟨generalMixedOuterStripSeries S target source,
    norm_generalMixedOuterStripSeries_le S target source b hb hactual, ?_⟩
  exact generalMixedOuterStripSeries_coordinate hp S target source
    (fun i I => g i (lpHaarHeapIndex I.1 I.2)) hSh b hb hactual

theorem exists_generalMixedInnerTraceStripSeries {ι : Type*} (hp : p ≠ ∞)
    (g t : ι → ℕ → 𝕜) (δ : ι → ℝ) (hδ : ∀ i, 0 ≤ δ i)
    (hg : ∀ i j, ‖g i j - t i j‖ ≤ lpHaarTraceErrorBudget (δ i) j)
    (ht : ∀ i j, j ≠ 0 → ‖t i j - t i ((j - 1) / 2)‖ ≤
      lpHaarTraceErrorBudget (δ i) ((j - 1) / 2))
    (hroot : ∀ i, ‖t i 0‖ ≤ δ i)
    (target source : ι → DyadicIndex) (b : ι → ℝ) (hb : Summable b)
    (hbudget : ∀ i, 4 * (‖dyadicHaar 𝕜 p (target i)‖ *
      ((14 * δ i) * (intervalLpDyadicRadius (source i).1)⁻¹)) ≤ b i) :
    ∃ E : DoublyZeroMean 𝕜 p →L[𝕜] DoublyZeroMean 𝕜 p,
      ‖E‖ ≤ ∑' i, b i ∧ ∀ A B L J : DyadicIndex,
        cancellativeHaarCoordinate 𝕜 p A B (E (cancellativeHaar 𝕜 p L J)) =
          ∑' i, if source i = L then g i (lpHaarHeapIndex J.1 J.2) *
            (if (A, B) = (target i, J) then 1 else 0) else 0 := by
  letI : NormedSpace 𝕜 (DoublyZeroMean 𝕜 p) := inferInstance
  have hQ : ∀ i, ∃ Q : Lp 𝕜 1 unitIntervalMeasure →L[𝕜] Lp 𝕜 1 unitIntervalMeasure,
      ‖Q‖ ≤ 14 * δ i ∧ ∀ J : DyadicIndex,
        Q (dyadicHaar 𝕜 1 J) = g i (lpHaarHeapIndex J.1 J.2) • dyadicHaar 𝕜 1 J :=
    fun i => exists_generalMixed_scalar_trace_multiplier (𝕜 := 𝕜) (p := 1) (by simp)
      (g i) (t i) (hδ i) (hg i) (ht i) (hroot i)
  choose N hNn hNh using hQ
  have hactual : ∀ i, 4 * (‖dyadicHaar 𝕜 p (target i)‖ *
      (‖N i‖ * (intervalLpDyadicRadius (source i).1)⁻¹)) ≤ b i := by
    intro i
    apply LE.le.trans _ (hbudget i)
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 4)
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact mul_le_mul_of_nonneg_right (hNn i)
      (inv_nonneg.mpr (intervalLpDyadicRadius_pos (source i).1).le)
  refine ⟨generalMixedInnerStripSeries (p := p) N target source,
    norm_generalMixedInnerStripSeries_le N target source b hb hactual, ?_⟩
  exact generalMixedInnerStripSeries_coordinate hp N target source
    (fun i J => g i (lpHaarHeapIndex J.1 J.2)) hNh b hb hactual

end SurveyStatements.P5

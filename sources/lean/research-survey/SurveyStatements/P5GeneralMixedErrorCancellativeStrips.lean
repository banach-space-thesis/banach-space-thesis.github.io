import SurveyStatements.P5GeneralMixedErrorStrips

/-! The genuine one-coordinate strip maps restricted through the fixed
cancellative projection. This harmless projection contributes its actual
norm bound four to the construction budgets. -/

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

def generalMixedProjectedOperator (U : MixedNorm 𝕜 p →L[𝕜] MixedNorm 𝕜 p) :
    DoublyZeroMean 𝕜 p →L[𝕜] DoublyZeroMean 𝕜 p :=
  (cancellativeProjection 𝕜 p).comp (U.comp (DoublyZeroMean 𝕜 p).subtypeL)

theorem generalMixed_projection_fixes (x : DoublyZeroMean 𝕜 p) :
    cancellativeProjection 𝕜 p x.val = x :=
  congrArg (fun L : DoublyZeroMean 𝕜 p →L[𝕜] DoublyZeroMean 𝕜 p => L x)
    (cancellativeProjection_retraction 𝕜 p)

theorem norm_generalMixedProjectedOperator_le (U : MixedNorm 𝕜 p →L[𝕜] MixedNorm 𝕜 p) :
    ‖generalMixedProjectedOperator U‖ ≤ 4 * ‖U‖ := by
  letI : NormedSpace 𝕜 (DoublyZeroMean 𝕜 p) := inferInstance
  have hU : ‖U.comp (DoublyZeroMean 𝕜 p).subtypeL‖ ≤ ‖U‖ :=
    (ContinuousLinearMap.opNorm_comp_le U (DoublyZeroMean 𝕜 p).subtypeL).trans
      ((mul_le_mul_of_nonneg_left (Submodule.norm_subtypeL_le _) (norm_nonneg U)).trans
        (by simp))
  exact (ContinuousLinearMap.opNorm_comp_le (cancellativeProjection 𝕜 p)
    (U.comp (DoublyZeroMean 𝕜 p).subtypeL)).trans
    (mul_le_mul (norm_cancellativeProjection_le 𝕜 p) hU
      (ContinuousLinearMap.opNorm_nonneg (U.comp (DoublyZeroMean 𝕜 p).subtypeL))
      (by norm_num))

def generalMixedOuterStrip
    (S : Lp 𝕜 p unitIntervalMeasure →L[𝕜] Lp 𝕜 p unitIntervalMeasure)
    (J L : DyadicIndex) : DoublyZeroMean 𝕜 p →L[𝕜] DoublyZeroMean 𝕜 p :=
  generalMixedProjectedOperator (generalMixedRawOuterStrip S J L)

def generalMixedInnerStrip
    (N : Lp 𝕜 1 unitIntervalMeasure →L[𝕜] Lp 𝕜 1 unitIntervalMeasure)
    (I K : DyadicIndex) : DoublyZeroMean 𝕜 p →L[𝕜] DoublyZeroMean 𝕜 p :=
  generalMixedProjectedOperator (generalMixedRawInnerStrip (p := p) N I K)

theorem norm_generalMixedOuterStrip_le
    (S : Lp 𝕜 p unitIntervalMeasure →L[𝕜] Lp 𝕜 p unitIntervalMeasure)
    (J L : DyadicIndex) :
    ‖generalMixedOuterStrip S J L‖ ≤
      4 * (‖dyadicHaar 𝕜 1 J‖ * (‖S‖ * ‖dyadicHaarCoordinate 𝕜 1 L‖)) :=
  (norm_generalMixedProjectedOperator_le _).trans
    (mul_le_mul_of_nonneg_left (norm_generalMixedRawOuterStrip_le S J L) (by norm_num))

theorem norm_generalMixedInnerStrip_le
    (N : Lp 𝕜 1 unitIntervalMeasure →L[𝕜] Lp 𝕜 1 unitIntervalMeasure)
    (I K : DyadicIndex) :
    ‖generalMixedInnerStrip (p := p) N I K‖ ≤
      4 * (‖dyadicHaar 𝕜 p I‖ * (‖N‖ * (intervalLpDyadicRadius K.1)⁻¹)) :=
  (norm_generalMixedProjectedOperator_le _).trans
    (mul_le_mul_of_nonneg_left (norm_generalMixedRawInnerStrip_le N I K) (by norm_num))

theorem generalMixedOuterStrip_haar (hp : p ≠ ∞)
    (S : Lp 𝕜 p unitIntervalMeasure →L[𝕜] Lp 𝕜 p unitIntervalMeasure)
    (d : DyadicIndex → 𝕜) (hS : ∀ I, S (dyadicHaar 𝕜 p I) = d I • dyadicHaar 𝕜 p I)
    (J L I R : DyadicIndex) :
    generalMixedOuterStrip S J L (cancellativeHaar 𝕜 p I R) =
      if L = R then d I • cancellativeHaar 𝕜 p I J else 0 := by
  change cancellativeProjection 𝕜 p
    (generalMixedRawOuterStrip S J L (productHaar 𝕜 p I R)) = _
  rw [generalMixedRawOuterStrip_haar hp S d hS]
  by_cases h : L = R
  · rw [if_pos h, if_pos h, map_smul]
    exact congrArg (fun z : DoublyZeroMean 𝕜 p => d I • z)
      (generalMixed_projection_fixes (cancellativeHaar 𝕜 p I J))
  · simp [h]

theorem generalMixedInnerStrip_haar (hp : p ≠ ∞)
    (N : Lp 𝕜 1 unitIntervalMeasure →L[𝕜] Lp 𝕜 1 unitIntervalMeasure)
    (e : DyadicIndex → 𝕜) (hN : ∀ J, N (dyadicHaar 𝕜 1 J) = e J • dyadicHaar 𝕜 1 J)
    (I K L J : DyadicIndex) :
    generalMixedInnerStrip (p := p) N I K (cancellativeHaar 𝕜 p L J) =
      if K = L then e J • cancellativeHaar 𝕜 p I J else 0 := by
  change cancellativeProjection 𝕜 p
    (generalMixedRawInnerStrip (p := p) N I K (productHaar 𝕜 p L J)) = _
  rw [generalMixedRawInnerStrip_haar hp N e hN]
  by_cases h : K = L
  · rw [if_pos h, if_pos h, map_smul]
    exact congrArg (fun z : DoublyZeroMean 𝕜 p => e J • z)
      (generalMixed_projection_fixes (cancellativeHaar 𝕜 p I J))
  · simp [h]

end SurveyStatements.P5

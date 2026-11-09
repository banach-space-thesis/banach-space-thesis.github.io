import SurveyStatements.P5GeneralMixedErrorOperators
import SurveyStatements.P5OperatorReductionShadowExpansionMasks
import SurveyStatements.P5OperatorReductionReaderAlgebra
import SurveyStatements.P5TensorBilinearity

/-! Actual one-coordinate strip maps. The norm estimates retain the Haar
normalization factors and are valid for arbitrary bounded one-variable maps. -/

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

def generalMixedOuterHaarReader (I : DyadicIndex) :
    MixedNorm 𝕜 p →L[𝕜] Lp 𝕜 1 unitIntervalMeasure :=
  (intervalLpDyadicRadius I.1 : 𝕜)⁻¹ •
    weightedOuterReader (𝕜 := 𝕜) (E := Lp 𝕜 1 unitIntervalMeasure) (p := p)
      (haarPacketWeight I.1 I.2)
      (haarPacketWeight_stronglyMeasurable I.1 I.2) (haarPacketWeight_norm_le I.1 I.2)

theorem generalMixed_scalar_outer_weight (I : DyadicIndex)
    (f : Lp 𝕜 p unitIntervalMeasure) :
    weightedOuterReader (𝕜 := 𝕜) (E := 𝕜) (p := p) (haarPacketWeight I.1 I.2)
        (haarPacketWeight_stronglyMeasurable I.1 I.2) (haarPacketWeight_norm_le I.1 I.2) f =
      (intervalLpDyadicRadius I.1 : 𝕜) * dyadicHaarCoordinate 𝕜 p I f := by
  have hm : unitIntervalMeasure.real
      (lpHaarCell (I.1 + 1) (2 * I.2.val) ∪ lpHaarCell (I.1 + 1) (2 * I.2.val + 1)) =
      intervalLpDyadicRadius I.1 := by
    rw [lpHaarCell_children, measureReal_def, unitIntervalMeasure,
      lpHaarCell_measure I.1 I.2 I.2.isLt,
      ENNReal.toReal_ofReal (intervalLpDyadicRadius_pos I.1).le]
  have hn : (intervalLpDyadicRadius I.1 : 𝕜) ≠ 0 :=
    RCLike.ofReal_ne_zero.mpr (intervalLpDyadicRadius_pos I.1).ne'
  have hc := lpHaarCoefficient_apply (𝕜 := 𝕜) (p := p)
    (μ := unitIntervalMeasure)
    (lpHaarCell (I.1 + 1) (2 * I.2.val))
    (lpHaarCell (I.1 + 1) (2 * I.2.val + 1))
    measurableSet_Ioc measurableSet_Ioc
    (lpHaarCell_disjoint_sameLevel (I.1 + 1) (by omega)) f
  rw [hm] at hc
  rw [weightedOuterReader_apply, dyadicHaarCoordinate_eq_support]
  calc
    _ = (intervalLpDyadicRadius I.1 : 𝕜) *
        ((intervalLpDyadicRadius I.1 : 𝕜)⁻¹ *
          ∫ x, haarPacketWeight I.1 I.2 x * f x ∂unitIntervalMeasure) := by
      simp only [smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hn, one_mul]
      change (@integral ℝ 𝕜 _ (NormedSpace.restrictScalars ℝ 𝕜 𝕜)
        _ unitIntervalMeasure (fun x => haarPacketWeight I.1 I.2 x * f x)) = _
      rw [NormedSpace.restrictScalars_eq]
    _ = _ := congrArg (fun c : 𝕜 => (intervalLpDyadicRadius I.1 : 𝕜) * c) hc.symm

theorem generalMixedOuterHaarReader_tensor (I : DyadicIndex)
    (g : Lp 𝕜 1 unitIntervalMeasure) (f : Lp 𝕜 p unitIntervalMeasure) :
    generalMixedOuterHaarReader (𝕜 := 𝕜) (p := p) I (tensorWith g f) =
      dyadicHaarCoordinate 𝕜 p I f • g := by
  have hn : (intervalLpDyadicRadius I.1 : 𝕜) ≠ 0 :=
    RCLike.ofReal_ne_zero.mpr (intervalLpDyadicRadius_pos I.1).ne'
  rw [generalMixedOuterHaarReader, ContinuousLinearMap.smul_apply,
    weightedOuterReader_tensor, generalMixed_scalar_outer_weight, smul_smul,
    ← mul_assoc, inv_mul_cancel₀ hn, one_mul]

theorem norm_generalMixedOuterHaarReader_le (I : DyadicIndex) :
    ‖generalMixedOuterHaarReader (𝕜 := 𝕜) (p := p) I‖ ≤
      (intervalLpDyadicRadius I.1)⁻¹ := by
  rw [generalMixedOuterHaarReader, norm_smul, norm_inv, RCLike.norm_ofReal,
    abs_of_pos (intervalLpDyadicRadius_pos I.1)]
  exact (mul_le_mul_of_nonneg_left
    (norm_weightedOuterReader_le (𝕜 := 𝕜) (E := Lp 𝕜 1 unitIntervalMeasure)
      (p := p) _ _ _)
    (inv_nonneg.mpr (intervalLpDyadicRadius_pos I.1).le)).trans (by simp)

theorem generalMixed_norm_tensorWith_le (g : Lp 𝕜 1 unitIntervalMeasure) :
    ‖tensorWith (p := p) g‖ ≤ ‖g‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg g)
  intro f
  exact (norm_tensorWith 𝕜 p g f).le

theorem generalMixed_norm_tensorInnerMap_le (f : Lp 𝕜 p unitIntervalMeasure) :
    ‖tensorInnerMap f‖ ≤ ‖f‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg f)
  intro g
  change ‖tensorWith g f‖ ≤ _
  rw [norm_tensorWith]
  exact le_of_eq (mul_comm _ _)

def generalMixedRawOuterStrip
    (S : Lp 𝕜 p unitIntervalMeasure →L[𝕜] Lp 𝕜 p unitIntervalMeasure)
    (J L : DyadicIndex) : MixedNorm 𝕜 p →L[𝕜] MixedNorm 𝕜 p :=
  (tensorWith (p := p) (dyadicHaar 𝕜 1 J)).comp
    (S.comp ((dyadicHaarCoordinate 𝕜 1 L).compLpL p unitIntervalMeasure))

def generalMixedRawInnerStrip
    (N : Lp 𝕜 1 unitIntervalMeasure →L[𝕜] Lp 𝕜 1 unitIntervalMeasure)
    (I K : DyadicIndex) : MixedNorm 𝕜 p →L[𝕜] MixedNorm 𝕜 p :=
  (tensorInnerMap (dyadicHaar 𝕜 p I)).comp
    (N.comp (generalMixedOuterHaarReader (𝕜 := 𝕜) (p := p) K))

theorem norm_generalMixedRawOuterStrip_le
    (S : Lp 𝕜 p unitIntervalMeasure →L[𝕜] Lp 𝕜 p unitIntervalMeasure)
    (J L : DyadicIndex) :
    ‖generalMixedRawOuterStrip S J L‖ ≤
      ‖dyadicHaar 𝕜 1 J‖ * (‖S‖ * ‖dyadicHaarCoordinate 𝕜 1 L‖) := by
  have hinner : ‖S.comp ((dyadicHaarCoordinate 𝕜 1 L).compLpL p unitIntervalMeasure)‖ ≤
      ‖S‖ * ‖dyadicHaarCoordinate 𝕜 1 L‖ :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_compLpL_le _) (norm_nonneg S))
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul (generalMixed_norm_tensorWith_le _) hinner (norm_nonneg _) (norm_nonneg _))

theorem norm_generalMixedRawInnerStrip_le
    (N : Lp 𝕜 1 unitIntervalMeasure →L[𝕜] Lp 𝕜 1 unitIntervalMeasure)
    (I K : DyadicIndex) :
    ‖generalMixedRawInnerStrip (p := p) N I K‖ ≤
      ‖dyadicHaar 𝕜 p I‖ * (‖N‖ * (intervalLpDyadicRadius K.1)⁻¹) := by
  have hinner : ‖N.comp (generalMixedOuterHaarReader (𝕜 := 𝕜) (p := p) K)‖ ≤
      ‖N‖ * (intervalLpDyadicRadius K.1)⁻¹ :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_left (norm_generalMixedOuterHaarReader_le K) (norm_nonneg N))
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul (generalMixed_norm_tensorInnerMap_le _) hinner (norm_nonneg _) (norm_nonneg _))

theorem generalMixedRawOuterStrip_haar (hp : p ≠ ∞)
    (S : Lp 𝕜 p unitIntervalMeasure →L[𝕜] Lp 𝕜 p unitIntervalMeasure)
    (d : DyadicIndex → 𝕜) (hS : ∀ I, S (dyadicHaar 𝕜 p I) = d I • dyadicHaar 𝕜 p I)
    (J L I R : DyadicIndex) :
    generalMixedRawOuterStrip S J L (productHaar 𝕜 p I R) =
      if L = R then d I • productHaar 𝕜 p I J else 0 := by
  rw [generalMixedRawOuterStrip, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, productHaar, innerFunctional_tensor,
    dyadicHaarCoordinate_biorthogonal (by simp : (1 : ℝ≥0∞) ≠ ∞)]
  by_cases h : L = R <;> simp [h, hS I, productHaar]

theorem generalMixedRawInnerStrip_haar (hp : p ≠ ∞)
    (N : Lp 𝕜 1 unitIntervalMeasure →L[𝕜] Lp 𝕜 1 unitIntervalMeasure)
    (e : DyadicIndex → 𝕜) (hN : ∀ J, N (dyadicHaar 𝕜 1 J) = e J • dyadicHaar 𝕜 1 J)
    (I K L J : DyadicIndex) :
    generalMixedRawInnerStrip (p := p) N I K (productHaar 𝕜 p L J) =
      if K = L then e J • productHaar 𝕜 p I J else 0 := by
  rw [generalMixedRawInnerStrip, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, productHaar, generalMixedOuterHaarReader_tensor,
    dyadicHaarCoordinate_biorthogonal hp]
  by_cases h : K = L
  · simp only [h, if_true, one_smul, hN J]
    exact tensorWith_smul_inner _ _ _
  · simp [h]

end SurveyStatements.P5

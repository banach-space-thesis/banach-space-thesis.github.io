import SurveyStatements.P5OperatorReductionPacketGeometryNorms
import SurveyStatements.P5OperatorReductionReaders
import SurveyStatements.P5OperatorReductionMoments
import SurveyStatements.P5HaarNorm

/-! Actual outer Lp operators obtained by averaging the inner signed Haar
packet. Their normalization is the measure of the genuine packet parent. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open MeasureTheory Filter
open scoped ENNReal Classical BigOperators

namespace SurveyStatements.P5OperatorReduction
open SurveyStatements.P5 SurveyStatements.P5Support
variable {𝕜 : Type*} [RCLike 𝕜]

def outerShadowFiniteMean {Ω E : Type*} [Fintype Ω]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (v : Ω → E) : E :=
  (((Fintype.card Ω : ℝ)⁻¹ : ℝ) : 𝕜) • ∑ θ, v θ

theorem outerShadowFiniteMean_map {Ω E F : Type*} [Fintype Ω]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (L : E →L[𝕜] F) (v : Ω → E) :
    L (outerShadowFiniteMean (𝕜 := 𝕜) v) =
      outerShadowFiniteMean (𝕜 := 𝕜) (fun θ => L (v θ)) := by
  simp only [outerShadowFiniteMean, map_smul, map_sum]

theorem norm_outerShadowFiniteMean_le {Ω E : Type*} [Fintype Ω] [Nonempty Ω]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (v : Ω → E) (C : ℝ) (hv : ∀ θ, ‖v θ‖ ≤ C) :
    ‖outerShadowFiniteMean (𝕜 := 𝕜) v‖ ≤ C := by
  have hc : (Fintype.card Ω : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [outerShadowFiniteMean, norm_smul, RCLike.norm_ofReal,
    abs_of_nonneg (by positivity)]
  calc
    _ ≤ (Fintype.card Ω : ℝ)⁻¹ * ∑ θ, ‖v θ‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ (Fintype.card Ω : ℝ)⁻¹ * ∑ _θ : Ω, C :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun θ _ => hv θ)) (by positivity)
    _ = C := by simp [Finset.sum_const, nsmul_eq_mul, ← mul_assoc, hc]

def outerShadowL1Exponent : BanachExponent := ⟨1, le_rfl⟩

theorem outerShadow_scalarSign_norm (b : Bool) :
    ‖scalarSign (𝕜 := 𝕜) b‖ = 1 := by
  cases b <;> simp [scalarSign]

def outerShadowInnerWeight (n : ℕ) (S : Finset (Fin (2 ^ n)))
    (θ : Fin (2 ^ n) → Bool) : ℝ → 𝕜 :=
  operatorReductionRawPacketFunction n S (fun k => scalarSign (θ k))

theorem outerShadowInnerWeight_measurable (n : ℕ) (S : Finset (Fin (2 ^ n)))
    (θ : Fin (2 ^ n) → Bool) :
    StronglyMeasurable (outerShadowInnerWeight (𝕜 := 𝕜) n S θ) := by
  apply Finset.stronglyMeasurable_fun_sum
  intro k _
  exact stronglyMeasurable_const.mul
    ((stronglyMeasurable_const.indicator measurableSet_Ioc).sub
      (stronglyMeasurable_const.indicator measurableSet_Ioc))

theorem outerShadowInnerWeight_bound (n : ℕ) (S : Finset (Fin (2 ^ n)))
    (θ : Fin (2 ^ n) → Bool) (x : ℝ) :
    ‖outerShadowInnerWeight (𝕜 := 𝕜) n S θ x‖ ≤ 1 := by
  apply (norm_operatorReductionRawPacketFunction_le n S
    (fun k => scalarSign (θ k))
    (fun k _ => (outerShadow_scalarSign_norm (𝕜 := 𝕜) (θ k)).le) x).trans
  by_cases hx : x ∈ lpHaarBlockParent n S <;> simp [hx]

def outerShadowInnerReader (𝕜 : Type*) [RCLike 𝕜]
    (n : ℕ) (S : Finset (Fin (2 ^ n))) (θ : Fin (2 ^ n) → Bool) :
    Lp 𝕜 1 unitIntervalMeasure →L[𝕜] 𝕜 :=
  weightedOuterReader (p := 1) (outerShadowInnerWeight n S θ)
    (outerShadowInnerWeight_measurable n S θ) (outerShadowInnerWeight_bound n S θ)

def outerShadowInnerPacket (𝕜 : Type*) [RCLike 𝕜]
    (n : ℕ) (S : Finset (Fin (2 ^ n))) (θ : Fin (2 ^ n) → Bool) :
    Lp 𝕜 1 unitIntervalMeasure :=
  operatorReductionRawHaarPacket 𝕜 outerShadowL1Exponent n S (fun k => scalarSign (θ k))

def outerShadowParentMass (n : ℕ) (S : Finset (Fin (2 ^ n))) : ℝ :=
  (S.card : ℝ) * intervalLpDyadicRadius n

def outerShadowSignedOperator (p : BanachExponent)
    (T : MixedNorm 𝕜 p.val →L[𝕜] MixedNorm 𝕜 p.val)
    (n : ℕ) (S : Finset (Fin (2 ^ n))) (θ : Fin (2 ^ n) → Bool) :
    Lp 𝕜 p.val unitIntervalMeasure →L[𝕜] Lp 𝕜 p.val unitIntervalMeasure :=
  ((outerShadowInnerReader 𝕜 n S θ).compLpL p.val unitIntervalMeasure).comp
    (T.comp (tensorWith (p := p.val) (outerShadowInnerPacket 𝕜 n S θ)))

def outerHaarPacketShadow (p : BanachExponent)
    (T : MixedNorm 𝕜 p.val →L[𝕜] MixedNorm 𝕜 p.val)
    (n : ℕ) (S : Finset (Fin (2 ^ n))) :
    Lp 𝕜 p.val unitIntervalMeasure →L[𝕜] Lp 𝕜 p.val unitIntervalMeasure :=
  ((outerShadowParentMass n S)⁻¹ : 𝕜) •
    outerShadowFiniteMean (𝕜 := 𝕜) (outerShadowSignedOperator p T n S)

theorem outerHaarPacketShadow_apply (p : BanachExponent)
    (T : MixedNorm 𝕜 p.val →L[𝕜] MixedNorm 𝕜 p.val)
    (n : ℕ) (S : Finset (Fin (2 ^ n))) (f : Lp 𝕜 p.val unitIntervalMeasure) :
    outerHaarPacketShadow p T n S f =
      ((outerShadowParentMass n S)⁻¹ : 𝕜) •
        outerShadowFiniteMean (𝕜 := 𝕜) (fun θ =>
          (outerShadowInnerReader 𝕜 n S θ).compLpL p.val unitIntervalMeasure
            (T (tensorWith (p := p.val) (outerShadowInnerPacket 𝕜 n S θ) f))) := by
  simp only [outerHaarPacketShadow, outerShadowFiniteMean,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
    outerShadowSignedOperator, ContinuousLinearMap.comp_apply]

end SurveyStatements.P5OperatorReduction

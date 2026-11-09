import SurveyStatements.P5OperatorReductionOuterShadows

/-! Uniform norm bounds for the actual inner-averaged outer operators. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open MeasureTheory
open scoped ENNReal Classical BigOperators

namespace SurveyStatements.P5OperatorReduction
open SurveyStatements.P5 SurveyStatements.P5Support
variable {𝕜 : Type*} [RCLike 𝕜]

theorem outerShadowParentMass_nonneg (n : ℕ) (S : Finset (Fin (2 ^ n))) :
    0 ≤ outerShadowParentMass n S :=
  mul_nonneg (Nat.cast_nonneg _) (intervalLpDyadicRadius_pos n).le

theorem norm_outerShadowInnerReader_le (n : ℕ) (S : Finset (Fin (2 ^ n)))
    (θ : Fin (2 ^ n) → Bool) : ‖outerShadowInnerReader 𝕜 n S θ‖ ≤ 1 :=
  norm_weightedOuterReader_le (𝕜 := 𝕜) (E := 𝕜) (p := 1)
    (outerShadowInnerWeight n S θ)
    (outerShadowInnerWeight_measurable n S θ) (outerShadowInnerWeight_bound n S θ)

theorem norm_outerShadowInnerPacket_le (n : ℕ) (S : Finset (Fin (2 ^ n)))
    (θ : Fin (2 ^ n) → Bool) :
    ‖outerShadowInnerPacket 𝕜 n S θ‖ ≤ outerShadowParentMass n S := by
  have h := norm_operatorReductionRawHaarPacket_le (𝕜 := 𝕜)
    outerShadowL1Exponent (by norm_num [outerShadowL1Exponent]) n S
    (fun k => scalarSign (θ k))
    (fun k _ => (outerShadow_scalarSign_norm (𝕜 := 𝕜) (θ k)).le)
  simpa only [outerShadowInnerPacket, outerShadowParentMass, outerShadowL1Exponent,
    ENNReal.toReal_one, div_one, Real.rpow_one] using h

theorem norm_tensorWith_operator_le (p : BanachExponent)
    (g : Lp 𝕜 1 unitIntervalMeasure) : ‖tensorWith (p := p.val) g‖ ≤ ‖g‖ := by
  apply (tensorWith (p := p.val) g).opNorm_le_bound (norm_nonneg g)
  intro f
  exact (norm_tensorWith 𝕜 p.val g f).le

theorem norm_outerShadowSignedOperator_le (p : BanachExponent)
    (T : MixedNorm 𝕜 p.val →L[𝕜] MixedNorm 𝕜 p.val)
    (n : ℕ) (S : Finset (Fin (2 ^ n))) (θ : Fin (2 ^ n) → Bool) :
    ‖outerShadowSignedOperator p T n S θ‖ ≤ ‖T‖ * outerShadowParentMass n S := by
  have hreader : ‖(outerShadowInnerReader 𝕜 n S θ).compLpL p.val unitIntervalMeasure‖ ≤ 1 :=
    (ContinuousLinearMap.norm_compLpL_le (p := p.val) (μ := unitIntervalMeasure)
      (outerShadowInnerReader 𝕜 n S θ)).trans (norm_outerShadowInnerReader_le n S θ)
  have hin : ‖tensorWith (p := p.val) (outerShadowInnerPacket 𝕜 n S θ)‖ ≤
      outerShadowParentMass n S :=
    (norm_tensorWith_operator_le p _).trans (norm_outerShadowInnerPacket_le n S θ)
  unfold outerShadowSignedOperator
  calc
    _ ≤ ‖(outerShadowInnerReader 𝕜 n S θ).compLpL p.val unitIntervalMeasure‖ *
        ‖T.comp (tensorWith (p := p.val) (outerShadowInnerPacket 𝕜 n S θ))‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * (‖T‖ * outerShadowParentMass n S) :=
      mul_le_mul hreader ((T.opNorm_comp_le _).trans
        (mul_le_mul_of_nonneg_left hin (norm_nonneg T)))
        (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

theorem norm_outerHaarPacketShadow_le (p : BanachExponent)
    (T : MixedNorm 𝕜 p.val →L[𝕜] MixedNorm 𝕜 p.val)
    (n : ℕ) (S : Finset (Fin (2 ^ n))) :
    ‖outerHaarPacketShadow p T n S‖ ≤ ‖T‖ := by
  have hmass := outerShadowParentMass_nonneg n S
  by_cases hz : outerShadowParentMass n S = 0
  · simp only [outerHaarPacketShadow, hz, inv_zero, RCLike.ofReal_zero,
      zero_smul, norm_zero]
    exact norm_nonneg T
  · rw [outerHaarPacketShadow, norm_smul, norm_inv, RCLike.norm_ofReal,
      abs_of_nonneg hmass]
    calc
      _ ≤ (outerShadowParentMass n S)⁻¹ * (‖T‖ * outerShadowParentMass n S) :=
        mul_le_mul_of_nonneg_left
          (norm_outerShadowFiniteMean_le _ _ (norm_outerShadowSignedOperator_le p T n S))
          (inv_nonneg.mpr hmass)
      _ = ‖T‖ := by field_simp

end SurveyStatements.P5OperatorReduction

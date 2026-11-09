import SurveyStatements.P5OperatorReductionPacketGeometryNorms

/-! Cardinal-normalized phase packets have one uniform actual pointwise bound
on every refinement of their fixed parent. This is the support estimate used
for uniform integrability of the operator-reduction packets. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter Set
open scoped ENNReal BigOperators Classical

namespace SurveyStatements.P5
open P5Support
variable {𝕜 : Type*} [RCLike 𝕜]

def operatorReductionUnitHaarPacket (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent)
    (n : ℕ) (S : Finset (Fin (2 ^ n))) (a : Fin (2 ^ n) → 𝕜) : IntervalLp 𝕜 p :=
  (((S.card : ℝ) ^ (1 / p.val.toReal) : ℝ) : 𝕜)⁻¹ •
    operatorReductionNormalizedHaarPacket 𝕜 p n S a

theorem operatorReductionNormalizedHaarPacket_norm_ae
    (p : BanachExponent) (hp : p.val ≠ ∞) (n : ℕ)
    (S : Finset (Fin (2 ^ n))) (a : Fin (2 ^ n) → 𝕜)
    (ha : ∀ k ∈ S, ‖a k‖ = 1) :
    ∀ᵐ x ∂unitIntervalMeasure,
      ‖operatorReductionNormalizedHaarPacket 𝕜 p n S a x‖ =
        (intervalLpDyadicRadius n ^ (1 / p.val.toReal))⁻¹ *
          (lpHaarBlockParent n S).indicator (fun _ => (1 : ℝ)) x := by
  rw [operatorReductionNormalizedHaarPacket_eq_scaled_raw p hp]
  filter_upwards [Lp.coeFn_smul
    (((intervalLpDyadicRadius n ^ (1 / p.val.toReal) : ℝ) : 𝕜)⁻¹)
    (operatorReductionRawHaarPacket 𝕜 p n S a),
    operatorReductionRawHaarPacket_ae p n S a] with x hsmul hraw
  have hpos := Real.rpow_pos_of_pos (intervalLpDyadicRadius_pos n) (1 / p.val.toReal)
  rw [hsmul, Pi.smul_apply, norm_smul, norm_inv, RCLike.norm_ofReal,
    abs_of_nonneg hpos.le, hraw, norm_operatorReductionRawPacketFunction_eq n S a ha]

theorem operatorReductionUnitHaarPacket_norm_ae
    (p : BanachExponent) (hp : p.val ≠ ∞) (n : ℕ)
    (S : Finset (Fin (2 ^ n))) (a : Fin (2 ^ n) → 𝕜)
    (ha : ∀ k ∈ S, ‖a k‖ = 1) :
    ∀ᵐ x ∂unitIntervalMeasure,
      ‖operatorReductionUnitHaarPacket 𝕜 p n S a x‖ =
        (((S.card : ℝ) * intervalLpDyadicRadius n) ^ (1 / p.val.toReal))⁻¹ *
          (lpHaarBlockParent n S).indicator (fun _ => (1 : ℝ)) x := by
  filter_upwards [Lp.coeFn_smul
    ((((S.card : ℝ) ^ (1 / p.val.toReal) : ℝ) : 𝕜)⁻¹)
    (operatorReductionNormalizedHaarPacket 𝕜 p n S a),
    operatorReductionNormalizedHaarPacket_norm_ae p hp n S a ha] with x hsmul hnorm
  rw [operatorReductionUnitHaarPacket, hsmul, Pi.smul_apply,
    norm_smul, norm_inv, RCLike.norm_ofReal,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _), hnorm,
    Real.mul_rpow (Nat.cast_nonneg _) (intervalLpDyadicRadius_pos n).le,
    mul_inv, mul_assoc]

theorem operatorReductionUnitHaarPacket_refine_norm_ae
    (p : BanachExponent) (hp : p.val ≠ ∞) (n : ℕ)
    (S : Finset (Fin (2 ^ n))) (d : ℕ) (a : Fin (2 ^ (n + d)) → 𝕜)
    (ha : ∀ k ∈ lpHaarRefine n S d, ‖a k‖ = 1) :
    ∀ᵐ x ∂unitIntervalMeasure,
      ‖operatorReductionUnitHaarPacket 𝕜 p (n + d) (lpHaarRefine n S d) a x‖ =
        (((S.card : ℝ) * intervalLpDyadicRadius n) ^ (1 / p.val.toReal))⁻¹ *
          (lpHaarBlockParent n S).indicator (fun _ => (1 : ℝ)) x := by
  filter_upwards [operatorReductionUnitHaarPacket_norm_ae p hp (n + d)
    (lpHaarRefine n S d) a ha] with x hx
  simpa only [lpHaarRefine_mass, lpHaarBlockParent_refine] using hx

theorem operatorReductionUnitHaarPacket_refine_uniform_bound
    (p : BanachExponent) (hp : p.val ≠ ∞) (n : ℕ)
    (S : Finset (Fin (2 ^ n))) (d : ℕ) (a : Fin (2 ^ (n + d)) → 𝕜)
    (ha : ∀ k ∈ lpHaarRefine n S d, ‖a k‖ = 1) :
    ∀ᵐ x ∂unitIntervalMeasure,
      ‖operatorReductionUnitHaarPacket 𝕜 p (n + d) (lpHaarRefine n S d) a x‖ ≤
        (((S.card : ℝ) * intervalLpDyadicRadius n) ^ (1 / p.val.toReal))⁻¹ := by
  filter_upwards [operatorReductionUnitHaarPacket_refine_norm_ae p hp n S d a ha]
    with x hx
  rw [hx]
  by_cases hmem : x ∈ lpHaarBlockParent n S
  · simpa only [Set.indicator_of_mem hmem, mul_one] using
      (le_rfl :
        (((S.card : ℝ) * intervalLpDyadicRadius n) ^ (1 / p.val.toReal))⁻¹ ≤
        (((S.card : ℝ) * intervalLpDyadicRadius n) ^ (1 / p.val.toReal))⁻¹)
  · rw [Set.indicator_of_notMem hmem, mul_zero]
    exact inv_nonneg.mpr (Real.rpow_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (intervalLpDyadicRadius_pos n).le) _)

end SurveyStatements.P5

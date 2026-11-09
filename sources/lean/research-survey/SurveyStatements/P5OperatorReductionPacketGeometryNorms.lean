import SurveyStatements.P5OperatorReductionPacketGeometryFunctions

/-! Same-level packet norms derived from their actual disjoint support cells.
Normalized Haar packets have the exact card^(1/p) bound used in matrix moments. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter Set
open scoped ENNReal BigOperators Classical

namespace SurveyStatements.P5
open P5Support
variable {𝕜 : Type*} [RCLike 𝕜]

def operatorReductionPacketIndicator (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent)
    (n : ℕ) (S : Finset (Fin (2 ^ n))) : IntervalLp 𝕜 p :=
  indicatorConstLp (s := lpHaarBlockParent n S) p.val
    (S.measurableSet_biUnion (fun _ _ => measurableSet_Ioc))
    (measure_ne_top _ _) (1 : 𝕜)

theorem operatorReductionPacketIndicator_norm_ae (p : BanachExponent)
    (n : ℕ) (S : Finset (Fin (2 ^ n))) :
    ∀ᵐ x ∂unitIntervalMeasure,
      ‖operatorReductionPacketIndicator 𝕜 p n S x‖ =
        (lpHaarBlockParent n S).indicator (fun _ => (1 : ℝ)) x := by
  filter_upwards [indicatorConstLp_coeFn (p := p.val)
    (s := lpHaarBlockParent n S)
    (hs := S.measurableSet_biUnion (fun _ _ => measurableSet_Ioc))
    (hμs := measure_ne_top (volume.restrict (Icc (0 : ℝ) 1)) (lpHaarBlockParent n S))
    (c := (1 : 𝕜))] with x hx
  change operatorReductionPacketIndicator 𝕜 p n S x =
    (lpHaarBlockParent n S).indicator (fun _ => (1 : 𝕜)) x at hx
  by_cases hmem : x ∈ lpHaarBlockParent n S
  · simpa only [Set.indicator_of_mem hmem, norm_one] using congrArg norm hx
  · simpa only [Set.indicator_of_notMem hmem, norm_zero] using congrArg norm hx

theorem norm_operatorReductionPacketIndicator (p : BanachExponent) (hp : p.val ≠ ∞)
    (n : ℕ) (S : Finset (Fin (2 ^ n))) :
    ‖operatorReductionPacketIndicator 𝕜 p n S‖ =
      ((S.card : ℝ) * intervalLpDyadicRadius n) ^ (1 / p.val.toReal) := by
  rw [operatorReductionPacketIndicator, norm_indicatorConstLp
    (ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ≥0∞) < 1) p.property)) hp,
    norm_one, one_mul]
  change ((volume.restrict (Icc (0 : ℝ) 1)).real (lpHaarBlockParent n S)) ^
    (1 / p.val.toReal) = _
  rw [lpHaarBlockParent_real_measure]

theorem norm_operatorReductionRawHaarPacket_le (p : BanachExponent) (hp : p.val ≠ ∞)
    (n : ℕ) (S : Finset (Fin (2 ^ n))) (a : Fin (2 ^ n) → 𝕜)
    (ha : ∀ k ∈ S, ‖a k‖ ≤ 1) :
    ‖operatorReductionRawHaarPacket 𝕜 p n S a‖ ≤
      ((S.card : ℝ) * intervalLpDyadicRadius n) ^ (1 / p.val.toReal) := by
  calc
    _ ≤ ‖operatorReductionPacketIndicator 𝕜 p n S‖ := by
      apply Lp.norm_le_norm_of_ae_le
      filter_upwards [operatorReductionRawHaarPacket_ae p n S a,
        operatorReductionPacketIndicator_norm_ae (𝕜 := 𝕜) p n S] with x hraw hind
      rw [hraw, hind]
      exact norm_operatorReductionRawPacketFunction_le n S a ha x
    _ = _ := norm_operatorReductionPacketIndicator p hp n S

theorem norm_operatorReductionRawHaarPacket_eq (p : BanachExponent) (hp : p.val ≠ ∞)
    (n : ℕ) (S : Finset (Fin (2 ^ n))) (a : Fin (2 ^ n) → 𝕜)
    (ha : ∀ k ∈ S, ‖a k‖ = 1) :
    ‖operatorReductionRawHaarPacket 𝕜 p n S a‖ =
      ((S.card : ℝ) * intervalLpDyadicRadius n) ^ (1 / p.val.toReal) := by
  have heq : ∀ᵐ x ∂unitIntervalMeasure,
      ‖operatorReductionRawHaarPacket 𝕜 p n S a x‖ =
        ‖operatorReductionPacketIndicator 𝕜 p n S x‖ := by
    filter_upwards [operatorReductionRawHaarPacket_ae p n S a,
      operatorReductionPacketIndicator_norm_ae (𝕜 := 𝕜) p n S] with x hraw hind
    rw [hraw, hind]
    exact norm_operatorReductionRawPacketFunction_eq n S a ha x
  calc
    _ = ‖operatorReductionPacketIndicator 𝕜 p n S‖ :=
      congrArg ENNReal.toReal (eLpNorm_congr_norm_ae (p := p.val) heq)
    _ = _ := norm_operatorReductionPacketIndicator p hp n S

theorem operatorReductionNormalizedHaarPacket_eq_scaled_raw
    (p : BanachExponent) (hp : p.val ≠ ∞) (n : ℕ)
    (S : Finset (Fin (2 ^ n))) (a : Fin (2 ^ n) → 𝕜) :
    operatorReductionNormalizedHaarPacket 𝕜 p n S a =
      ((intervalLpDyadicRadius n ^ (1 / p.val.toReal) : ℝ) : 𝕜)⁻¹ •
        operatorReductionRawHaarPacket 𝕜 p n S a := by
  unfold operatorReductionNormalizedHaarPacket operatorReductionRawHaarPacket
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [lpHaarNormalizedVector, lpHaarRawVector,
    lpHaarDyadic_norm 𝕜 p hp n k k.isLt, smul_smul, smul_smul, mul_comm]

theorem operatorReductionPacket_scale_identity (p : BanachExponent) (n : ℕ)
    (S : Finset (Fin (2 ^ n))) :
    (intervalLpDyadicRadius n ^ (1 / p.val.toReal))⁻¹ *
      ((S.card : ℝ) * intervalLpDyadicRadius n) ^ (1 / p.val.toReal) =
        (S.card : ℝ) ^ (1 / p.val.toReal) := by
  have hpos := Real.rpow_pos_of_pos (intervalLpDyadicRadius_pos n) (1 / p.val.toReal)
  rw [Real.mul_rpow (Nat.cast_nonneg _) (intervalLpDyadicRadius_pos n).le]
  calc
    _ = (S.card : ℝ) ^ (1 / p.val.toReal) *
        ((intervalLpDyadicRadius n ^ (1 / p.val.toReal))⁻¹ *
          intervalLpDyadicRadius n ^ (1 / p.val.toReal)) := by ring
    _ = _ := by rw [inv_mul_cancel₀ hpos.ne', mul_one]

theorem norm_operatorReductionNormalizedHaarPacket_le
    (p : BanachExponent) (hp : p.val ≠ ∞) (n : ℕ)
    (S : Finset (Fin (2 ^ n))) (a : Fin (2 ^ n) → 𝕜)
    (ha : ∀ k ∈ S, ‖a k‖ ≤ 1) :
    ‖operatorReductionNormalizedHaarPacket 𝕜 p n S a‖ ≤
      (S.card : ℝ) ^ (1 / p.val.toReal) := by
  have hpos := Real.rpow_pos_of_pos (intervalLpDyadicRadius_pos n) (1 / p.val.toReal)
  rw [operatorReductionNormalizedHaarPacket_eq_scaled_raw p hp,
    norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_nonneg hpos.le]
  exact (mul_le_mul_of_nonneg_left (norm_operatorReductionRawHaarPacket_le p hp n S a ha)
    (inv_nonneg.mpr hpos.le)).trans_eq (operatorReductionPacket_scale_identity p n S)

theorem norm_operatorReductionNormalizedHaarPacket_eq
    (p : BanachExponent) (hp : p.val ≠ ∞) (n : ℕ)
    (S : Finset (Fin (2 ^ n))) (a : Fin (2 ^ n) → 𝕜)
    (ha : ∀ k ∈ S, ‖a k‖ = 1) :
    ‖operatorReductionNormalizedHaarPacket 𝕜 p n S a‖ =
      (S.card : ℝ) ^ (1 / p.val.toReal) := by
  have hpos := Real.rpow_pos_of_pos (intervalLpDyadicRadius_pos n) (1 / p.val.toReal)
  rw [operatorReductionNormalizedHaarPacket_eq_scaled_raw p hp,
    norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_nonneg hpos.le,
    norm_operatorReductionRawHaarPacket_eq p hp n S a ha]
  exact operatorReductionPacket_scale_identity p n S

end SurveyStatements.P5

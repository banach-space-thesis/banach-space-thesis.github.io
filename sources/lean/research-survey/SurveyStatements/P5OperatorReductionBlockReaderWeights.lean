import SurveyStatements.P5OperatorReductionShadowExpansion
import SurveyStatements.P5Support.LpHaarBlockReaders

/-! Exact agreement of the actual finite signed block reader with the
parent-normalized raw Haar weighted integral reader, for every exponent. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter Set
open scoped ENNReal Classical BigOperators
namespace SurveyStatements.P5OperatorReduction
open SurveyStatements.P5 SurveyStatements.P5Support
local instance blockReaderWeightsVolumeProbability :
    IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) := ⟨by simp⟩
variable {𝕜 : Type*} [RCLike 𝕜]

theorem weightedOuterReader_haar_eq_radius_coefficient (p : BanachExponent)
    (n : ℕ) (k : Fin (2 ^ n)) (f : IntervalLp 𝕜 p) :
    weightedOuterReader (𝕜 := 𝕜) (E := 𝕜) (p := p.val)
      (haarPacketWeight (𝕜 := 𝕜) n k)
      (haarPacketWeight_stronglyMeasurable n k) (haarPacketWeight_norm_le n k) f =
      (intervalLpDyadicRadius n : 𝕜) * lpHaarDyadicCoefficient 𝕜 p n k f := by
  have hm : (volume.restrict (Set.Icc (0 : ℝ) 1)).real
      (lpHaarCell (n + 1) (2 * k.val) ∪ lpHaarCell (n + 1) (2 * k.val + 1)) =
      intervalLpDyadicRadius n := by
    rw [lpHaarCell_children, measureReal_def, lpHaarCell_measure n k k.isLt,
      ENNReal.toReal_ofReal (intervalLpDyadicRadius_pos n).le]
  have hn : (intervalLpDyadicRadius n : 𝕜) ≠ 0 :=
    RCLike.ofReal_ne_zero.mpr (intervalLpDyadicRadius_pos n).ne'
  have hreader :
      weightedOuterReader (𝕜 := 𝕜) (E := 𝕜) (p := p.val)
        (haarPacketWeight (𝕜 := 𝕜) n k)
        (haarPacketWeight_stronglyMeasurable n k) (haarPacketWeight_norm_le n k) f =
      ∫ x, haarPacketWeight (𝕜 := 𝕜) n k x * f x
        ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    change probabilityLpIntegral (𝕜 := 𝕜)
      (vectorBoundedMultiply (𝕜 := 𝕜) (E := 𝕜) (p := p.val)
        (haarPacketWeight (𝕜 := 𝕜) n k)
        (haarPacketWeight_stronglyMeasurable n k) (haarPacketWeight_norm_le n k) f) = _
    rw [probabilityLpIntegral_apply]
    change (@integral ℝ 𝕜 _ (NormedSpace.restrictScalars ℝ 𝕜 𝕜)
      _ (volume.restrict (Set.Icc (0 : ℝ) 1))
      (fun x => (vectorBoundedMultiply (𝕜 := 𝕜) (E := 𝕜) (p := p.val)
        (haarPacketWeight (𝕜 := 𝕜) n k)
        (haarPacketWeight_stronglyMeasurable n k) (haarPacketWeight_norm_le n k) f) x)) = _
    rw [NormedSpace.restrictScalars_eq]
    apply integral_congr_ae
    filter_upwards [vectorBoundedMultiplyValue_ae (𝕜 := 𝕜) (E := 𝕜) (p := p.val)
      (haarPacketWeight (𝕜 := 𝕜) n k)
      (haarPacketWeight_stronglyMeasurable n k) (haarPacketWeight_norm_le n k) f] with x hx
    simpa only [smul_eq_mul] using hx
  rw [hreader, lpHaarDyadicCoefficient, lpHaarCoefficient_apply, hm]
  simp only [haarPacketWeight]
  rw [← mul_assoc, mul_inv_cancel₀ hn, one_mul]

theorem rawPacket_weightedReader_eq_signed_coefficients (p : BanachExponent)
    (n : ℕ) (S : Finset (Fin (2 ^ n))) (θ : Fin (2 ^ n) → Bool)
    (f : IntervalLp 𝕜 p) :
    weightedOuterReader (𝕜 := 𝕜) (E := 𝕜) (p := p.val)
      (operatorReductionRawPacketFunction n S (fun k => scalarSign (θ k)))
      (rawPacketFunction_stronglyMeasurable n S (fun k => scalarSign (θ k)))
      (norm_rawPacketFunction_le_one n S (fun k => scalarSign (θ k))
        (fun k _ => (norm_scalarSign_eq_one (θ k)).le)) f =
      (intervalLpDyadicRadius n : 𝕜) *
        ∑ k ∈ S, signedValue (θ k) (lpHaarDyadicCoefficient 𝕜 p n k f) := by
  have heq (x : ℝ) :
      operatorReductionRawPacketFunction n S (fun k => scalarSign (θ k)) x =
        ∑ k ∈ S, signedWeight (θ k) (haarPacketWeight (𝕜 := 𝕜) n k) x := by
    unfold operatorReductionRawPacketFunction haarPacketWeight signedWeight
    exact Finset.sum_congr rfl (fun k _ => scalarSign_mul (θ k) _)
  rw [weightedOuterReader_finite_sum S
    (fun k => signedWeight (θ k) (haarPacketWeight (𝕜 := 𝕜) n k))
    (fun k => signedWeight_measurable (θ k) (haarPacketWeight n k)
      (haarPacketWeight_stronglyMeasurable n k))
    (fun k => signedWeight_bound (θ k) (haarPacketWeight n k)
      (haarPacketWeight_norm_le n k))
    (operatorReductionRawPacketFunction n S (fun k => scalarSign (θ k)))
    (rawPacketFunction_stronglyMeasurable n S (fun k => scalarSign (θ k)))
    (norm_rawPacketFunction_le_one n S (fun k => scalarSign (θ k))
      (fun k _ => (norm_scalarSign_eq_one (θ k)).le)) heq f]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [weightedOuterReader_signed_param (θ k) (haarPacketWeight n k)
    (haarPacketWeight_stronglyMeasurable n k) (haarPacketWeight_norm_le n k) f,
    weightedOuterReader_haar_eq_radius_coefficient p n k f]
  cases θ k <;> simp [signedValue, mul_neg]

theorem lpHaarSignedBlockReader_eq_rawWeightedReader (p : BanachExponent)
    (n : ℕ) (S : Finset (Fin (2 ^ n))) (θ : Fin (2 ^ n) → Bool) :
    lpHaarSignedBlockReader 𝕜 p n S θ =
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).real (lpHaarBlockParent n S) : 𝕜)⁻¹ •
        weightedOuterReader (𝕜 := 𝕜) (E := 𝕜) (p := p.val)
          (operatorReductionRawPacketFunction n S (fun k => scalarSign (θ k)))
          (rawPacketFunction_stronglyMeasurable n S (fun k => scalarSign (θ k)))
          (norm_rawPacketFunction_le_one n S (fun k => scalarSign (θ k))
            (fun k _ => (norm_scalarSign_eq_one (θ k)).le)) := by
  ext f
  rw [lpHaarSignedBlockReader_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  change (S.card : 𝕜)⁻¹ *
      ∑ k ∈ S, signedValue (θ k) (lpHaarDyadicCoefficient 𝕜 p n k f) =
    ((volume.restrict (Set.Icc (0 : ℝ) 1)).real (lpHaarBlockParent n S) : 𝕜)⁻¹ *
      weightedOuterReader (𝕜 := 𝕜) (E := 𝕜) (p := p.val)
        (operatorReductionRawPacketFunction n S (fun k => scalarSign (θ k)))
        (rawPacketFunction_stronglyMeasurable n S (fun k => scalarSign (θ k)))
        (norm_rawPacketFunction_le_one n S (fun k => scalarSign (θ k))
          (fun k _ => (norm_scalarSign_eq_one (θ k)).le)) f
  rw [rawPacket_weightedReader_eq_signed_coefficients (𝕜 := 𝕜) p n S θ f,
    lpHaarBlockParent_real_measure]
  push_cast
  have hr : (intervalLpDyadicRadius n : 𝕜) ≠ 0 :=
    RCLike.ofReal_ne_zero.mpr (intervalLpDyadicRadius_pos n).ne'
  rw [mul_inv_rev]
  calc
    _ = (S.card : 𝕜)⁻¹ *
        ((intervalLpDyadicRadius n : 𝕜)⁻¹ * (intervalLpDyadicRadius n : 𝕜)) *
        ∑ k ∈ S, signedValue (θ k) (lpHaarDyadicCoefficient 𝕜 p n k f) := by
      rw [inv_mul_cancel₀ hr, mul_one]
    _ = _ := by ring

theorem rawHaarPacket_eq_signedBlock (p : BanachExponent)
    (n : ℕ) (S : Finset (Fin (2 ^ n))) (θ : Fin (2 ^ n) → Bool) :
    operatorReductionRawHaarPacket 𝕜 p n S (fun k => scalarSign (θ k)) =
      lpHaarSignedBlock 𝕜 p n S θ := by
  unfold operatorReductionRawHaarPacket lpHaarSignedBlock
  apply Finset.sum_congr rfl
  intro k _
  cases hθ : θ k <;> simp [scalarSign, signedValue, hθ]

end SurveyStatements.P5OperatorReduction

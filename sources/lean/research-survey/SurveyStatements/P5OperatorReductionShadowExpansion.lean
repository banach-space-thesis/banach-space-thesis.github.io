import SurveyStatements.P5OperatorReductionShadowExpansionMasks
import SurveyStatements.P5OperatorReductionRawShadows
import SurveyStatements.P5Support.LpMeanZeroRetracts

/-! Exact finite-sign expansion of the actual raw Haar-packet shadow.
The full sign cube is retained even when the packet uses a subset of a level. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal Classical BigOperators

namespace SurveyStatements.P5OperatorReduction
open SurveyStatements.P5 SurveyStatements.P5Support
local instance shadowExpansionVolumeProbability :
    IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) := ⟨by simp⟩
variable {𝕜 : Type*} [RCLike 𝕜]

/-- The weighted-reader integral uses the existing compatible real structure. -/
theorem weightedOuterReader_apply_real {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (η : ℝ → 𝕜) (hη : StronglyMeasurable η) (hb : ∀ x, ‖η x‖ ≤ 1)
    (f : Lp E p (volume.restrict (Set.Icc (0 : ℝ) 1))) :
    weightedOuterReader (𝕜 := 𝕜) η hη hb f =
      ∫ x, η x • f x ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  rw [weightedOuterReader_apply]
  change (@integral ℝ E _ (NormedSpace.restrictScalars ℝ 𝕜 E)
    _ (volume.restrict (Set.Icc (0 : ℝ) 1)) (fun x => η x • f x)) = _
  rw [NormedSpace.restrictScalars_eq]

theorem vectorMean_signed_reader_input_subset
    {Ω E F : Type*} [Fintype Ω] [DecidableEq Ω]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (S : Finset Ω) (A : Ω → E →L[𝕜] F) (x : Ω → E) :
    vectorMean (𝕜 := 𝕜) (fun θ : Ω → Bool =>
      (∑ i ∈ S, signedValue (θ i) (A i))
        (∑ j ∈ S, signedValue (θ j) (x j))) = ∑ i ∈ S, A i (x i) := by
  have h := vectorMean_signed_reader_input (𝕜 := 𝕜)
    (fun i => if i ∈ S then A i else 0)
    (fun i => if i ∈ S then x i else 0)
  simp_rw [sum_signed_mask_eq] at h
  rw [h]
  calc
    _ = ∑ i, if i ∈ S then A i (x i) else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i ∈ S <;> simp [hi]
    _ = _ := sum_mask_eq S _

def haarPacketReader (p : BanachExponent) (n : ℕ) (k : Fin (2 ^ n)) :
    MixedNorm 𝕜 p.val →L[𝕜] Lp 𝕜 1 (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
  weightedOuterReader (𝕜 := 𝕜) (p := p.val) (haarPacketWeight n k)
    (haarPacketWeight_stronglyMeasurable n k) (haarPacketWeight_norm_le n k)

theorem masked_haarPacketReader (p : BanachExponent) (n : ℕ)
    (S : Finset (Fin (2 ^ n))) (k : Fin (2 ^ n)) :
    weightedOuterReader (𝕜 := 𝕜) (E := Lp 𝕜 1 (volume.restrict (Set.Icc (0 : ℝ) 1))) (p := p.val)
      (maskedHaarPacketWeight n S k)
      (maskedHaarPacketWeight_stronglyMeasurable n S k)
      (maskedHaarPacketWeight_norm_le n S k) =
        if k ∈ S then haarPacketReader (𝕜 := 𝕜) p n k else 0 := by
  apply ContinuousLinearMap.ext
  intro f
  rw [weightedOuterReader_apply_real]
  by_cases hk : k ∈ S
  · simp only [if_pos hk]
    change (∫ x, maskedHaarPacketWeight (𝕜 := 𝕜) n S k x • f x ∂(volume.restrict (Set.Icc (0 : ℝ) 1))) =
      weightedOuterReader (𝕜 := 𝕜) (haarPacketWeight (𝕜 := 𝕜) n k)
        (haarPacketWeight_stronglyMeasurable n k) (haarPacketWeight_norm_le n k) f
    rw [weightedOuterReader_apply_real]
    simp only [maskedHaarPacketWeight, if_pos hk]
  · simp only [if_neg hk, ContinuousLinearMap.zero_apply,
      maskedHaarPacketWeight, zero_smul, integral_zero]

theorem rawPacketReader_signed_mask (p : BanachExponent) (n : ℕ)
    (S : Finset (Fin (2 ^ n))) (θ : Fin (2 ^ n) → Bool) :
    weightedOuterReader (𝕜 := 𝕜) (E := Lp 𝕜 1 (volume.restrict (Set.Icc (0 : ℝ) 1))) (p := p.val)
      (operatorReductionRawPacketFunction n S (fun k => scalarSign (θ k)))
      (rawPacketFunction_stronglyMeasurable n S (fun k => scalarSign (θ k)))
      (norm_rawPacketFunction_le_one n S (fun k => scalarSign (θ k))
        (fun k _ => (norm_scalarSign_eq_one (θ k)).le)) =
      ∑ k, signedValue (θ k)
        (if k ∈ S then haarPacketReader (𝕜 := 𝕜) p n k else 0) := by
  rw [weightedOuterReader_signed_sum
    (fun k => maskedHaarPacketWeight (𝕜 := 𝕜) n S k)
    (fun k => maskedHaarPacketWeight_stronglyMeasurable n S k)
    (fun k => maskedHaarPacketWeight_norm_le n S k) θ
    (operatorReductionRawPacketFunction n S (fun k => scalarSign (θ k)))
    (rawPacketFunction_stronglyMeasurable n S (fun k => scalarSign (θ k)))
    (norm_rawPacketFunction_le_one n S (fun k => scalarSign (θ k))
      (fun k _ => (norm_scalarSign_eq_one (θ k)).le))
    (rawPacketFunction_signed_mask n S θ)]
  simp_rw [masked_haarPacketReader]

theorem rawHaarPacketShadow_eq_diagonal_sum {ι : Type*}
    (p : BanachExponent) (n : ι → ℕ) (S : ∀ i, Finset (Fin (2 ^ n i)))
    (T : MixedNorm 𝕜 p.val →L[𝕜] MixedNorm 𝕜 p.val)
    (g : Lp 𝕜 1 (volume.restrict (Set.Icc (0 : ℝ) 1))) (i : ι) :
    rawHaarPacketShadow p n S T g i =
      ∑ k ∈ S i, haarPacketReader (𝕜 := 𝕜) p (n i) k
        (T (tensorWith g (lpHaarDyadic 𝕜 p (n i) k))) := by
  unfold rawHaarPacketShadow packetShadow
  simp_rw [rawPacketReader_signed_mask p (n i) (S i),
    rawHaarPacket_input_signed_mask p (n i) (S i)]
  have hinput (k : Fin (2 ^ n i)) :
      T (tensorWith g (maskedHaarPacketVector (𝕜 := 𝕜) p (n i) (S i) k)) =
        if k ∈ S i then T (tensorWith g (lpHaarDyadic 𝕜 p (n i) k)) else 0 := by
    by_cases hk : k ∈ S i <;> simp [maskedHaarPacketVector, hk]
  simp_rw [hinput, sum_signed_mask_eq]
  exact vectorMean_signed_reader_input_subset (S i)
    (fun k => haarPacketReader (𝕜 := 𝕜) p (n i) k)
    (fun k => T (tensorWith g (lpHaarDyadic 𝕜 p (n i) k)))

theorem normalized_rawHaarPacketShadow_eq_diagonal_sum {ι : Type*}
    (p : BanachExponent) (n : ι → ℕ) (S : ∀ i, Finset (Fin (2 ^ n i)))
    (T : MixedNorm 𝕜 p.val →L[𝕜] MixedNorm 𝕜 p.val)
    (g : Lp 𝕜 1 (volume.restrict (Set.Icc (0 : ℝ) 1))) (i : ι) :
    (RCLike.ofReal (((volume.restrict (Set.Icc (0 : ℝ) 1)) (lpHaarBlockParent (n i) (S i))).toReal⁻¹) : 𝕜) •
        rawHaarPacketShadow p n S T g i =
      (RCLike.ofReal (((volume.restrict (Set.Icc (0 : ℝ) 1)) (lpHaarBlockParent (n i) (S i))).toReal⁻¹) : 𝕜) •
        ∑ k ∈ S i, haarPacketReader (𝕜 := 𝕜) p (n i) k
          (T (tensorWith g (lpHaarDyadic 𝕜 p (n i) k))) := by
  rw [rawHaarPacketShadow_eq_diagonal_sum]

def scalarHaarPacketReader (n : ℕ) (k : Fin (2 ^ n)) :
    Lp 𝕜 1 (volume.restrict (Set.Icc (0 : ℝ) 1)) →L[𝕜] 𝕜 :=
  weightedOuterReader (𝕜 := 𝕜) (p := 1) (haarPacketWeight n k)
    (haarPacketWeight_stronglyMeasurable n k) (haarPacketWeight_norm_le n k)

theorem norm_scalarHaarPacketReader_le (n : ℕ) (k : Fin (2 ^ n)) :
    ‖scalarHaarPacketReader (𝕜 := 𝕜) n k‖ ≤ 1 :=
  norm_weightedOuterReader_le (E := 𝕜) (p := 1) _ _ _

theorem scalarHaarPacketReader_apply (n : ℕ) (k : Fin (2 ^ n))
    (y : Lp 𝕜 1 (volume.restrict (Set.Icc (0 : ℝ) 1))) :
    scalarHaarPacketReader (𝕜 := 𝕜) n k y =
      ∫ x, haarPacketWeight (𝕜 := 𝕜) n k x * y x ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  change probabilityLpIntegral (𝕜 := 𝕜)
    (vectorBoundedMultiply (𝕜 := 𝕜) (E := 𝕜) (p := 1)
      (haarPacketWeight (𝕜 := 𝕜) n k)
      (haarPacketWeight_stronglyMeasurable n k) (haarPacketWeight_norm_le n k) y) = _
  rw [probabilityLpIntegral_apply]
  change (@integral ℝ 𝕜 _ (NormedSpace.restrictScalars ℝ 𝕜 𝕜)
    _ (volume.restrict (Set.Icc (0 : ℝ) 1))
    (fun x => (vectorBoundedMultiply (𝕜 := 𝕜) (E := 𝕜) (p := 1)
      (haarPacketWeight (𝕜 := 𝕜) n k)
      (haarPacketWeight_stronglyMeasurable n k) (haarPacketWeight_norm_le n k) y) x)) = _
  rw [NormedSpace.restrictScalars_eq]
  apply integral_congr_ae
  filter_upwards [vectorBoundedMultiplyValue_ae (𝕜 := 𝕜) (E := 𝕜) (p := 1)
    (haarPacketWeight (𝕜 := 𝕜) n k)
    (haarPacketWeight_stronglyMeasurable n k) (haarPacketWeight_norm_le n k) y] with x hx
  simpa only [smul_eq_mul] using hx

theorem scalarHaarPacketReader_eq_restricted (n : ℕ) (k : Fin (2 ^ n)) :
    scalarHaarPacketReader (𝕜 := 𝕜) n k =
      restrictedFunctional (lpHaarCell n k) measurableSet_Ioc
        (scalarHaarPacketReader (𝕜 := 𝕜) n k) := by
  ext y
  change scalarHaarPacketReader (𝕜 := 𝕜) n k y =
    scalarHaarPacketReader (𝕜 := 𝕜) n k
      (vectorIndicatorMultiply (𝕜 := 𝕜) (lpHaarCell n k) measurableSet_Ioc y)
  rw [scalarHaarPacketReader_apply, scalarHaarPacketReader_apply]
  apply integral_congr_ae
  filter_upwards [vectorIndicatorMultiply_ae (𝕜 := 𝕜)
    (lpHaarCell n k) measurableSet_Ioc y] with x hx
  rw [hx]
  by_cases hmem : x ∈ lpHaarCell n k
  · rw [Set.indicator_of_mem hmem]
  · have hchildren : x ∉ lpHaarCell (n + 1) (2 * k.val) ∪
        lpHaarCell (n + 1) (2 * k.val + 1) := by
      rw [lpHaarCell_children]
      exact hmem
    simp only [Set.mem_union, not_or] at hchildren
    simp [haarPacketWeight, lpHaarFunction, hchildren.1, hchildren.2]

theorem scalarHaarPacketReader_eq_radius_coefficient (n : ℕ)
    (k : Fin (2 ^ n)) (f : Lp 𝕜 1 (volume.restrict (Set.Icc (0 : ℝ) 1))) :
    scalarHaarPacketReader (𝕜 := 𝕜) n k f =
      (intervalLpDyadicRadius n : 𝕜) *
        lpHaarDyadicCoefficient 𝕜 ⟨1, le_rfl⟩ n k f := by
  have hm : (volume.restrict (Set.Icc (0 : ℝ) 1)).real
      (lpHaarCell (n + 1) (2 * k.val) ∪ lpHaarCell (n + 1) (2 * k.val + 1)) =
      intervalLpDyadicRadius n := by
    rw [lpHaarCell_children, measureReal_def, lpHaarCell_measure n k k.isLt,
      ENNReal.toReal_ofReal (intervalLpDyadicRadius_pos n).le]
  have hn : (intervalLpDyadicRadius n : 𝕜) ≠ 0 :=
    RCLike.ofReal_ne_zero.mpr (intervalLpDyadicRadius_pos n).ne'
  rw [scalarHaarPacketReader_apply,
    lpHaarDyadicCoefficient, lpHaarCoefficient_apply, hm]
  simp only [haarPacketWeight]
  rw [← mul_assoc, mul_inv_cancel₀ hn, one_mul]

theorem scalarHaarPacketReader_meanZeroProjection (n : ℕ)
    (k : Fin (2 ^ n)) (f : Lp 𝕜 1 (volume.restrict (Set.Icc (0 : ℝ) 1))) :
    scalarHaarPacketReader (𝕜 := 𝕜) n k
      (intervalLpMeanZeroProjection 𝕜 ⟨1, le_rfl⟩ f).val =
        scalarHaarPacketReader (𝕜 := 𝕜) n k f := by
  rw [scalarHaarPacketReader_eq_radius_coefficient,
    scalarHaarPacketReader_eq_radius_coefficient]
  congr 1
  change lpHaarDyadicCoefficient 𝕜 ⟨1, le_rfl⟩ n k
    (f - lpHaarIntegral f • lpHaarRawVector 𝕜 ⟨1, le_rfl⟩ none) =
      lpHaarDyadicCoefficient 𝕜 ⟨1, le_rfl⟩ n k f
  rw [map_sub, map_smul]
  simp only [lpHaarRawVector]
  rw [lpHaarDyadicCoefficient_const 𝕜 ⟨1, le_rfl⟩ n k (1 : 𝕜),
    smul_zero, sub_zero]

theorem rawL1HaarCoefficient_meanZeroProjection (n : ℕ)
    (k : Fin (2 ^ n)) (f : Lp 𝕜 1 (volume.restrict (Set.Icc (0 : ℝ) 1))) :
    lpHaarDyadicCoefficient 𝕜 ⟨1, le_rfl⟩ n k
      (intervalLpMeanZeroProjection 𝕜 ⟨1, le_rfl⟩ f).val =
        lpHaarDyadicCoefficient 𝕜 ⟨1, le_rfl⟩ n k f := by
  have h := scalarHaarPacketReader_meanZeroProjection n k f
  rw [scalarHaarPacketReader_eq_radius_coefficient,
    scalarHaarPacketReader_eq_radius_coefficient] at h
  exact mul_left_cancel₀
    (RCLike.ofReal_ne_zero.mpr (intervalLpDyadicRadius_pos n).ne') h

theorem masked_scalarHaarPacketReader (n : ℕ)
    (S : Finset (Fin (2 ^ n))) (k : Fin (2 ^ n)) :
    weightedOuterReader (𝕜 := 𝕜) (E := 𝕜) (p := 1)
      (maskedHaarPacketWeight n S k)
      (maskedHaarPacketWeight_stronglyMeasurable n S k)
      (maskedHaarPacketWeight_norm_le n S k) =
        if k ∈ S then scalarHaarPacketReader (𝕜 := 𝕜) n k else 0 := by
  apply ContinuousLinearMap.ext
  intro f
  rw [weightedOuterReader_apply_real]
  by_cases hk : k ∈ S
  · simp only [if_pos hk]
    change (∫ x, maskedHaarPacketWeight (𝕜 := 𝕜) n S k x • f x ∂(volume.restrict (Set.Icc (0 : ℝ) 1))) =
      weightedOuterReader (𝕜 := 𝕜) (haarPacketWeight (𝕜 := 𝕜) n k)
        (haarPacketWeight_stronglyMeasurable n k) (haarPacketWeight_norm_le n k) f
    rw [weightedOuterReader_apply_real]
    simp only [maskedHaarPacketWeight, if_pos hk]
  · simp only [if_neg hk, ContinuousLinearMap.zero_apply,
      maskedHaarPacketWeight, zero_smul, integral_zero]

theorem rawL1PacketReader_signed_mask (n : ℕ)
    (S : Finset (Fin (2 ^ n))) (θ : Fin (2 ^ n) → Bool) :
    weightedOuterReader (𝕜 := 𝕜) (E := 𝕜) (p := 1)
      (operatorReductionRawPacketFunction n S (fun k => scalarSign (θ k)))
      (rawPacketFunction_stronglyMeasurable n S (fun k => scalarSign (θ k)))
      (norm_rawPacketFunction_le_one n S (fun k => scalarSign (θ k))
        (fun k _ => (norm_scalarSign_eq_one (θ k)).le)) =
      ∑ k, signedValue (θ k)
        (if k ∈ S then scalarHaarPacketReader (𝕜 := 𝕜) n k else 0) := by
  rw [weightedOuterReader_signed_sum
    (fun k => maskedHaarPacketWeight (𝕜 := 𝕜) n S k)
    (fun k => maskedHaarPacketWeight_stronglyMeasurable n S k)
    (fun k => maskedHaarPacketWeight_norm_le n S k) θ
    (operatorReductionRawPacketFunction n S (fun k => scalarSign (θ k)))
    (rawPacketFunction_stronglyMeasurable n S (fun k => scalarSign (θ k)))
    (norm_rawPacketFunction_le_one n S (fun k => scalarSign (θ k))
      (fun k _ => (norm_scalarSign_eq_one (θ k)).le))
    (rawPacketFunction_signed_mask n S θ)]
  simp_rw [masked_scalarHaarPacketReader]

/-- The inner L1 version of the finite shadow identity, for an arbitrary
actual L1 operator. It averages the full sign cube, including unused cells. -/
theorem rawL1HaarPacket_reader_input_eq_diagonal_sum (n : ℕ)
    (S : Finset (Fin (2 ^ n)))
    (Q : Lp 𝕜 1 (volume.restrict (Set.Icc (0 : ℝ) 1)) →L[𝕜] Lp 𝕜 1 (volume.restrict (Set.Icc (0 : ℝ) 1))) :
    vectorMean (𝕜 := 𝕜) (fun θ : Fin (2 ^ n) → Bool =>
      weightedOuterReader (𝕜 := 𝕜) (E := 𝕜) (p := 1)
        (operatorReductionRawPacketFunction n S (fun k => scalarSign (θ k)))
        (rawPacketFunction_stronglyMeasurable n S (fun k => scalarSign (θ k)))
        (norm_rawPacketFunction_le_one n S (fun k => scalarSign (θ k))
          (fun k _ => (norm_scalarSign_eq_one (θ k)).le))
        (Q (operatorReductionRawHaarPacket 𝕜 ⟨1, le_rfl⟩ n S
          (fun k => scalarSign (θ k))))) =
      ∑ k ∈ S, scalarHaarPacketReader (𝕜 := 𝕜) n k
        (Q (lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ n k)) := by
  have hQinput (θ : Fin (2 ^ n) → Bool) :
      Q (operatorReductionRawHaarPacket 𝕜 ⟨1, le_rfl⟩ n S
        (fun k => scalarSign (θ k))) =
      ∑ k, signedValue (θ k)
        (Q (maskedHaarPacketVector (𝕜 := 𝕜) ⟨1, le_rfl⟩ n S k)) := by
    rw [rawHaarPacket_signed_mask ⟨1, le_rfl⟩ n S, map_sum]
    simp_rw [map_signedValue]
  simp_rw [rawL1PacketReader_signed_mask, hQinput]
  have hinput (k : Fin (2 ^ n)) :
      Q (maskedHaarPacketVector (𝕜 := 𝕜) ⟨1, le_rfl⟩ n S k) =
        if k ∈ S then Q (lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ n k) else 0 := by
    by_cases hk : k ∈ S <;> simp [maskedHaarPacketVector, hk]
  simp_rw [hinput, sum_signed_mask_eq]
  exact vectorMean_signed_reader_input_subset S
    (fun k => scalarHaarPacketReader (𝕜 := 𝕜) n k)
    (fun k => Q (lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ n k))

end SurveyStatements.P5OperatorReduction

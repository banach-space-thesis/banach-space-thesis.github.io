import SurveyStatements.P5OperatorReductionPacketGeometryFunctions
import SurveyStatements.P5OperatorReductionSignIdentity
import SurveyStatements.P5OperatorReductionMoments
import SurveyStatements.P5HaarNorm

/-! Actual masked same-level Haar packets. Keeping the full sign cube
allows the finite averaging identity to cover arbitrary packet subsets. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open MeasureTheory Filter Set
open scoped ENNReal Classical BigOperators

namespace SurveyStatements.P5OperatorReduction
open SurveyStatements.P5 SurveyStatements.P5Support
variable {𝕜 : Type*} [RCLike 𝕜]

theorem sum_mask_eq {Ω X : Type*} [Fintype Ω] [DecidableEq Ω] [AddCommMonoid X]
    (S : Finset Ω) (v : Ω → X) :
    (∑ i, if i ∈ S then v i else 0) = ∑ i ∈ S, v i := by
  calc
    _ = ∑ i ∈ S, if i ∈ S then v i else 0 :=
      (Finset.sum_subset (Finset.subset_univ S)
        (fun i _ hi => if_neg hi)).symm
    _ = _ := Finset.sum_congr rfl (fun i hi => if_pos hi)

theorem sum_signed_mask_eq {Ω X : Type*} [Fintype Ω] [DecidableEq Ω] [AddCommGroup X]
    (S : Finset Ω) (v : Ω → X) (θ : Ω → Bool) :
    (∑ i, signedValue (θ i) (if i ∈ S then v i else 0)) =
      ∑ i ∈ S, signedValue (θ i) (v i) := by
  have hterm (i : Ω) : signedValue (θ i) (if i ∈ S then v i else 0) =
      if i ∈ S then signedValue (θ i) (v i) else 0 := by
    by_cases hi : i ∈ S <;> simp [hi, signedValue]
  simp_rw [hterm]
  exact sum_mask_eq S _

def haarPacketWeight (n : ℕ) (k : Fin (2 ^ n)) : ℝ → 𝕜 :=
  lpHaarFunction 𝕜 (lpHaarCell (n + 1) (2 * k.val))
    (lpHaarCell (n + 1) (2 * k.val + 1))

theorem haarPacketWeight_stronglyMeasurable (n : ℕ) (k : Fin (2 ^ n)) :
    StronglyMeasurable (haarPacketWeight (𝕜 := 𝕜) n k) := by
  unfold haarPacketWeight lpHaarFunction
  exact (stronglyMeasurable_const.indicator measurableSet_Ioc).sub
    (stronglyMeasurable_const.indicator measurableSet_Ioc)

theorem haarPacketWeight_norm_le (n : ℕ) (k : Fin (2 ^ n)) (x : ℝ) :
    ‖haarPacketWeight (𝕜 := 𝕜) n k x‖ ≤ 1 := by
  unfold haarPacketWeight
  rw [lpHaarFunction_norm _ _ (lpHaarCell_disjoint_sameLevel (n + 1) (by omega))]
  by_cases hx : x ∈ lpHaarCell (n + 1) (2 * k.val) ∪
      lpHaarCell (n + 1) (2 * k.val + 1) <;> simp [hx]

def maskedHaarPacketWeight (n : ℕ) (S : Finset (Fin (2 ^ n)))
    (k : Fin (2 ^ n)) (x : ℝ) : 𝕜 :=
  if k ∈ S then haarPacketWeight n k x else 0

theorem maskedHaarPacketWeight_stronglyMeasurable (n : ℕ)
    (S : Finset (Fin (2 ^ n))) (k : Fin (2 ^ n)) :
    StronglyMeasurable (maskedHaarPacketWeight (𝕜 := 𝕜) n S k) := by
  change StronglyMeasurable (fun x : ℝ =>
    if k ∈ S then haarPacketWeight (𝕜 := 𝕜) n k x else 0)
  by_cases hk : k ∈ S
  · simpa only [maskedHaarPacketWeight, if_pos hk] using
      haarPacketWeight_stronglyMeasurable (𝕜 := 𝕜) n k
  · simpa only [maskedHaarPacketWeight, if_neg hk] using
      (stronglyMeasurable_const : StronglyMeasurable (fun _ : ℝ => (0 : 𝕜)))

theorem maskedHaarPacketWeight_norm_le (n : ℕ)
    (S : Finset (Fin (2 ^ n))) (k : Fin (2 ^ n)) (x : ℝ) :
    ‖maskedHaarPacketWeight (𝕜 := 𝕜) n S k x‖ ≤ 1 := by
  by_cases hk : k ∈ S
  · simpa only [maskedHaarPacketWeight, if_pos hk] using
      haarPacketWeight_norm_le (𝕜 := 𝕜) n k x
  · simp only [maskedHaarPacketWeight, if_neg hk, norm_zero, zero_le_one]

def maskedHaarPacketVector (p : BanachExponent) (n : ℕ)
    (S : Finset (Fin (2 ^ n))) (k : Fin (2 ^ n)) : IntervalLp 𝕜 p :=
  if k ∈ S then lpHaarDyadic 𝕜 p n k else 0

theorem rawPacketFunction_signed_mask (n : ℕ) (S : Finset (Fin (2 ^ n)))
    (θ : Fin (2 ^ n) → Bool) (x : ℝ) :
    operatorReductionRawPacketFunction n S (fun k => scalarSign (θ k)) x =
      ∑ k, signedValue (θ k) (maskedHaarPacketWeight (𝕜 := 𝕜) n S k x) := by
  unfold maskedHaarPacketWeight
  rw [sum_signed_mask_eq]
  unfold operatorReductionRawPacketFunction haarPacketWeight
  exact Finset.sum_congr rfl (fun k _ => scalarSign_mul (θ k) _)

theorem rawHaarPacket_signed_mask (p : BanachExponent) (n : ℕ)
    (S : Finset (Fin (2 ^ n))) (θ : Fin (2 ^ n) → Bool) :
    operatorReductionRawHaarPacket 𝕜 p n S (fun k => scalarSign (θ k)) =
      ∑ k, signedValue (θ k) (maskedHaarPacketVector (𝕜 := 𝕜) p n S k) := by
  unfold maskedHaarPacketVector
  rw [sum_signed_mask_eq]
  unfold operatorReductionRawHaarPacket
  apply Finset.sum_congr rfl
  intro k _
  cases hθ : θ k <;> simp [scalarSign, signedValue, hθ]

theorem rawHaarPacket_input_signed_mask (p : BanachExponent) (n : ℕ)
    (S : Finset (Fin (2 ^ n))) (θ : Fin (2 ^ n) → Bool)
    (T : MixedNorm 𝕜 p.val →L[𝕜] MixedNorm 𝕜 p.val)
    (g : Lp 𝕜 1 unitIntervalMeasure) :
    T (tensorWith g (operatorReductionRawHaarPacket 𝕜 p n S
      (fun k => scalarSign (θ k)))) =
      ∑ k, signedValue (θ k) (T (tensorWith g
        (maskedHaarPacketVector (𝕜 := 𝕜) p n S k))) := by
  rw [rawHaarPacket_signed_mask, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_signedValue, map_signedValue]

end SurveyStatements.P5OperatorReduction

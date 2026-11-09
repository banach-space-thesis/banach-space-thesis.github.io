import SurveyStatements.P5HaarSeparation
import SurveyStatements.P5Support.LpHaarDiagonalBounds

/-! Uniform bounds for the actual Haar coordinates times their vector norms.
These give bounded product-Haar diagonals for arbitrary bounded operators. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 100000
open MeasureTheory
open scoped ENNReal

namespace SurveyStatements.P5

variable (𝕜 : Type*) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)]

theorem norm_dyadicHaarCoordinate_mul_norm_le (hp : p ≠ ∞) (I : DyadicIndex) :
    ‖dyadicHaarCoordinate 𝕜 p I‖ * ‖dyadicHaar 𝕜 p I‖ ≤ 6 := by
  let q : P5Support.BanachExponent := ⟨p, Fact.out⟩
  let i : Option P5Support.LpHaarTreeIndex := some I
  have he : P5Support.lpHaarIndexEquiv (P5Support.lpHaarEncode i) = i :=
    P5Support.lpHaarDecode_encode i
  have h := P5Support.intervalLpHaarBasis_coord_norm_le 𝕜 q hp
    (P5Support.lpHaarEncode i)
  change ‖P5Support.lpHaarNormalizedCoordinate 𝕜 q
    (P5Support.lpHaarIndexEquiv (P5Support.lpHaarEncode i))‖ ≤ 6 at h
  rw [he] at h
  change ‖((‖P5Support.lpHaarDyadic 𝕜 q I.1 I.2‖ : ℝ) : 𝕜) •
    P5Support.lpHaarDyadicCoefficient 𝕜 q I.1 I.2‖ ≤ 6 at h
  rw [norm_smul, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _)] at h
  rw [dyadicHaarCoordinate_eq_support, dyadicHaar_eq_support, mul_comm]
  exact h

theorem norm_productHaarCoordinate_mul_norm_le (hp : p ≠ ∞) (I J : DyadicIndex) :
    ‖productHaarCoordinate 𝕜 p I J‖ * ‖productHaar 𝕜 p I J‖ ≤ 36 := by
  have hI := norm_dyadicHaarCoordinate_mul_norm_le 𝕜 p hp I
  have hJ := norm_dyadicHaarCoordinate_mul_norm_le 𝕜 1 (by norm_num) J
  have hc : ‖productHaarCoordinate 𝕜 p I J‖ ≤
      ‖dyadicHaarCoordinate 𝕜 p I‖ * ‖dyadicHaarCoordinate 𝕜 1 J‖ := by
    calc
      _ ≤ ‖dyadicHaarCoordinate 𝕜 p I‖ *
          ‖(dyadicHaarCoordinate 𝕜 1 J).compLpL p unitIntervalMeasure‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (ContinuousLinearMap.norm_compLpL_le _) (norm_nonneg _)
  calc
    _ ≤ (‖dyadicHaarCoordinate 𝕜 p I‖ * ‖dyadicHaarCoordinate 𝕜 1 J‖) *
        ‖productHaar 𝕜 p I J‖ := mul_le_mul_of_nonneg_right hc (norm_nonneg _)
    _ = (‖dyadicHaarCoordinate 𝕜 p I‖ * ‖dyadicHaar 𝕜 p I‖) *
        (‖dyadicHaarCoordinate 𝕜 1 J‖ * ‖dyadicHaar 𝕜 1 J‖) := by
      rw [productHaar, norm_tensorWith]
      ring
    _ ≤ 6 * 6 := mul_le_mul hI hJ (by positivity) (by norm_num)
    _ = 36 := by norm_num

theorem productHaar_operator_diagonal_norm_le (hp : p ≠ ∞)
    (T : MixedNorm 𝕜 p →L[𝕜] MixedNorm 𝕜 p) (I J : DyadicIndex) :
    ‖productHaarCoordinate 𝕜 p I J (T (productHaar 𝕜 p I J))‖ ≤ 36 * ‖T‖ := by
  calc
    _ ≤ ‖productHaarCoordinate 𝕜 p I J‖ * ‖T (productHaar 𝕜 p I J)‖ :=
      (productHaarCoordinate 𝕜 p I J).le_opNorm _
    _ ≤ ‖productHaarCoordinate 𝕜 p I J‖ * (‖T‖ * ‖productHaar 𝕜 p I J‖) :=
      mul_le_mul_of_nonneg_left (T.le_opNorm (productHaar 𝕜 p I J)) (norm_nonneg _)
    _ = (‖productHaarCoordinate 𝕜 p I J‖ * ‖productHaar 𝕜 p I J‖) * ‖T‖ := by ring
    _ ≤ 36 * ‖T‖ := mul_le_mul_of_nonneg_right
      (norm_productHaarCoordinate_mul_norm_le 𝕜 p hp I J) (norm_nonneg _)

def cancellativeHaar (I J : DyadicIndex) : DoublyZeroMean 𝕜 p :=
  ⟨productHaar 𝕜 p I J, productHaar_mem_doublyZeroMean 𝕜 p I J⟩

def cancellativeHaarCoordinate (I J : DyadicIndex) : DoublyZeroMean 𝕜 p →L[𝕜] 𝕜 :=
  (productHaarCoordinate 𝕜 p I J).comp (DoublyZeroMean 𝕜 p).subtypeL

theorem norm_cancellativeHaarCoordinate_le (I J : DyadicIndex) :
    ‖cancellativeHaarCoordinate 𝕜 p I J‖ ≤ ‖productHaarCoordinate 𝕜 p I J‖ := by
  calc
    _ ≤ ‖productHaarCoordinate 𝕜 p I J‖ * ‖(DoublyZeroMean 𝕜 p).subtypeL‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖productHaarCoordinate 𝕜 p I J‖ * 1 := mul_le_mul_of_nonneg_left
      (Submodule.norm_subtypeL_le _) (norm_nonneg _)
    _ = _ := mul_one _

theorem cancellativeHaarCoordinate_biorthogonal (hp : p ≠ ∞)
    (I J K L : DyadicIndex) :
    cancellativeHaarCoordinate 𝕜 p I J (cancellativeHaar 𝕜 p K L) =
      if (I, J) = (K, L) then 1 else 0 :=
  productHaarCoordinate_biorthogonal hp I J K L

theorem cancellativeHaar_operator_diagonal_norm_le (hp : p ≠ ∞)
    (T : DoublyZeroMean 𝕜 p →L[𝕜] DoublyZeroMean 𝕜 p) (I J : DyadicIndex) :
    ‖cancellativeHaarCoordinate 𝕜 p I J (T (cancellativeHaar 𝕜 p I J))‖ ≤
      36 * ‖T‖ := by
  letI : NormedSpace 𝕜 (DoublyZeroMean 𝕜 p) := inferInstance
  have hnorm : ‖cancellativeHaar 𝕜 p I J‖ = ‖productHaar 𝕜 p I J‖ := rfl
  calc
    _ ≤ ‖cancellativeHaarCoordinate 𝕜 p I J‖ * ‖T (cancellativeHaar 𝕜 p I J)‖ :=
      (cancellativeHaarCoordinate 𝕜 p I J).le_opNorm _
    _ ≤ ‖cancellativeHaarCoordinate 𝕜 p I J‖ *
        (‖T‖ * ‖cancellativeHaar 𝕜 p I J‖) :=
      mul_le_mul_of_nonneg_left (T.le_opNorm (cancellativeHaar 𝕜 p I J))
        (norm_nonneg (cancellativeHaarCoordinate 𝕜 p I J))
    _ ≤ ‖productHaarCoordinate 𝕜 p I J‖ * (‖T‖ * ‖productHaar 𝕜 p I J‖) := by
      rw [hnorm]
      exact mul_le_mul_of_nonneg_right
        (norm_cancellativeHaarCoordinate_le 𝕜 p I J) (by positivity)
    _ = (‖productHaarCoordinate 𝕜 p I J‖ * ‖productHaar 𝕜 p I J‖) * ‖T‖ := by ring
    _ ≤ 36 * ‖T‖ := mul_le_mul_of_nonneg_right
      (norm_productHaarCoordinate_mul_norm_le 𝕜 p hp I J) (norm_nonneg T)

end SurveyStatements.P5

import SurveyStatements.P5OperatorReductionOuterShadowCoefficients
import SurveyStatements.P5OperatorReductionOuterShadowTraceGeometry
import SurveyStatements.P5OperatorReductionInnerSlices
import SurveyStatements.P5OperatorReductionOuterShadowBounds

/-! Full-sequence scalar limits of the actual inner-averaged outer
operators. The limit is the actual local L1 trace of the genuine slice. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal Classical BigOperators Topology
namespace SurveyStatements.P5OperatorReduction
open SurveyStatements.P5 SurveyStatements.P5Support SurveyStatements.P5L1Variation
variable {𝕜 : Type*} [RCLike 𝕜]

theorem meanZeroInnerSlice_haarDiagonal (p : BanachExponent)
    (T : MixedNorm 𝕜 p.val →L[𝕜] MixedNorm 𝕜 p.val)
    (f : Lp 𝕜 p.val (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (η : ℝ → 𝕜) (hη : StronglyMeasurable η) (hb : ∀ x, ‖η x‖ ≤ 1)
    (n : ℕ) (k : Fin (2 ^ n)) :
    haarOperatorDiagonal 𝕜
      (extendMeanZero 𝕜 (meanZeroInnerSlice T f η hη hb)) n k =
      lpHaarDyadicCoefficient 𝕜 outerShadowL1Exponent n k
        (innerSliceOperator T f η hη hb
          (lpHaarDyadic 𝕜 outerShadowL1Exponent n k)) := by
  rw [haarOperatorDiagonal_on_meanZero]
  change lpHaarDyadicCoefficient 𝕜 ⟨1, le_rfl⟩ n k
    (intervalLpMeanZeroProjection 𝕜 ⟨1, le_rfl⟩
      (innerSliceOperator T f η hη hb (lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ n k))).val = _
  exact rawL1HaarCoefficient_meanZeroProjection n k _

theorem outerHaarPacketShadow_descendants_weightedReader (p : BanachExponent)
    (T : MixedNorm 𝕜 p.val →L[𝕜] MixedNorm 𝕜 p.val)
    (f : Lp 𝕜 p.val (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (η : ℝ → 𝕜) (hη : StronglyMeasurable η) (hb : ∀ x, ‖η x‖ ≤ 1)
    (r : ℕ) (S : Finset (Fin (2 ^ r))) (j : ℕ) :
    weightedOuterReader (𝕜 := 𝕜) (E := 𝕜) (p := p.val) η hη hb
      (outerHaarPacketShadow p T (r + j) (shadowDescendants r S j) f) =
      equalDyadicLevelAverage 𝕜 (meanZeroInnerSlice T f η hη hb) r S j := by
  rw [outerHaarPacketShadow_weightedReader_coefficient,
    equalDyadicLevelAverage_eq_shadowDescendants]
  apply congrArg (fun z : 𝕜 => ((shadowDescendants r S j).card : 𝕜)⁻¹ * z)
  apply Finset.sum_congr rfl
  intro k _
  exact (meanZeroInnerSlice_haarDiagonal p T f η hη hb (r + j) k).symm

theorem outerHaarPacketShadow_localTrace_tendsto (p : BanachExponent)
    (T : MixedNorm 𝕜 p.val →L[𝕜] MixedNorm 𝕜 p.val)
    (f : Lp 𝕜 p.val (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (η : ℝ → 𝕜) (hη : StronglyMeasurable η) (hb : ∀ x, ‖η x‖ ≤ 1)
    (r : ℕ) (S : Finset (Fin (2 ^ r))) :
    Tendsto (fun j => weightedOuterReader (𝕜 := 𝕜) (E := 𝕜) (p := p.val) η hη hb
        (outerHaarPacketShadow p T (r + j) (shadowDescendants r S j) f)) atTop
      (𝓝 (localTraceFunctional 𝕜 r S (meanZeroInnerSlice T f η hη hb))) := by
  simp_rw [outerHaarPacketShadow_descendants_weightedReader]
  exact localTraceFunctional_tendsto 𝕜 (meanZeroInnerSlice T f η hη hb) r S

/-- Every absolute-level reservoir preserves the same scalar local trace. -/
theorem outerHaarPacketShadow_localTrace_reservoir_tendsto (p : BanachExponent)
    (T : MixedNorm 𝕜 p.val →L[𝕜] MixedNorm 𝕜 p.val)
    (f : Lp 𝕜 p.val (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (η : ℝ → 𝕜) (hη : StronglyMeasurable η) (hb : ∀ x, ‖η x‖ ≤ 1)
    (r : ℕ) (S : Finset (Fin (2 ^ r))) (σ : ℕ → ℕ)
    (hσ : Tendsto σ atTop atTop) :
    Tendsto (fun j => weightedOuterReader (𝕜 := 𝕜) (E := 𝕜) (p := p.val) η hη hb
        (outerHaarPacketShadow p T (r + σ j) (shadowDescendants r S (σ j)) f)) atTop
      (𝓝 (localTraceFunctional 𝕜 r S (meanZeroInnerSlice T f η hη hb))) :=
  (outerHaarPacketShadow_localTrace_tendsto p T f η hη hb r S).comp hσ

theorem norm_innerSliceLocalTrace_le (p : BanachExponent)
    (T : MixedNorm 𝕜 p.val →L[𝕜] MixedNorm 𝕜 p.val)
    (f : Lp 𝕜 p.val (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (η : ℝ → 𝕜) (hη : StronglyMeasurable η) (hb : ∀ x, ‖η x‖ ≤ 1)
    (r : ℕ) (S : Finset (Fin (2 ^ r))) :
    ‖localTraceFunctional 𝕜 r S (meanZeroInnerSlice T f η hη hb)‖ ≤ ‖T‖ * ‖f‖ := by
  apply le_of_tendsto (outerHaarPacketShadow_localTrace_tendsto p T f η hη hb r S).norm
  apply Eventually.of_forall
  intro j
  calc
    _ ≤ ‖outerHaarPacketShadow p T (r + j) (shadowDescendants r S j) f‖ :=
      contraction_apply_bound (𝕜 := 𝕜) (X := Lp 𝕜 p.val (volume.restrict (Set.Icc (0 : ℝ) 1)))
        (Y := 𝕜) (weightedOuterReader (𝕜 := 𝕜) (E := 𝕜) (p := p.val) η hη hb)
        (norm_weightedOuterReader_le (E := 𝕜) (p := p.val) η hη hb) _
    _ ≤ ‖T‖ * ‖f‖ :=
      ((outerHaarPacketShadow p T (r + j) (shadowDescendants r S j)).le_opNorm f).trans
        (mul_le_mul_of_nonneg_right
          (norm_outerHaarPacketShadow_le p T (r + j) (shadowDescendants r S j))
          (norm_nonneg f))

end SurveyStatements.P5OperatorReduction

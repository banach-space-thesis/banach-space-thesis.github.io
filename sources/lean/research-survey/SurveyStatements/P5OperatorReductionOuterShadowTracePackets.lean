import SurveyStatements.P5OperatorReductionOuterShadowTraceValues
import SurveyStatements.P5Support.LpHaarTraceSplitSelection

/-! Exact physical-parent traces of arbitrary actual raw inner packets.
This applies to any refining packet representation of a fixed parent. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal Classical BigOperators Topology
namespace SurveyStatements.P5OperatorReduction
open SurveyStatements.P5 SurveyStatements.P5Support SurveyStatements.P5L1Variation
variable {𝕜 : Type*} [RCLike 𝕜]

theorem outerHaarPacketShadow_weightedReader_parent_trace (p : BanachExponent)
    (T : MixedNorm 𝕜 p.val →L[𝕜] MixedNorm 𝕜 p.val)
    (f : Lp 𝕜 p.val (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (η : ℝ → 𝕜) (hη : StronglyMeasurable η) (hb : ∀ x, ‖η x‖ ≤ 1)
    (n : ℕ) (S : Finset (Fin (2 ^ n))) :
    weightedOuterReader (𝕜 := 𝕜) (E := 𝕜) (p := p.val) η hη hb
      (outerHaarPacketShadow p T n S f) =
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).real (lpHaarBlockParent n S) : 𝕜)⁻¹ *
        lpHaarLevelTrace
          (haarOperatorDiagonal 𝕜 (extendMeanZero 𝕜 (meanZeroInnerSlice T f η hη hb)))
          n (lpHaarBlockParent n S) := by
  rw [outerHaarPacketShadow_weightedReader, outerShadowParentMass_eq_real_measure,
    smul_eq_mul, lpHaarLevelTrace_parent]
  apply congrArg (fun z : 𝕜 =>
    ((volume.restrict (Set.Icc (0 : ℝ) 1)).real (lpHaarBlockParent n S) : 𝕜)⁻¹ * z)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [scalarHaarPacketReader_eq_radius_coefficient,
    meanZeroInnerSlice_haarDiagonal p T f η hη hb n k]
  rfl

theorem outerHaarPacketShadow_fixed_parent_tendsto (p : BanachExponent)
    (T : MixedNorm 𝕜 p.val →L[𝕜] MixedNorm 𝕜 p.val)
    (f : Lp 𝕜 p.val (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (η : ℝ → 𝕜) (hη : StronglyMeasurable η) (hb : ∀ x, ‖η x‖ ≤ 1)
    (r : ℕ) (B : Finset (Fin (2 ^ r))) (hB : B.Nonempty)
    (σ : ℕ → ℕ) (hσ : Tendsto σ atTop atTop)
    (S : ∀ j, Finset (Fin (2 ^ σ j)))
    (hparent : ∀ j, lpHaarBlockParent (σ j) (S j) = lpHaarBlockParent r B) :
    Tendsto (fun j => weightedOuterReader (𝕜 := 𝕜) (E := 𝕜) (p := p.val) η hη hb
      (outerHaarPacketShadow p T (σ j) (S j) f)) atTop
      (𝓝 (localTraceFunctional 𝕜 r B (meanZeroInnerSlice T f η hη hb))) := by
  have hmass : 0 < (volume.restrict (Set.Icc (0 : ℝ) 1)).real (lpHaarBlockParent r B) := by
    rw [lpHaarBlockParent_real_measure]
    exact mul_pos (by exact_mod_cast Finset.card_pos.mpr hB)
      (intervalLpDyadicRadius_pos r)
  have hmass𝕜 : ((volume.restrict (Set.Icc (0 : ℝ) 1)).real (lpHaarBlockParent r B) : 𝕜) ≠ 0 :=
    RCLike.ofReal_ne_zero.mpr hmass.ne'
  have hend :
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).real (lpHaarBlockParent r B) : 𝕜)⁻¹ *
        innerSliceDyadicTraceValue p T f η hη hb ⟨r, B⟩ =
      localTraceFunctional 𝕜 r B (meanZeroInnerSlice T f η hη hb) := by
    rw [innerSliceDyadicTraceValue, lpHaarDyadicSet, ← mul_assoc,
      inv_mul_cancel₀ hmass𝕜, one_mul]
  have hlim := (tendsto_const_nhds (x :=
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).real (lpHaarBlockParent r B) : 𝕜)⁻¹)).mul
    (innerSliceDyadicTraceValue_reservoir_tendsto p T f η hη hb ⟨r, B⟩ σ hσ)
  rw [hend] at hlim
  convert hlim using 1
  funext j
  rw [outerHaarPacketShadow_weightedReader_parent_trace, hparent j]
  rfl

end SurveyStatements.P5OperatorReduction

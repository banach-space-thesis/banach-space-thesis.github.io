import PEMS.UniformTruncationLowerBound
import ThesisCommon.Analysis.L1LocalizedAdjointCuts

/-! A common fixed truncation threshold controls every finite-input contraction
of an arbitrary ambient operator by its actual localized small-cut supremum. -/
noncomputable section
open MeasureTheory Set Filter ThesisCommon
open scoped ENNReal ThesisCommon.PositiveOperatorOrder
namespace PEMS
variable {X X' Y : Type*} [MeasurableSpace X] [MeasurableSpace X'] [MeasurableSpace Y]
variable {μ : Measure X} {μ' : Measure X'} {ν : Measure Y} [IsFiniteMeasure μ']

theorem localized_truncation_le_smallSetSup_of_input_contraction
    (T : LOne ℝ μ →L[ℝ] LOne ℝ ν) (J : LOne ℝ μ' →L[ℝ] LOne ℝ μ)
    (hJ : ‖J‖ ≤ 1) (hTJ : 0 ≤ T.comp J)
    (Θ : Set Y) (hΘ : MeasurableSet Θ) [IsFiniteMeasure (ν.restrict Θ)]
    {k : X' × Y → ℝ} (hk : IsIntegralKernel k (localizedIntegralPart Θ (T.comp J)))
    (hpos : ∀ z, 0 ≤ k z) {C δ r : ℝ} (hC : 0 ≤ C)
    (hKC : ‖localizedIntegralPart Θ (T.comp J)‖ ≤ C)
    (hδ : 0 < δ) (hr : 0 < r) (hsize : 2 * C / r < δ) :
    ‖localizedIntegralRemainder Θ hΘ (T.comp J) +
      (lebesgueLpExtend (𝕜 := ℝ) Θ hΘ).toContinuousLinearMap.comp (hk.truncatedOperator r)‖ ≤
        smallSetSup T Θ δ := by
  let Q := T.comp J
  let O := (lpCutL Θᶜ hΘ.compl).comp Q
  let R := (lebesgueLpRestrict (𝕜 := ℝ) Θ).comp Q
  let K := localizedIntegralPart Θ Q
  let S := R - K
  have hO : 0 ≤ O := positive_outputCut_nonneg hTJ Θᶜ hΘ.compl
  have hK : 0 ≤ K := localizedIntegralPart_nonneg Θ hTJ
  have hS : 0 ≤ S := sub_nonneg.mpr (localizedIntegralPart_le_restrict Θ hTJ)
  have hSing : IsSingularOperator S := integralBandProjection_residual_singular R
  have hSK : S + K = R := sub_add_cancel _ _
  have hb : HasKernelBound μ' (ν.restrict Θ) k C := by
    filter_upwards [hk.hasKernelBound_sigmaFinite] with x hx
    exact ⟨hx.1, hx.2.trans hKC⟩
  have hq : 0 ≤ smallSetSup T Θ δ := (smallSetSup_bounds T Θ hΘ δ hδ).1
  have hmass := positive_singular_kernel_tail_le_of_smallCuts S K hS hSing hk hpos
    (positiveAdjointOneDensity O hO) (measurable_positiveAdjointOneDensity O hO) hC hb hr hsize
    (q := smallSetSup T Θ δ) (by
      intro B hB hBδ
      have hνB : ν (B ∩ Θ) < ENNReal.ofReal δ := by
        rw [← Measure.restrict_apply hB]
        apply (ENNReal.toReal_lt_toReal (measure_ne_top (ν.restrict Θ) B) ENNReal.ofReal_ne_top).mp
        simpa only [measureReal_def, ENNReal.toReal_ofReal hδ.le] using hBδ
      have hcut := cutOperatorNorm_le_smallSetSup T Θ hΘ (hB.inter hΘ) inter_subset_right hνB
      rw [cutOperatorNorm_eq _ _ (hΘ.compl.union (hB.inter hΘ))] at hcut
      have hn : ‖O + (lebesgueLpExtend (𝕜 := ℝ) Θ hΘ).toContinuousLinearMap.comp
          ((lpCutL B hB).comp (S + K))‖ ≤ smallSetSup T Θ δ := by
        rw [hSK]
        change ‖(lpCutL Θᶜ hΘ.compl).comp Q +
          (lebesgueLpExtend (𝕜 := ℝ) Θ hΘ).toContinuousLinearMap.comp
            ((lpCutL B hB).comp ((lebesgueLpRestrict (𝕜 := ℝ) Θ).comp Q))‖ ≤ _
        rw [lOne_localized_cut_decomposition]
        calc
          _ ≤ ‖(lpCutL (Θᶜ ∪ (B ∩ Θ)) (hΘ.compl.union (hB.inter hΘ))).comp T‖ * ‖J‖ :=
            ContinuousLinearMap.opNorm_comp_le _ _
          _ ≤ ‖(lpCutL (Θᶜ ∪ (B ∩ Θ)) (hΘ.compl.union (hB.inter hΘ))).comp T‖ := by
            nlinarith [norm_nonneg ((lpCutL (Θᶜ ∪ (B ∩ Θ))
              (hΘ.compl.union (hB.inter hΘ))).comp T)]
          _ ≤ _ := hcut
      have hp := positive_outputCut_nonneg (add_nonneg hS hK) B hB
      have hd := positiveAdjointOneDensity_add_extend Θ hΘ hO hp
      have hn' := (norm_positive_le_iff_adjointDensity
        (add_nonneg hO (lebesgueL1Extend_comp_nonneg Θ hΘ hp)) hq).mp hn
      filter_upwards [hd, hn'] with x hx hn
      simpa only [hx] using hn)
  have hrem := localizedIntegralRemainder_nonneg Θ hΘ hTJ
  have hdrem := positiveAdjointOneDensity_congr hrem
    (add_nonneg hO (lebesgueL1Extend_comp_nonneg Θ hΘ hS))
    (localizedIntegralRemainder_eq_outside_add_extend Θ hΘ Q)
  have hd := positiveAdjointOneDensity_add_extend Θ hΘ hO hS
  rw [← hdrem] at hd
  have htrpos : ∀ z, 0 ≤ truncatedKernel r k z :=
    fun z => indicator_nonneg (fun w _ => hpos w) z
  have htr := (hk.truncatedOperator_represents r).positive_of_nonneg_ae (Eventually.of_forall htrpos)
  apply (norm_positive_add_extended_integral_le_iff Θ hΘ hrem htr
    (hk.truncatedOperator_represents r) hq).mpr
  filter_upwards [hmass, hd] with x hx hdx
  rw [hdx]
  simpa only [Real.norm_of_nonneg (htrpos _)] using hx

end PEMS

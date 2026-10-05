import PEMS.L1WeakNoncompactness
import ThesisCommon.Analysis.PositiveKernelApproximation

/-! The full quantitative norm formula for positive real operators on the
compact standard models. Best attainment and the full paper scope remain
separate assertions. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter ThesisCommon
open scoped ENNReal ProbabilityTheory ThesisCommon.PositiveOperatorOrder
namespace PEMS
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable [CompactSpace X] [CompactSpace Y] [T2Space X] [T2Space Y]
variable [TotallyDisconnectedSpace X] [TotallyDisconnectedSpace Y]
variable [SecondCountableTopology X] [SecondCountableTopology Y]
variable [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
variable [StandardBorelSpace Y]
variable {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [IsFiniteMeasure ν]

theorem positive_truncation_inf_le_alphaTheta
    (T : LOne ℝ μ →L[ℝ] LOne ℝ ν) (hT : 0 ≤ T)
    (κ : Kernel X Y) [IsFiniteKernel κ]
    (hrepr : μ ⊗ₘ κ = clopenOperatorMeasure T hT)
    (hk : IsIntegralKernel (kernelRealDensity κ ν) (integralBandProjection T)) :
    sInf (Set.range (fun n : ℕ =>
      ‖T - integralBandProjection T + hk.truncatedOperator n‖)) ≤ alphaTheta T univ := by
  apply le_csInf
  · exact ⟨_, 1, zero_lt_one, rfl⟩
  · rintro _ ⟨δ, hδ, rfl⟩
    have hcut : ∀ (B : Set Y) (hB : MeasurableSet B), ν.real B < δ →
        ‖(lpCutL B hB).comp T‖ ≤ smallSetSup T univ δ := by
      intro B hB hBδ
      have hμB : ν B < ENNReal.ofReal δ :=
        (ENNReal.toReal_lt_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
          (by simpa only [ENNReal.toReal_ofReal hδ.le] using hBδ)
      simpa only [compl_univ, empty_union, cutOperatorNorm_eq T B hB] using
        cutOperatorNorm_le_smallSetSup T univ MeasurableSet.univ hB (subset_univ B) hμB
    obtain ⟨n, hn⟩ := exists_nat_truncated_remainder_le_of_smallCuts T hT κ hrepr hk hδ
      (smallSetSup_bounds T univ MeasurableSet.univ δ hδ).1 hcut
    exact (csInf_le ⟨0, by rintro _ ⟨n, rfl⟩; exact norm_nonneg _⟩
      (Set.mem_range_self n)).trans hn

theorem positive_standard_weis_norm_formula
    (T : LOne ℝ μ →L[ℝ] LOne ℝ ν) (hT : 0 ≤ T)
    (κ : Kernel X Y) [IsFiniteKernel κ]
    (hrepr : μ ⊗ₘ κ = clopenOperatorMeasure T hT)
    (hk : IsIntegralKernel (kernelRealDensity κ ν) (integralBandProjection T)) :
    weakEssentialNorm T = localizedWeakNoncompactness T ∧
    weakEssentialNorm T = sInf (Set.range (fun n : ℕ =>
      ‖T - integralBandProjection T + hk.truncatedOperator n‖)) := by
  have hlo := localizedWeakNoncompactness_le_weakEssentialNorm T
  have hmid := positive_truncation_inf_le_alphaTheta T hT κ hrepr hk
  rw [← localizedWeakNoncompactness_eq_alphaTheta_univ T] at hmid
  have hu : weakEssentialNorm T ≤ sInf (Set.range (fun n : ℕ =>
      ‖T - integralBandProjection T + hk.truncatedOperator n‖)) := by
    simpa only [sub_add_cancel] using weakEssentialNorm_le_truncation_inf hk
      (T - integralBandProjection T)
  exact ⟨le_antisymm (hu.trans hmid) hlo, le_antisymm hu (hmid.trans hlo)⟩

theorem weakEssentialNorm_eq_localized_positive_standard
    (T : LOne ℝ μ →L[ℝ] LOne ℝ ν) (hT : 0 ≤ T) :
    weakEssentialNorm T = localizedWeakNoncompactness T := by
  obtain ⟨κ, hκ, _, hrepr, hk⟩ := exists_positive_operator_kernel_parts T hT
  letI := hκ
  exact (positive_standard_weis_norm_formula T hT κ hrepr hk).1

end PEMS

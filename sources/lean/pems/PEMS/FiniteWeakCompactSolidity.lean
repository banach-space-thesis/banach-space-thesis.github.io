import PEMS.FiniteWeisFormula
import PEMS.L1WeakNoncompactnessGeneral
import ThesisCommon.Analysis.WeakCalkinNorm

/-! Weak compactness is solid for actual real L1 operators on finite measure
spaces. This follows from monotonicity of the small-set functional and the
proved real Weis formula, rather than assuming solidity of the ideal. -/
noncomputable section
open MeasureTheory Set ThesisCommon
open scoped ENNReal ThesisCommon.PositiveOperatorOrder
namespace PEMS
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}

theorem cutOperatorNorm_le_of_abs_le
    {S H : LOne ℝ μ →L[ℝ] LOne ℝ ν} (hSH : |S| ≤ H)
    (B : Set Y) (hB : MeasurableSet B) :
    cutOperatorNorm S B ≤ cutOperatorNorm H B := by
  have hH : 0 ≤ H := (abs_nonneg S).trans hSH
  rw [cutOperatorNorm_eq S B hB, cutOperatorNorm_eq H B hB]
  apply norm_le_norm_of_abs_le_abs
  rw [abs_outputCut_lOneOperator, abs_outputCut_lOneOperator, abs_of_nonneg hH]
  intro f hf
  exact lOneCut_mono B hB (hSH f hf)

theorem smallSetSup_le_of_abs_le
    {S H : LOne ℝ μ →L[ℝ] LOne ℝ ν} (hSH : |S| ≤ H)
    (Θ : Set Y) (hΘ : MeasurableSet Θ) {δ : ℝ} (hδ : 0 < δ) :
    smallSetSup S Θ δ ≤ smallSetSup H Θ δ := by
  apply csSup_le
  · refine ⟨_, ∅, MeasurableSet.empty, empty_subset _, ?_, rfl⟩
    simpa using ENNReal.ofReal_pos.mpr hδ
  · rintro q ⟨B, hB, hsub, hsmall, rfl⟩
    exact (cutOperatorNorm_le_of_abs_le hSH _ (hΘ.compl.union hB)).trans
      (cutOperatorNorm_le_smallSetSup H Θ hΘ hB hsub hsmall)

theorem alphaTheta_le_of_abs_le
    {S H : LOne ℝ μ →L[ℝ] LOne ℝ ν} (hSH : |S| ≤ H)
    (Θ : Set Y) (hΘ : MeasurableSet Θ) : alphaTheta S Θ ≤ alphaTheta H Θ := by
  apply le_csInf
  · exact ⟨_, 1, zero_lt_one, rfl⟩
  · rintro q ⟨δ, hδ, rfl⟩
    exact (alphaTheta_le_smallSetSup S Θ hΘ hδ).trans
      (smallSetSup_le_of_abs_le hSH Θ hΘ hδ)

theorem localizedWeakNoncompactness_le_of_abs_le
    {S H : LOne ℝ μ →L[ℝ] LOne ℝ ν} (hSH : |S| ≤ H) :
    localizedWeakNoncompactness S ≤ localizedWeakNoncompactness H := by
  apply le_csInf
  · exact ⟨_, ∅, MeasurableSet.empty, by simp, rfl⟩
  · rintro q ⟨Θ, hΘ, hfin, rfl⟩
    exact (localizedWeakNoncompactness_le_alphaTheta S hΘ hfin).trans
      (alphaTheta_le_of_abs_le hSH Θ hΘ)

theorem weakEssentialNorm_le_of_abs_le_real_finite
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {S H : LOne ℝ μ →L[ℝ] LOne ℝ ν} (hSH : |S| ≤ H) :
    weakEssentialNorm S ≤ weakEssentialNorm H := by
  rw [weakEssentialNorm_eq_localized_real_finite, weakEssentialNorm_eq_localized_real_finite]
  exact localizedWeakNoncompactness_le_of_abs_le hSH

theorem weaklyCompact_of_abs_le_real_finite
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {S H : LOne ℝ μ →L[ℝ] LOne ℝ ν} (hSH : |S| ≤ H)
    (hH : IsWeaklyCompactOperator H) : IsWeaklyCompactOperator S := by
  apply (weakEssentialNorm_eq_zero_iff S).mp
  apply le_antisymm _ (weakEssentialNorm_nonneg S)
  exact (weakEssentialNorm_le_of_abs_le_real_finite hSH).trans_eq
    ((weakEssentialNorm_eq_zero_iff H).mpr hH)

end PEMS

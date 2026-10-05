import PEMS.FiniteWeisFormula
import PEMS.MainStatements
import ThesisCommon.Analysis.PositiveFiniteKernelBestApproximation
import ThesisCommon.Analysis.WeakCalkinNorm
import ThesisCommon.Analysis.LatticeSignLift

/-! Actual best weakly compact approximation for real L1 operators on
arbitrary finite measure spaces. Positive budget clipping and the proved
finite norm formula give positive attainment; the actual lattice sign lift
gives signed attainment. No countable-generation hypothesis remains. -/
noncomputable section
open MeasureTheory ThesisCommon
open scoped ThesisCommon.PositiveOperatorOrder
namespace PEMS
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [IsFiniteMeasure ν]

theorem exists_positive_finite_weaklyCompact_bestApproximation
    (T : LOne ℝ μ →L[ℝ] LOne ℝ ν) (hT : 0 ≤ T) :
    ∃ H : LOne ℝ μ →L[ℝ] LOne ℝ ν, IsWeaklyCompactOperator H ∧
      0 ≤ H ∧ H ≤ integralBandProjection T ∧ ‖T - H‖ = weakEssentialNorm T := by
  obtain ⟨k, hk⟩ := integralBandProjection_isIntegral T
  obtain ⟨H, hH, hH0, hHP, hnorm⟩ :=
    exists_positive_weaklyCompact_integralBand_truncationInf_approx_finite T hT hk
  have hinf := (real_finite_weis_norm_formula (T - integralBandProjection T)
    (integralBandProjection T) (integralBandProjection_residual_singular T) hk).2
  simp only [sub_add_cancel] at hinf
  rw [← hinf] at hnorm
  exact ⟨H, hH, hH0, hHP, le_antisymm hnorm (weakEssentialNorm_le T hH)⟩

theorem weaklyCompact_abs_iff_real_finite (T : LOne ℝ μ →L[ℝ] LOne ℝ ν) :
    IsWeaklyCompactOperator |T| ↔ IsWeaklyCompactOperator T := by
  rw [← weakEssentialNorm_eq_zero_iff |T|, ← weakEssentialNorm_eq_zero_iff T,
    weakEssentialNorm_abs_real_finite]

theorem exists_real_finite_weaklyCompact_bestApproximation
    (T : LOne ℝ μ →L[ℝ] LOne ℝ ν) :
    ∃ W : LOne ℝ μ →L[ℝ] LOne ℝ ν, IsWeaklyCompactOperator W ∧
      ‖T - W‖ = weakEssentialNorm T := by
  obtain ⟨H, hH, hH0, hHP, hnorm⟩ :=
    exists_positive_finite_weaklyCompact_bestApproximation |T| (abs_nonneg T)
  have hHT : H ≤ |T| := hHP.trans (integralBandProjection_le_id |T| (abs_nonneg T))
  let W := latticeSignLift T H
  have hWabs : |W| = H := abs_latticeSignLift T hH0 hHT
  have hW : IsWeaklyCompactOperator W := (weaklyCompact_abs_iff_real_finite W).mp (hWabs ▸ hH)
  refine ⟨W, hW, ?_⟩
  calc
    ‖T - W‖ = ‖|T - W|‖ := (norm_abs_lOneOperator _).symm
    _ = ‖|T| - H‖ := by rw [show |T - W| = |T| - H from abs_sub_latticeSignLift T hH0 hHT]
    _ = weakEssentialNorm |T| := hnorm
    _ = weakEssentialNorm T := weakEssentialNorm_abs_real_finite T

theorem real_finite_attained_weis_formula (T : LOne ℝ μ →L[ℝ] LOne ℝ ν) :
    ∃ W : LOne ℝ μ →L[ℝ] LOne ℝ ν, IsWeaklyCompactOperator W ∧
      weakEssentialNorm T = ‖T - W‖ ∧ ‖T - W‖ = localizedWeakNoncompactness T := by
  obtain ⟨W, hW, heq⟩ := exists_real_finite_weaklyCompact_bestApproximation T
  exact ⟨W, hW, heq.symm, heq.trans (weakEssentialNorm_eq_localized_real_finite T)⟩

theorem theorem_1_1_real_finite (T : LOne ℝ μ →L[ℝ] LOne ℝ ν) : Theorem_1_1 μ ν T := by
  intro _ _
  exact real_finite_attained_weis_formula T

end PEMS

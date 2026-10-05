import PEMS.PositiveWeisFormula
import ThesisCommon.Analysis.PositiveKernelBestApproximation

/-! Exact weakly compact attainment for positive real operators on the compact
standard models. The candidate is the actual measurable budget-clipped kernel. -/

noncomputable section
open MeasureTheory ProbabilityTheory ThesisCommon
open scoped ENNReal ProbabilityTheory ThesisCommon.PositiveOperatorOrder

namespace PEMS

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable [CompactSpace X] [CompactSpace Y] [T2Space X] [T2Space Y]
variable [TotallyDisconnectedSpace X] [TotallyDisconnectedSpace Y]
variable [SecondCountableTopology X] [SecondCountableTopology Y]
variable [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
variable [StandardBorelSpace Y]
variable {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [IsFiniteMeasure ν]

theorem exists_positive_standard_weaklyCompact_bestApproximation
    (T : LOne ℝ μ →L[ℝ] LOne ℝ ν) (hT : 0 ≤ T) :
    ∃ H : LOne ℝ μ →L[ℝ] LOne ℝ ν, IsWeaklyCompactOperator H ∧
      0 ≤ H ∧ H ≤ integralBandProjection T ∧ ‖T - H‖ = weakEssentialNorm T := by
  obtain ⟨κ, hκ, _, hrepr, hk⟩ := exists_positive_operator_kernel_parts T hT
  letI := hκ
  obtain ⟨H, hH, hH0, hHP, hnorm⟩ :=
    exists_positive_weaklyCompact_truncationInf_approx T hT κ hrepr hk
  rw [← (positive_standard_weis_norm_formula T hT κ hrepr hk).2] at hnorm
  exact ⟨H, hH, hH0, hHP, le_antisymm hnorm (weakEssentialNorm_le T hH)⟩

end PEMS

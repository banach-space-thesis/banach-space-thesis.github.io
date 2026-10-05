import PEMS.PositiveWeisBestApproximation
import PEMS.RealWeisFormula
import ThesisCommon.Analysis.WeakCalkinNorm
import ThesisCommon.Analysis.LatticeSignLift

/-! Signed real attainment on compact standard models. The weak compactness
of the sign lift follows from the proved norm formula and closedness of the
actual weakly compact ideal, with no ideal-solidity hypothesis. -/

noncomputable section
open MeasureTheory ThesisCommon
open scoped ThesisCommon.PositiveOperatorOrder

namespace PEMS

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable [CompactSpace X] [CompactSpace Y] [T2Space X] [T2Space Y]
variable [TotallyDisconnectedSpace X] [TotallyDisconnectedSpace Y]
variable [SecondCountableTopology X] [SecondCountableTopology Y]
variable [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
variable [StandardBorelSpace Y]
variable {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [IsFiniteMeasure ν]

theorem weaklyCompact_abs_iff_real_standard (T : LOne ℝ μ →L[ℝ] LOne ℝ ν) :
    IsWeaklyCompactOperator |T| ↔ IsWeaklyCompactOperator T := by
  rw [← weakEssentialNorm_eq_zero_iff |T|, ← weakEssentialNorm_eq_zero_iff T,
    weakEssentialNorm_abs_real_standard]

/-- Every signed real operator has an actual best weakly compact approximant. -/
theorem exists_real_standard_weaklyCompact_bestApproximation
    (T : LOne ℝ μ →L[ℝ] LOne ℝ ν) :
    ∃ W : LOne ℝ μ →L[ℝ] LOne ℝ ν, IsWeaklyCompactOperator W ∧
      ‖T - W‖ = weakEssentialNorm T := by
  obtain ⟨H, hH, hH0, hHP, hnorm⟩ :=
    exists_positive_standard_weaklyCompact_bestApproximation |T| (abs_nonneg T)
  have hHT : H ≤ |T| := hHP.trans (integralBandProjection_le_id |T| (abs_nonneg T))
  let W := latticeSignLift T H
  have hWabs : |W| = H := abs_latticeSignLift T hH0 hHT
  have hW : IsWeaklyCompactOperator W := (weaklyCompact_abs_iff_real_standard W).mp (hWabs ▸ hH)
  refine ⟨W, hW, ?_⟩
  calc
    ‖T - W‖ = ‖|T - W|‖ := (norm_abs_lOneOperator _).symm
    _ = ‖|T| - H‖ := by rw [show |T - W| = |T| - H from abs_sub_latticeSignLift T hH0 hHT]
    _ = weakEssentialNorm |T| := hnorm
    _ = weakEssentialNorm T := weakEssentialNorm_abs_real_standard T

end PEMS

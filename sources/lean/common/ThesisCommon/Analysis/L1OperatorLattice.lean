import ThesisCommon.Analysis.ALOperatorOrderComplete
import ThesisCommon.Analysis.L1OperatorModulus

/-! Actual real L1 operators as a Dedekind complete lattice. Its modulus
is identified with the independently constructed bounded operator modulus. -/
noncomputable section
open MeasureTheory
namespace ThesisCommon
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}

namespace PositiveOperatorOrder
scoped instance lOneConditionallyCompleteLattice :
    ConditionallyCompleteLattice (Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) :=
  alOperatorConditionallyCompleteLattice (lOne_norm_add_of_nonneg μ) (lOne_norm_add_of_nonneg ν)
end PositiveOperatorOrder

open scoped PositiveOperatorOrder

theorem abs_lOneOperator_eq (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) : |T| = lOneOperatorModulus T :=
  alOperatorSup_neg (lOne_norm_add_of_nonneg μ) (lOne_norm_add_of_nonneg ν) T

theorem lOneOperator_exists_isLUB {s : Set (Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν)}
    (hs : s.Nonempty) (hbdd : BddAbove s) : ∃ T, IsLUB s T :=
  ⟨sSup s, isLUB_csSup hs hbdd⟩

theorem norm_abs_lOneOperator (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) : ‖|T|‖ = ‖T‖ := by
  rw [abs_lOneOperator_eq, norm_lOneOperatorModulus]

namespace PositiveOperatorOrder
scoped instance lOneSolidNorm : HasSolidNorm (Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) where
  solid := by
    intro S T hST
    rw [abs_lOneOperator_eq, abs_lOneOperator_eq] at hST
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
    intro f
    have hbound := (lOneOperatorModulus_dominates S f).trans (hST |f| (abs_nonneg f))
    have hpos := lOneOperatorModulus_nonneg T |f| (abs_nonneg f)
    calc
      ‖S f‖ ≤ ‖lOneOperatorModulus T |f|‖ := norm_le_norm_of_abs_le_abs (by
        simpa only [abs_of_nonneg hpos] using hbound)
      _ ≤ ‖lOneOperatorModulus T‖ * ‖|f|‖ := (lOneOperatorModulus T).le_opNorm _
      _ = ‖T‖ * ‖f‖ := by rw [norm_lOneOperatorModulus, norm_abs_eq_norm]
end PositiveOperatorOrder

end ThesisCommon

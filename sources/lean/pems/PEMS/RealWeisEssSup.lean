import PEMS.CountablyGeneratedWeisFormula
import ThesisCommon.Analysis.L1AdjointOneKernel

/-! The displayed essential-supremum expression in Theorem 4.4, for real
L1 operators on finite countably generated measure spaces. The symbol
`positiveAdjointOne |S| (abs_nonneg S)` is an actual L-infinity element:
its pairing is the Banach adjoint of |S| applied to the constant-one
functional. Its construction and the column formula are proved in the
common library, not included as representation hypotheses. The general
complex and localizable source scope is not asserted here. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal ThesisCommon.PositiveOperatorOrder
namespace PEMS
open ThesisCommon
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}
variable [MeasurableSpace.CountablyGenerated X] [MeasurableSpace.CountablyGenerated Y]
variable [IsFiniteMeasure μ] [IsFiniteMeasure ν]

theorem real_countablyGenerated_weis_essSup_formula
    (S K : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hS : IsSingularOperator S)
    {k : X × Y → ℝ} (hk : IsIntegralKernel k K) :
    weakEssentialNorm (S + K) = localizedWeakNoncompactness (S + K) ∧
    weakEssentialNorm (S + K) = sInf (Set.range (fun n : ℕ =>
      essSup (fun x => positiveAdjointOne |S| (abs_nonneg S) x +
        ∫ y, |truncatedKernel (n : ℝ) k (x, y)| ∂ν) μ)) := by
  obtain ⟨hloc, hnorm⟩ := real_countablyGenerated_weis_norm_formula S K hS hk
  exact ⟨hloc, hnorm.trans (congrArg sInf (congrArg Set.range (funext fun n =>
    singular_truncated_norm_eq_essSup_adjoint_column hk hS (n : ℝ))))⟩

theorem real_countablyGenerated_weis_essSup_formula_of_decomposition
    (T S K : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hT : T = S + K)
    (hS : IsSingularOperator S) {k : X × Y → ℝ} (hk : IsIntegralKernel k K) :
    weakEssentialNorm T = localizedWeakNoncompactness T ∧
    weakEssentialNorm T = sInf (Set.range (fun n : ℕ =>
      essSup (fun x => positiveAdjointOne |S| (abs_nonneg S) x +
        ∫ y, |truncatedKernel (n : ℝ) k (x, y)| ∂ν) μ)) := by
  subst T
  exact real_countablyGenerated_weis_essSup_formula S K hS hk

end PEMS

import PFP.AppendixDualStatements
import ThesisCommon.Analysis.QuasiReflexivePrimaryDual

/-! Full proof of the exact Appendix B.3 target. -/
noncomputable section
namespace PFP
open ThesisCommon

theorem proposition_B_3 (𝕜 X : Type*) [RCLike 𝕜] [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] [CompleteSpace X] : Proposition_B_3 𝕜 X :=
  primary_dual_of_quasi_reflexive_orderOne

end PFP

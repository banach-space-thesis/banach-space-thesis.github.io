import PFP.AppendixDualStatements
import ThesisCommon.Analysis.QuasiReflexiveDual
import ThesisCommon.Analysis.ResiduumDirectSums

/-! The full canonical quotient assertions of Appendix B.2. -/
noncomputable section
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 800000
namespace PFP
open ThesisCommon

theorem lemma_B_2 (𝕜 X : Type*) [RCLike 𝕜] [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] [CompleteSpace X] : Lemma_B_2 𝕜 X := by
  intro h
  refine ⟨h.dual, ?_⟩
  intro Y Z hY hZ hYZ
  exact ⟨residuumComplementedEquiv Y Z hY hZ hYZ⟩

end PFP

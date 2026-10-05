import PFP.AppendixDualStatements
import ThesisCommon.Analysis.ScalarExtensionAbsorption

/-! Checked Appendix B conclusions. B.1 is proved by the source's actual
complemented decomposition and hyperplane isomorphisms. The checked proofs
of B.2 and B.3 are in separate modules for their canonical bidual arguments.
-/
noncomputable section
namespace PFP
open ThesisCommon
variable (𝕜 X : Type*) [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [CompleteSpace X]

/-- Full Lemma B.1, `lem:complemented-copy-implies-hyperplanes`. -/
theorem lemma_B_1 : Lemma_B_1 𝕜 X := by
  intro _ h
  obtain ⟨E, hE, he⟩ := h
  have hX := scalarExtension_of_complemented_subspace E hE he
  exact ⟨hX, hX.everyHyperplane⟩

end PFP

import Posets.OperatorLemmas
import PosetsCommon.DiscreteCZero

noncomputable section
namespace Posets
variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem cZero_separable : TopologicalSpace.SeparableSpace (cZero 𝕜) :=
  ThesisCommon.discreteCZero_separable

/-- Literal factorisation through c₀ entails separable range in the actual norm topology. -/
theorem FactorsThroughCZero.hasSeparableRange {T : E →L[𝕜] F}
    (hT : FactorsThroughCZero 𝕜 T) : HasSeparableRange 𝕜 E F T := by
  obtain ⟨A, B, rfl⟩ := hT
  letI := cZero_separable (𝕜 := 𝕜)
  have hB : HasSeparableRange 𝕜 (cZero 𝕜) F B :=
    TopologicalSpace.isSeparable_range B.continuous
  exact hB.comp_right A

end Posets

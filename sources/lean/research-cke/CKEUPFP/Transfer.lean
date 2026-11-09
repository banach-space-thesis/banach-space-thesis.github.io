import CKEUPFP.CantorTransfer
import CKEUPFP.MilutinVector

/-! The unconditional main statement of the supplied paper. -/

noncomputable section

namespace CKEUPFP

/-- Theorem 1.1: an uncountable compact metrizable continuous-function space
inherits UPFP from its separable Banach range when the range contains no c₀. -/
theorem transferTheorem (𝕜 K E : Type*) [RCLike 𝕜]
    [TopologicalSpace K] [CompactSpace K] [TopologicalSpace.MetrizableSpace K]
    [Uncountable K] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [CompleteSpace E] [TopologicalSpace.SeparableSpace E] :
    TransferTheorem 𝕜 K E :=
  transferTheorem_of_cantor K E cantorQuantitativeTransfer

end CKEUPFP

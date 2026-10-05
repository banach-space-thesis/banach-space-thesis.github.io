import Posets.ScalarQuotientMap
import Posets.CommonScalarQuotientNorm

noncomputable section
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 3
open ThesisCommon
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜]

variable {P : Type} [PartialOrder P] [Countable P] [Nonempty P]
  {X : BoundedExtension P → Type} [∀ p, NormedAddCommGroup (X p)] [∀ p, NormedSpace 𝕜 (X p)]
  {ι : ∀ s t, X s →L[𝕜] X t} (h : FewOperators 𝕜 X ι)

/-- Exact norm one, already at the linear stage of the quotient construction. -/
theorem norm_scalarQuotientMap : ‖scalarQuotientMap h‖ = 1 :=
  norm_commonScalarQuotientMap (middleFewOperators h) (middleCommonSubspace h) (middleBlockScalarColumns h)

end Posets

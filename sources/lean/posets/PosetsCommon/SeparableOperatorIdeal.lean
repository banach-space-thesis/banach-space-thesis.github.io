import JFA.SeparableIdeal
import Mathlib.RingTheory.TwoSidedIdeal.Basic

noncomputable section
namespace ThesisCommon
variable (𝕜 : Type*) [RCLike 𝕜] (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The separable-range ideal bundled for the algebraic section argument. -/
def separableOperatorIdeal : TwoSidedIdeal (E →L[𝕜] E) :=
  TwoSidedIdeal.mk' {T | JFA.HasSeparableRange 𝕜 E E T}
    JFA.hasSeparableRange_zero (fun hS hT => hS.add hT) (fun hT => hT.neg)
    (fun {S _} hT => hT.comp_left S) (fun {_ T} hS => hS.comp_right T)

theorem mem_separableOperatorIdeal (T : E →L[𝕜] E) :
    T ∈ separableOperatorIdeal 𝕜 E ↔ JFA.HasSeparableRange 𝕜 E E T :=
  TwoSidedIdeal.mem_mk' _ _ _ _ _ _ T

end ThesisCommon

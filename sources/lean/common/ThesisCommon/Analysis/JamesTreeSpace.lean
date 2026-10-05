import ThesisCommon.Analysis.JamesTreePreSpace
import Mathlib.Analysis.Normed.Module.Completion

/-! Actual completions of the finitely supported tree spaces. The segment
family remains explicit. The literal-chain and consecutive-chain models
are both available, with no choice of the manuscript's unqualified JT_p
alias and no assertion of its primary factorisation property. -/
noncomputable section
namespace ThesisCommon
variable (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent) (S : JamesTreeSegmentFamily)

/-- The completion for the specified actual segment norm. -/
abbrev SegmentJamesTreeSpace := UniformSpace.Completion (JamesTreePreSpace 𝕜 p S)

/-- Canonical norm-preserving inclusion of c₀₀ into its genuine completion. -/
def jamesTreeDenseEmbedding : JamesTreePreSpace 𝕜 p S →ₗᵢ[𝕜] SegmentJamesTreeSpace 𝕜 p S :=
  UniformSpace.Completion.toComplₗᵢ

theorem jamesTreeDenseEmbedding_denseRange : DenseRange (jamesTreeDenseEmbedding 𝕜 p S) :=
  UniformSpace.Completion.denseRange_coe

@[simp] theorem jamesTreeDenseEmbedding_norm (a : JamesTreePreSpace 𝕜 p S) :
    ‖jamesTreeDenseEmbedding 𝕜 p S a‖ = ‖a‖ :=
  (jamesTreeDenseEmbedding 𝕜 p S).norm_map a

/-- The actual completion using the manuscript's literal finite-chain predicate. -/
abbrev LiteralChainJamesTreeSpace := SegmentJamesTreeSpace 𝕜 p literalTreeSegmentFamily

/-- The actual completion using the consecutive/order-convex finite-chain predicate. -/
abbrev ConsecutiveJamesTreeSpace := SegmentJamesTreeSpace 𝕜 p consecutiveTreeSegmentFamily

end ThesisCommon

import ThesisCommon.Analysis.JamesTreePrefixCompletion

/-! Prefix-subtree maps for both actual James-tree models. Every structural
hypothesis of the generic maps is discharged here. No unqualified JT alias
or assertion of PFP is introduced. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

abbrev literalJamesTreePrefixInsert (p : BanachExponent) (u : DyadicTreeNode) :
    LiteralChainJamesTreeSpace 𝕜 p →L[𝕜] LiteralChainJamesTreeSpace 𝕜 p :=
  jamesTreePrefixInsert u (literalJamesTreePrefixClosure u)

abbrev literalJamesTreePrefixRead (p : BanachExponent) (u : DyadicTreeNode) :
    LiteralChainJamesTreeSpace 𝕜 p →L[𝕜] LiteralChainJamesTreeSpace 𝕜 p :=
  jamesTreePrefixRead u (literalJamesTreePrefixClosure u)

abbrev literalJamesTreePrefixProjection (p : BanachExponent) (u : DyadicTreeNode) :
    LiteralChainJamesTreeSpace 𝕜 p →L[𝕜] LiteralChainJamesTreeSpace 𝕜 p :=
  jamesTreePrefixProjection u (literalJamesTreePrefixClosure u)

abbrev literalJamesTreePrefixIsometry (p : BanachExponent) (u : DyadicTreeNode) :
    LiteralChainJamesTreeSpace 𝕜 p →ₗᵢ[𝕜] LiteralChainJamesTreeSpace 𝕜 p :=
  jamesTreePrefixIsometry u (literalJamesTreePrefixClosure u)

abbrev consecutiveJamesTreePrefixInsert (p : BanachExponent) (u : DyadicTreeNode) :
    ConsecutiveJamesTreeSpace 𝕜 p →L[𝕜] ConsecutiveJamesTreeSpace 𝕜 p :=
  jamesTreePrefixInsert u (consecutiveJamesTreePrefixClosure u)

abbrev consecutiveJamesTreePrefixRead (p : BanachExponent) (u : DyadicTreeNode) :
    ConsecutiveJamesTreeSpace 𝕜 p →L[𝕜] ConsecutiveJamesTreeSpace 𝕜 p :=
  jamesTreePrefixRead u (consecutiveJamesTreePrefixClosure u)

abbrev consecutiveJamesTreePrefixProjection (p : BanachExponent) (u : DyadicTreeNode) :
    ConsecutiveJamesTreeSpace 𝕜 p →L[𝕜] ConsecutiveJamesTreeSpace 𝕜 p :=
  jamesTreePrefixProjection u (consecutiveJamesTreePrefixClosure u)

abbrev consecutiveJamesTreePrefixIsometry (p : BanachExponent) (u : DyadicTreeNode) :
    ConsecutiveJamesTreeSpace 𝕜 p →ₗᵢ[𝕜] ConsecutiveJamesTreeSpace 𝕜 p :=
  jamesTreePrefixIsometry u (consecutiveJamesTreePrefixClosure u)

theorem literalJamesTreePrefix_retraction (p : BanachExponent) (u : DyadicTreeNode) :
    (literalJamesTreePrefixRead (𝕜 := 𝕜) p u).comp (literalJamesTreePrefixInsert p u) =
      ContinuousLinearMap.id 𝕜 _ :=
  jamesTreePrefixRead_comp_insert u (literalJamesTreePrefixClosure u)

theorem consecutiveJamesTreePrefix_retraction (p : BanachExponent) (u : DyadicTreeNode) :
    (consecutiveJamesTreePrefixRead (𝕜 := 𝕜) p u).comp (consecutiveJamesTreePrefixInsert p u) =
      ContinuousLinearMap.id 𝕜 _ :=
  jamesTreePrefixRead_comp_insert u (consecutiveJamesTreePrefixClosure u)

theorem literalJamesTreePrefix_norms (p : BanachExponent) (u : DyadicTreeNode) :
    ‖literalJamesTreePrefixInsert (𝕜 := 𝕜) p u‖ = 1 ∧
    ‖literalJamesTreePrefixRead (𝕜 := 𝕜) p u‖ = 1 ∧
    ‖literalJamesTreePrefixProjection (𝕜 := 𝕜) p u‖ = 1 :=
  jamesTreePrefix_norms u (literalJamesTreePrefixClosure u)

theorem consecutiveJamesTreePrefix_norms (p : BanachExponent) (u : DyadicTreeNode) :
    ‖consecutiveJamesTreePrefixInsert (𝕜 := 𝕜) p u‖ = 1 ∧
    ‖consecutiveJamesTreePrefixRead (𝕜 := 𝕜) p u‖ = 1 ∧
    ‖consecutiveJamesTreePrefixProjection (𝕜 := 𝕜) p u‖ = 1 :=
  jamesTreePrefix_norms u (consecutiveJamesTreePrefixClosure u)

theorem literalJamesTreePrefixProjection_idempotent (p : BanachExponent)
    (u : DyadicTreeNode) :
    (literalJamesTreePrefixProjection (𝕜 := 𝕜) p u).comp
      (literalJamesTreePrefixProjection p u) = literalJamesTreePrefixProjection p u :=
  jamesTreePrefixProjection_idempotent u (literalJamesTreePrefixClosure u)

theorem consecutiveJamesTreePrefixProjection_idempotent (p : BanachExponent)
    (u : DyadicTreeNode) :
    (consecutiveJamesTreePrefixProjection (𝕜 := 𝕜) p u).comp
      (consecutiveJamesTreePrefixProjection p u) = consecutiveJamesTreePrefixProjection p u :=
  jamesTreePrefixProjection_idempotent u (consecutiveJamesTreePrefixClosure u)

end ThesisCommon

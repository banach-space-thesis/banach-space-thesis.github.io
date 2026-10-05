import ThesisCommon.Analysis.JamesTreeDelayedRange

/-! Selected-subtree maps for both actual James-tree models. Every structural
hypothesis of the generic maps is discharged here. No unqualified JT alias
or assertion of PFP is introduced. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

abbrev literalJamesTreeDelayedInsert (p : BanachExponent) (e : DyadicDelayedFork) :
    LiteralChainJamesTreeSpace 𝕜 p →L[𝕜] LiteralChainJamesTreeSpace 𝕜 p :=
  jamesTreeDelayedInsert e (literalJamesTreeDelayedForkClosure e)

abbrev literalJamesTreeDelayedRead (p : BanachExponent) (e : DyadicDelayedFork) :
    LiteralChainJamesTreeSpace 𝕜 p →L[𝕜] LiteralChainJamesTreeSpace 𝕜 p :=
  jamesTreeDelayedRead e (literalJamesTreeDelayedForkClosure e)

abbrev literalJamesTreeDelayedProjection (p : BanachExponent) (e : DyadicDelayedFork) :
    LiteralChainJamesTreeSpace 𝕜 p →L[𝕜] LiteralChainJamesTreeSpace 𝕜 p :=
  jamesTreeDelayedProjection e (literalJamesTreeDelayedForkClosure e)

abbrev literalJamesTreeDelayedIsometry (p : BanachExponent) (e : DyadicDelayedFork) :
    LiteralChainJamesTreeSpace 𝕜 p →ₗᵢ[𝕜] LiteralChainJamesTreeSpace 𝕜 p :=
  jamesTreeDelayedIsometry e (literalJamesTreeDelayedForkClosure e)

abbrev consecutiveJamesTreeDelayedInsert (p : BanachExponent) (e : DyadicDelayedFork) :
    ConsecutiveJamesTreeSpace 𝕜 p →L[𝕜] ConsecutiveJamesTreeSpace 𝕜 p :=
  jamesTreeDelayedInsert e (consecutiveJamesTreeDelayedForkClosure e)

abbrev consecutiveJamesTreeDelayedRead (p : BanachExponent) (e : DyadicDelayedFork) :
    ConsecutiveJamesTreeSpace 𝕜 p →L[𝕜] ConsecutiveJamesTreeSpace 𝕜 p :=
  jamesTreeDelayedRead e (consecutiveJamesTreeDelayedForkClosure e)

abbrev consecutiveJamesTreeDelayedProjection (p : BanachExponent) (e : DyadicDelayedFork) :
    ConsecutiveJamesTreeSpace 𝕜 p →L[𝕜] ConsecutiveJamesTreeSpace 𝕜 p :=
  jamesTreeDelayedProjection e (consecutiveJamesTreeDelayedForkClosure e)

abbrev consecutiveJamesTreeDelayedIsometry (p : BanachExponent) (e : DyadicDelayedFork) :
    ConsecutiveJamesTreeSpace 𝕜 p →ₗᵢ[𝕜] ConsecutiveJamesTreeSpace 𝕜 p :=
  jamesTreeDelayedIsometry e (consecutiveJamesTreeDelayedForkClosure e)

theorem literalJamesTreeDelayed_retraction (p : BanachExponent) (e : DyadicDelayedFork) :
    (literalJamesTreeDelayedRead (𝕜 := 𝕜) p e).comp (literalJamesTreeDelayedInsert p e) =
      ContinuousLinearMap.id 𝕜 _ :=
  jamesTreeDelayedRead_comp_insert e (literalJamesTreeDelayedForkClosure e)

theorem consecutiveJamesTreeDelayed_retraction (p : BanachExponent) (e : DyadicDelayedFork) :
    (consecutiveJamesTreeDelayedRead (𝕜 := 𝕜) p e).comp (consecutiveJamesTreeDelayedInsert p e) =
      ContinuousLinearMap.id 𝕜 _ :=
  jamesTreeDelayedRead_comp_insert e (consecutiveJamesTreeDelayedForkClosure e)

theorem literalJamesTreeDelayed_norms (p : BanachExponent) (e : DyadicDelayedFork) :
    ‖literalJamesTreeDelayedInsert (𝕜 := 𝕜) p e‖ = 1 ∧
    ‖literalJamesTreeDelayedRead (𝕜 := 𝕜) p e‖ = 1 ∧
    ‖literalJamesTreeDelayedProjection (𝕜 := 𝕜) p e‖ = 1 :=
  jamesTreeDelayed_norms e (literalJamesTreeDelayedForkClosure e)

theorem consecutiveJamesTreeDelayed_norms (p : BanachExponent) (e : DyadicDelayedFork) :
    ‖consecutiveJamesTreeDelayedInsert (𝕜 := 𝕜) p e‖ = 1 ∧
    ‖consecutiveJamesTreeDelayedRead (𝕜 := 𝕜) p e‖ = 1 ∧
    ‖consecutiveJamesTreeDelayedProjection (𝕜 := 𝕜) p e‖ = 1 :=
  jamesTreeDelayed_norms e (consecutiveJamesTreeDelayedForkClosure e)

theorem literalJamesTreeDelayedProjection_idempotent (p : BanachExponent)
    (e : DyadicDelayedFork) :
    (literalJamesTreeDelayedProjection (𝕜 := 𝕜) p e).comp
      (literalJamesTreeDelayedProjection p e) = literalJamesTreeDelayedProjection p e :=
  jamesTreeDelayedProjection_idempotent e (literalJamesTreeDelayedForkClosure e)

theorem consecutiveJamesTreeDelayedProjection_idempotent (p : BanachExponent)
    (e : DyadicDelayedFork) :
    (consecutiveJamesTreeDelayedProjection (𝕜 := 𝕜) p e).comp
      (consecutiveJamesTreeDelayedProjection p e) = consecutiveJamesTreeDelayedProjection p e :=
  jamesTreeDelayedProjection_idempotent e (consecutiveJamesTreeDelayedForkClosure e)

theorem literalJamesTreeDelayedProjection_range (p : BanachExponent)
    (e : DyadicDelayedFork) :
    LinearMap.range (literalJamesTreeDelayedProjection (𝕜 := 𝕜) p e).toLinearMap =
      jamesTreeDelayedSpan e :=
  jamesTreeDelayedProjection_range_eq_span e (literalJamesTreeDelayedForkClosure e)

theorem consecutiveJamesTreeDelayedProjection_range (p : BanachExponent)
    (e : DyadicDelayedFork) :
    LinearMap.range (consecutiveJamesTreeDelayedProjection (𝕜 := 𝕜) p e).toLinearMap =
      jamesTreeDelayedSpan e :=
  jamesTreeDelayedProjection_range_eq_span e (consecutiveJamesTreeDelayedForkClosure e)

abbrev literalJamesTreeDelayedSpanIsometry (p : BanachExponent)
    (e : DyadicDelayedFork) :
    LiteralChainJamesTreeSpace 𝕜 p ≃ₗᵢ[𝕜]
      jamesTreeDelayedSpan (𝕜 := 𝕜) (p := p) (S := literalTreeSegmentFamily) e :=
  jamesTreeDelayedSpanIsometry e (literalJamesTreeDelayedForkClosure e)

abbrev consecutiveJamesTreeDelayedSpanIsometry (p : BanachExponent)
    (e : DyadicDelayedFork) :
    ConsecutiveJamesTreeSpace 𝕜 p ≃ₗᵢ[𝕜]
      jamesTreeDelayedSpan (𝕜 := 𝕜) (p := p) (S := consecutiveTreeSegmentFamily) e :=
  jamesTreeDelayedSpanIsometry e (consecutiveJamesTreeDelayedForkClosure e)

end ThesisCommon

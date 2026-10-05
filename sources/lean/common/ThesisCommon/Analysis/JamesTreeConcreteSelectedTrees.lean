import ThesisCommon.Analysis.JamesTreeSelectedRange

/-! Selected-subtree maps for both actual James-tree models. Every structural
hypothesis of the generic maps is discharged here. No unqualified JT alias
or assertion of PFP is introduced. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

abbrev literalJamesTreeSelectedInsert (p : BanachExponent) (e : DyadicSubtreeEmbedding) :
    LiteralChainJamesTreeSpace 𝕜 p →L[𝕜] LiteralChainJamesTreeSpace 𝕜 p :=
  jamesTreeSelectedInsert e (literalJamesTreeSelectedClosure e)

abbrev literalJamesTreeSelectedRead (p : BanachExponent) (e : DyadicSubtreeEmbedding) :
    LiteralChainJamesTreeSpace 𝕜 p →L[𝕜] LiteralChainJamesTreeSpace 𝕜 p :=
  jamesTreeSelectedRead e (literalJamesTreeSelectedClosure e)

abbrev literalJamesTreeSelectedProjection (p : BanachExponent) (e : DyadicSubtreeEmbedding) :
    LiteralChainJamesTreeSpace 𝕜 p →L[𝕜] LiteralChainJamesTreeSpace 𝕜 p :=
  jamesTreeSelectedProjection e (literalJamesTreeSelectedClosure e)

abbrev literalJamesTreeSelectedIsometry (p : BanachExponent) (e : DyadicSubtreeEmbedding) :
    LiteralChainJamesTreeSpace 𝕜 p →ₗᵢ[𝕜] LiteralChainJamesTreeSpace 𝕜 p :=
  jamesTreeSelectedIsometry e (literalJamesTreeSelectedClosure e)

abbrev consecutiveJamesTreeSelectedInsert (p : BanachExponent) (e : DyadicSubtreeEmbedding) :
    ConsecutiveJamesTreeSpace 𝕜 p →L[𝕜] ConsecutiveJamesTreeSpace 𝕜 p :=
  jamesTreeSelectedInsert e (consecutiveJamesTreeSelectedClosure e)

abbrev consecutiveJamesTreeSelectedRead (p : BanachExponent) (e : DyadicSubtreeEmbedding) :
    ConsecutiveJamesTreeSpace 𝕜 p →L[𝕜] ConsecutiveJamesTreeSpace 𝕜 p :=
  jamesTreeSelectedRead e (consecutiveJamesTreeSelectedClosure e)

abbrev consecutiveJamesTreeSelectedProjection (p : BanachExponent) (e : DyadicSubtreeEmbedding) :
    ConsecutiveJamesTreeSpace 𝕜 p →L[𝕜] ConsecutiveJamesTreeSpace 𝕜 p :=
  jamesTreeSelectedProjection e (consecutiveJamesTreeSelectedClosure e)

abbrev consecutiveJamesTreeSelectedIsometry (p : BanachExponent) (e : DyadicSubtreeEmbedding) :
    ConsecutiveJamesTreeSpace 𝕜 p →ₗᵢ[𝕜] ConsecutiveJamesTreeSpace 𝕜 p :=
  jamesTreeSelectedIsometry e (consecutiveJamesTreeSelectedClosure e)

theorem literalJamesTreeSelected_retraction (p : BanachExponent) (e : DyadicSubtreeEmbedding) :
    (literalJamesTreeSelectedRead (𝕜 := 𝕜) p e).comp (literalJamesTreeSelectedInsert p e) =
      ContinuousLinearMap.id 𝕜 _ :=
  jamesTreeSelectedRead_comp_insert e (literalJamesTreeSelectedClosure e)

theorem consecutiveJamesTreeSelected_retraction (p : BanachExponent) (e : DyadicSubtreeEmbedding) :
    (consecutiveJamesTreeSelectedRead (𝕜 := 𝕜) p e).comp (consecutiveJamesTreeSelectedInsert p e) =
      ContinuousLinearMap.id 𝕜 _ :=
  jamesTreeSelectedRead_comp_insert e (consecutiveJamesTreeSelectedClosure e)

theorem literalJamesTreeSelected_norms (p : BanachExponent) (e : DyadicSubtreeEmbedding) :
    ‖literalJamesTreeSelectedInsert (𝕜 := 𝕜) p e‖ = 1 ∧
    ‖literalJamesTreeSelectedRead (𝕜 := 𝕜) p e‖ = 1 ∧
    ‖literalJamesTreeSelectedProjection (𝕜 := 𝕜) p e‖ = 1 :=
  jamesTreeSelected_norms e (literalJamesTreeSelectedClosure e)

theorem consecutiveJamesTreeSelected_norms (p : BanachExponent) (e : DyadicSubtreeEmbedding) :
    ‖consecutiveJamesTreeSelectedInsert (𝕜 := 𝕜) p e‖ = 1 ∧
    ‖consecutiveJamesTreeSelectedRead (𝕜 := 𝕜) p e‖ = 1 ∧
    ‖consecutiveJamesTreeSelectedProjection (𝕜 := 𝕜) p e‖ = 1 :=
  jamesTreeSelected_norms e (consecutiveJamesTreeSelectedClosure e)

theorem literalJamesTreeSelectedProjection_idempotent (p : BanachExponent)
    (e : DyadicSubtreeEmbedding) :
    (literalJamesTreeSelectedProjection (𝕜 := 𝕜) p e).comp
      (literalJamesTreeSelectedProjection p e) = literalJamesTreeSelectedProjection p e :=
  jamesTreeSelectedProjection_idempotent e (literalJamesTreeSelectedClosure e)

theorem consecutiveJamesTreeSelectedProjection_idempotent (p : BanachExponent)
    (e : DyadicSubtreeEmbedding) :
    (consecutiveJamesTreeSelectedProjection (𝕜 := 𝕜) p e).comp
      (consecutiveJamesTreeSelectedProjection p e) = consecutiveJamesTreeSelectedProjection p e :=
  jamesTreeSelectedProjection_idempotent e (consecutiveJamesTreeSelectedClosure e)

theorem literalJamesTreeSelectedProjection_range (p : BanachExponent)
    (e : DyadicSubtreeEmbedding) :
    LinearMap.range (literalJamesTreeSelectedProjection (𝕜 := 𝕜) p e).toLinearMap =
      jamesTreeSelectedSpan e :=
  jamesTreeSelectedProjection_range_eq_span e (literalJamesTreeSelectedClosure e)

theorem consecutiveJamesTreeSelectedProjection_range (p : BanachExponent)
    (e : DyadicSubtreeEmbedding) :
    LinearMap.range (consecutiveJamesTreeSelectedProjection (𝕜 := 𝕜) p e).toLinearMap =
      jamesTreeSelectedSpan e :=
  jamesTreeSelectedProjection_range_eq_span e (consecutiveJamesTreeSelectedClosure e)

abbrev literalJamesTreeSelectedSpanIsometry (p : BanachExponent)
    (e : DyadicSubtreeEmbedding) :
    LiteralChainJamesTreeSpace 𝕜 p ≃ₗᵢ[𝕜]
      jamesTreeSelectedSpan (𝕜 := 𝕜) (p := p) (S := literalTreeSegmentFamily) e :=
  jamesTreeSelectedSpanIsometry e (literalJamesTreeSelectedClosure e)

abbrev consecutiveJamesTreeSelectedSpanIsometry (p : BanachExponent)
    (e : DyadicSubtreeEmbedding) :
    ConsecutiveJamesTreeSpace 𝕜 p ≃ₗᵢ[𝕜]
      jamesTreeSelectedSpan (𝕜 := 𝕜) (p := p) (S := consecutiveTreeSegmentFamily) e :=
  jamesTreeSelectedSpanIsometry e (consecutiveJamesTreeSelectedClosure e)

end ThesisCommon

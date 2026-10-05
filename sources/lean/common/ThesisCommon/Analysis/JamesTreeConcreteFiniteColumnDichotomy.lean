import ThesisCommon.Analysis.JamesTreeFiniteColumnDichotomy

/-! The actual finite-column factorization dichotomy, with every geometric
condition discharged separately for the literal and consecutive norms. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜] {p : BanachExponent}

theorem literalJamesTree_finite_column_factor_dichotomy
    (hp : 1<p.val.toReal)
    (T : LiteralChainJamesTreeSpace 𝕜 p →L[𝕜] LiteralChainJamesTreeSpace 𝕜 p)
    (N : DyadicTreeNode → ℕ) (hN : ∀ t, t.length≤N t)
    (hT : ∀ t, literalJamesTreeLevelProjection p (N t)
      (T (jamesTreeUnit t))=T (jamesTreeUnit t))
    (hcompl : ∀ t, literalJamesTreeLevelProjection p (N t)
      ((ContinuousLinearMap.id 𝕜 (LiteralChainJamesTreeSpace 𝕜 p)-T) (jamesTreeUnit t))=
        (ContinuousLinearMap.id 𝕜 (LiteralChainJamesTreeSpace 𝕜 p)-T) (jamesTreeUnit t)) :
    FactorsIdentityWith T (LiteralChainJamesTreeSpace 𝕜 p) 6 ∨
      FactorsIdentityWith (ContinuousLinearMap.id 𝕜 (LiteralChainJamesTreeSpace 𝕜 p)-T) (LiteralChainJamesTreeSpace 𝕜 p) 6 :=
  jamesTree_finite_column_factor_dichotomy
    (fun A _ => literalJamesTreeMaskClosed_any A) literalJamesTreeSegmentsAreChains
    literalJamesTreeMaskClosed_levels (fun _ => literalJamesTreeMaskClosed_any _)
    (fun _ => literalJamesTreeMaskClosed_any _) (fun _ _ => literalJamesTreeMaskClosed_any _)
    (fun t => literalJamesTreeChainClosed (dyadicFalseRay_isConvex t).1)
    (fun _ => (dyadicTreeInterval_consecutive List.nil_prefix).1)
    literalJamesTreeDelayedForkClosure literalJamesTreeMaskClosed_initial hp T N hN hT hcompl

theorem consecutiveJamesTree_finite_column_factor_dichotomy
    (hp : 1<p.val.toReal)
    (T : ConsecutiveJamesTreeSpace 𝕜 p →L[𝕜] ConsecutiveJamesTreeSpace 𝕜 p)
    (N : DyadicTreeNode → ℕ) (hN : ∀ t, t.length≤N t)
    (hT : ∀ t, consecutiveJamesTreeLevelProjection p (N t)
      (T (jamesTreeUnit t))=T (jamesTreeUnit t))
    (hcompl : ∀ t, consecutiveJamesTreeLevelProjection p (N t)
      ((ContinuousLinearMap.id 𝕜 (ConsecutiveJamesTreeSpace 𝕜 p)-T) (jamesTreeUnit t))=
        (ContinuousLinearMap.id 𝕜 (ConsecutiveJamesTreeSpace 𝕜 p)-T) (jamesTreeUnit t)) :
    FactorsIdentityWith T (ConsecutiveJamesTreeSpace 𝕜 p) 6 ∨
      FactorsIdentityWith (ContinuousLinearMap.id 𝕜 (ConsecutiveJamesTreeSpace 𝕜 p)-T) (ConsecutiveJamesTreeSpace 𝕜 p) 6 :=
  jamesTree_finite_column_factor_dichotomy
    (fun _ => consecutiveJamesTreeMaskClosed_segment) consecutiveJamesTreeSegmentsAreChains
    consecutiveJamesTreeMaskClosed_levels consecutiveJamesTreeMaskClosed_levelTail
    consecutiveJamesTreeMaskClosed_cone (fun _ => consecutiveJamesTreeMaskClosed_convexChain)
    (fun t => consecutiveJamesTreeChainClosed (dyadicFalseRay_isConvex t))
    (fun _ => dyadicTreeInterval_consecutive List.nil_prefix)
    consecutiveJamesTreeDelayedForkClosure consecutiveJamesTreeMaskClosed_initial hp T N hN hT hcompl

end ThesisCommon


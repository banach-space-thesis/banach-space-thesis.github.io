import ThesisCommon.Analysis.JamesTreeFiniteColumnApproximation

/-! The finite-column-support perturbation in both actual tree norms,
including simultaneous support of the complementary operator's columns. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜] {p : BanachExponent}

theorem exists_literalJamesTree_finite_column_perturbation
    (T : LiteralChainJamesTreeSpace 𝕜 p →L[𝕜] LiteralChainJamesTreeSpace 𝕜 p)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (T' : LiteralChainJamesTreeSpace 𝕜 p →L[𝕜] LiteralChainJamesTreeSpace 𝕜 p)
      (N : DyadicTreeNode → ℕ),
      ‖T' - T‖ < ε ∧ (∀ t, t.length ≤ N t) ∧
      (∀ t, T' (jamesTreeUnit t) =
        literalJamesTreeLevelProjection p (N t) (T (jamesTreeUnit t))) ∧
      (∀ t, literalJamesTreeLevelProjection p (N t) (T' (jamesTreeUnit t)) = T' (jamesTreeUnit t)) ∧
      (∀ t, literalJamesTreeLevelProjection p (N t)
        ((ContinuousLinearMap.id 𝕜 (LiteralChainJamesTreeSpace 𝕜 p) - T') (jamesTreeUnit t)) =
        (ContinuousLinearMap.id 𝕜 (LiteralChainJamesTreeSpace 𝕜 p) - T') (jamesTreeUnit t)) :=
  exists_jamesTree_finite_column_perturbation literalJamesTreeMaskClosed_levels T hε

theorem exists_consecutiveJamesTree_finite_column_perturbation
    (T : ConsecutiveJamesTreeSpace 𝕜 p →L[𝕜] ConsecutiveJamesTreeSpace 𝕜 p)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (T' : ConsecutiveJamesTreeSpace 𝕜 p →L[𝕜] ConsecutiveJamesTreeSpace 𝕜 p)
      (N : DyadicTreeNode → ℕ),
      ‖T' - T‖ < ε ∧ (∀ t, t.length ≤ N t) ∧
      (∀ t, T' (jamesTreeUnit t) =
        consecutiveJamesTreeLevelProjection p (N t) (T (jamesTreeUnit t))) ∧
      (∀ t, consecutiveJamesTreeLevelProjection p (N t) (T' (jamesTreeUnit t)) = T' (jamesTreeUnit t)) ∧
      (∀ t, consecutiveJamesTreeLevelProjection p (N t)
        ((ContinuousLinearMap.id 𝕜 (ConsecutiveJamesTreeSpace 𝕜 p) - T') (jamesTreeUnit t)) =
        (ContinuousLinearMap.id 𝕜 (ConsecutiveJamesTreeSpace 𝕜 p) - T') (jamesTreeUnit t)) :=
  exists_jamesTree_finite_column_perturbation consecutiveJamesTreeMaskClosed_levels T hε

end ThesisCommon


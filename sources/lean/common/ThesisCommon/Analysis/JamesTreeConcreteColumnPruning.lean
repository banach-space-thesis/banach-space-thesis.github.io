import ThesisCommon.Analysis.JamesTreeColumnPruning
import ThesisCommon.Analysis.JamesTreeBranchTailEstimates

/-! The two fully discharged versions of Andrew's Proposition 3. The
finite branch intervals, common cut levels and later subtree nodes are
actual objects in each of the two recorded James-tree spaces. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜] {p : BanachExponent} {ι : Type*} [Fintype ι]

theorem exists_literalJamesTree_pruned_column
    (f : DyadicTreeNode ↪ DyadicTreeNode)
    (hf : ∀ s t, (f s).IsPrefix (f t) ↔ s.IsPrefix t)
    (hp : 1 < p.val.toReal)
    (T : LiteralChainJamesTreeSpace 𝕜 p →L[𝕜] LiteralChainJamesTreeSpace 𝕜 p)
    (u₀ : DyadicTreeNode) (u : ι → DyadicTreeNode) (N : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (v : DyadicTreeNode) (M : ℕ) (w t : ι → DyadicTreeNode),
      (f u₀).IsPrefix (f v) ∧ f v ≠ f u₀ ∧ N < M ∧
      ‖literalJamesTreeLevelProjection p N (T (jamesTreeUnit (f v)))‖ < ε ∧
      ‖T (jamesTreeUnit (f v)) -
        literalJamesTreeLevelProjection p M (T (jamesTreeUnit (f v)))‖ < ε ∧
      ∀ i, (u i).IsPrefix (w i) ∧ (f (u i)).IsPrefix (t i) ∧
        (t i).IsPrefix (f (w i)) ∧ (t i).length = M + 1 ∧ M + 1 < (f (w i)).length ∧
        ‖jamesTreeMask (dyadicTreeInterval (f (u i)) (t i) : Set DyadicTreeNode)
          (literalJamesTreeMaskClosed_set _) (T (jamesTreeUnit (f v)))‖ < ε :=
  exists_jamesTree_pruned_column f hf literalJamesTreeSegmentsAreChains
    literalJamesTreeMaskClosed_levels (fun _ => literalJamesTreeMaskClosed_set _)
    literalJamesTreeMaskClosed_cone (fun _ _ => literalJamesTreeMaskClosed_set _)
    hp T u₀ u N hε

theorem exists_consecutiveJamesTree_pruned_column
    (f : DyadicTreeNode ↪ DyadicTreeNode)
    (hf : ∀ s t, (f s).IsPrefix (f t) ↔ s.IsPrefix t)
    (hp : 1 < p.val.toReal)
    (T : ConsecutiveJamesTreeSpace 𝕜 p →L[𝕜] ConsecutiveJamesTreeSpace 𝕜 p)
    (u₀ : DyadicTreeNode) (u : ι → DyadicTreeNode) (N : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (v : DyadicTreeNode) (M : ℕ) (w t : ι → DyadicTreeNode),
      (f u₀).IsPrefix (f v) ∧ f v ≠ f u₀ ∧ N < M ∧
      ‖consecutiveJamesTreeLevelProjection p N (T (jamesTreeUnit (f v)))‖ < ε ∧
      ‖T (jamesTreeUnit (f v)) -
        consecutiveJamesTreeLevelProjection p M (T (jamesTreeUnit (f v)))‖ < ε ∧
      ∀ i, (u i).IsPrefix (w i) ∧ (f (u i)).IsPrefix (t i) ∧
        (t i).IsPrefix (f (w i)) ∧ (t i).length = M + 1 ∧ M + 1 < (f (w i)).length ∧
        ‖jamesTreeMask (dyadicTreeInterval (f (u i)) (t i) : Set DyadicTreeNode)
          (consecutiveJamesTreeMaskClosed_convexChain (dyadicTreeInterval_isConvex _ _))
          (T (jamesTreeUnit (f v)))‖ < ε :=
  exists_jamesTree_pruned_column f hf consecutiveJamesTreeSegmentsAreChains
    consecutiveJamesTreeMaskClosed_levels consecutiveJamesTreeMaskClosed_levelTail
    consecutiveJamesTreeMaskClosed_cone (fun _ => consecutiveJamesTreeMaskClosed_convexChain)
    hp T u₀ u N hε

end ThesisCommon

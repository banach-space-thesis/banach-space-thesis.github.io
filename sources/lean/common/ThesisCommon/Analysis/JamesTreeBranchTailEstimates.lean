import ThesisCommon.Analysis.JamesTreeBranchTailMasks

/-! The disjoint-branch-tail p-sum estimate in each actual norm. The
consecutive convention uses order-convex branches; no operator estimate
or infinite-vector approximation is postulated. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜] {p : BanachExponent} {ι : Type*} [Fintype ι]

theorem literalJamesTree_disjoint_branch_tails_sum_rpow_le
    (hp : 0 < p.val.toReal) (B : ι → Set DyadicTreeNode) (N : ℕ)
    (hd : Pairwise (fun i j => Disjoint (B i ∩ (dyadicInitialLevels N)ᶜ)
      (B j ∩ (dyadicInitialLevels N)ᶜ))) (x : LiteralChainJamesTreeSpace 𝕜 p) :
    ∑ i, ‖jamesTreeMask (B i ∩ (dyadicInitialLevels N)ᶜ)
      (literalJamesTreeMaskClosed_set _) x‖ ^ p.val.toReal ≤ ‖x‖ ^ p.val.toReal :=
  jamesTree_disjoint_masks_sum_rpow_le hp _ (fun _ => literalJamesTreeMaskClosed_set _) hd x

theorem consecutiveJamesTree_disjoint_branch_tails_sum_rpow_le
    (hp : 0 < p.val.toReal) (B : ι → Set DyadicTreeNode)
    (hB : ∀ i, IsConvexTreeChain (B i)) (N : ℕ)
    (hd : Pairwise (fun i j => Disjoint (B i ∩ (dyadicInitialLevels N)ᶜ)
      (B j ∩ (dyadicInitialLevels N)ᶜ))) (x : ConsecutiveJamesTreeSpace 𝕜 p) :
    ∑ i, ‖jamesTreeMask (B i ∩ (dyadicInitialLevels N)ᶜ)
      (jamesTreeMaskClosed_inter (consecutiveJamesTreeMaskClosed_convexChain (hB i))
        (consecutiveJamesTreeMaskClosed_levelTail N)) x‖ ^ p.val.toReal ≤ ‖x‖ ^ p.val.toReal :=
  jamesTree_disjoint_masks_sum_rpow_le hp _ (fun i =>
    jamesTreeMaskClosed_inter (consecutiveJamesTreeMaskClosed_convexChain (hB i))
      (consecutiveJamesTreeMaskClosed_levelTail N)) hd x

end ThesisCommon

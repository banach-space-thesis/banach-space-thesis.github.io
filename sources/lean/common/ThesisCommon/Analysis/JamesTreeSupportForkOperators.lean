import ThesisCommon.Analysis.JamesTreeSupportForks
import ThesisCommon.Analysis.JamesTreeSelectedBranchCoefficients

/-! Actual finite operator support gives the exact root-to-fork branch
coefficient after every strong subtree selection. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜] {p : BanachExponent} {S : JamesTreeSegmentFamily}

theorem jamesTree_supportFork_column_fixed
    (hL : ∀ m, JamesTreeMaskClosed S (dyadicInitialLevels m))
    (N : DyadicTreeNode → ℕ) (hN : ∀ t, t.length≤N t)
    (Q : SegmentJamesTreeSpace 𝕜 p S →L[𝕜] SegmentJamesTreeSpace 𝕜 p S)
    (hQ : ∀ t, jamesTreeMask (dyadicInitialLevels (N t)) (hL _)
      (Q (jamesTreeUnit t))=Q (jamesTreeUnit t))
    (e : DyadicSubtreeEmbedding) (v : DyadicTreeNode) :
    jamesTreeMask (dyadicInitialLevels (((dyadicSupportFork N).comp e).fork v).length) (hL _)
      (Q (jamesTreeUnit (((dyadicSupportFork N).comp e).node v))) =
      Q (jamesTreeUnit (((dyadicSupportFork N).comp e).node v)) := by
  simpa only [dyadicSupportFork_comp_endpoint,dyadicFalseEndpoint_length _ (hN _)] using
    hQ (((dyadicSupportFork N).comp e).node v)

theorem jamesTree_supportFork_branch_eq_sum
    (hL : ∀ m, JamesTreeMaskClosed S (dyadicInitialLevels m))
    (hbranch : ∀ t, JamesTreeChainClosed S (dyadicFalseRay t))
    (N : DyadicTreeNode → ℕ) (hN : ∀ t, t.length≤N t)
    (Q : SegmentJamesTreeSpace 𝕜 p S →L[𝕜] SegmentJamesTreeSpace 𝕜 p S)
    (hQ : ∀ t, jamesTreeMask (dyadicInitialLevels (N t)) (hL _)
      (Q (jamesTreeUnit t))=Q (jamesTreeUnit t))
    (e : DyadicSubtreeEmbedding) (v : DyadicTreeNode) :
    jamesTreeBranchCoefficient dyadicFalseRay hbranch Q (((dyadicSupportFork N).comp e).node v) =
      ∑ t∈dyadicTreeInterval [] (((dyadicSupportFork N).comp e).fork v),
        jamesTreeCoordinate t (Q (jamesTreeUnit (((dyadicSupportFork N).comp e).node v))) := by
  simpa only [jamesTreeBranchCoefficient,dyadicSupportFork_comp_endpoint] using
    jamesTreeBranchFunctional_eq_support_sum (((dyadicSupportFork N).comp e).node v)
      (hN _) (hL _) (hbranch _) (Q (jamesTreeUnit (((dyadicSupportFork N).comp e).node v))) (hQ _)

theorem jamesTree_diagonal_unit
    (hL : ∀ m, JamesTreeMaskClosed S (dyadicInitialLevels m))
    (D : SegmentJamesTreeSpace 𝕜 p S →L[𝕜] SegmentJamesTreeSpace 𝕜 p S)
    (c : DyadicTreeNode → 𝕜)
    (hD : ∀ x t, jamesTreeCoordinate t (D x)=c t*jamesTreeCoordinate t x)
    (s : DyadicTreeNode) : D (jamesTreeUnit s)=c s • jamesTreeUnit s := by
  apply jamesTreeCoordinate_ext hL
  intro t
  rw [hD,map_smul,jamesTreeCoordinate_unit]
  by_cases hts : t=s
  · subst t; simp only [ite_true,smul_eq_mul]
  · simp only [if_neg hts,mul_zero,smul_zero]

end ThesisCommon

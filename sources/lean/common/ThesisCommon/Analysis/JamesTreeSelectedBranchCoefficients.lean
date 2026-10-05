import ThesisCommon.Analysis.DyadicScalarBranchSelection
import ThesisCommon.Analysis.JamesTreeConcreteBranches

/-! The actual T-versus-id−T operator selection preceding the tree
gliding-hump construction. One full subtree has branch coefficients bounded
below by 1/2, and all its branches have arbitrarily small summable variation.
Both recorded segment conventions and every real/complex scalar are covered. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜] {p : BanachExponent} {S : JamesTreeSegmentFamily}

def jamesTreeBranchCoefficient (B : DyadicTreeNode → Set DyadicTreeNode)
    (hB : ∀ t, JamesTreeChainClosed S (B t))
    (T : SegmentJamesTreeSpace 𝕜 p S →L[𝕜] SegmentJamesTreeSpace 𝕜 p S)
    (t : DyadicTreeNode) : 𝕜 := jamesTreeChainFunctional (B t) (hB t) (T (jamesTreeUnit t))

theorem norm_jamesTreeBranchCoefficient_le (B : DyadicTreeNode → Set DyadicTreeNode)
    (hB : ∀ t, JamesTreeChainClosed S (B t))
    (T : SegmentJamesTreeSpace 𝕜 p S →L[𝕜] SegmentJamesTreeSpace 𝕜 p S)
    (t : DyadicTreeNode) : ‖jamesTreeBranchCoefficient B hB T t‖ ≤ ‖T‖ := by
  exact (jamesTreeChainFunctional_norm_le (B t) (hB t) _).trans
    (by simpa only [norm_jamesTreeUnit, mul_one] using T.le_opNorm (jamesTreeUnit t))

theorem exists_jamesTree_selected_branch_control (B : DyadicTreeNode → Set DyadicTreeNode)
    (hB : ∀ t, JamesTreeChainClosed S (B t)) (ht : ∀ t, t ∈ B t)
    (T : SegmentJamesTreeSpace 𝕜 p S →L[𝕜] SegmentJamesTreeSpace 𝕜 p S)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ Q : SegmentJamesTreeSpace 𝕜 p S →L[𝕜] SegmentJamesTreeSpace 𝕜 p S,
      (Q = T ∨ Q = ContinuousLinearMap.id 𝕜 _ - T) ∧
      ∃ e : DyadicSubtreeEmbedding, DyadicBranchControl (jamesTreeBranchCoefficient B hB Q) e (1 / 2) ε := by
  let Q (c : Bool) := if c then T else ContinuousLinearMap.id 𝕜 _ - T
  obtain ⟨c, e, he⟩ := exists_dyadic_scalar_branch_choice
    (fun c => jamesTreeBranchCoefficient B hB (Q c)) (fun c => ‖Q c‖)
    (fun c t => norm_jamesTreeBranchCoefficient_le B hB (Q c) t) (1 / 2)
    (fun t => jamesTreeChainFunctional_half_dichotomy (B t) (hB t) t (ht t) T) hε
  refine ⟨Q c, ?_, e, he⟩
  cases c <;> simp [Q]

abbrev literalJamesTreeBranchCoefficient
    (T : LiteralChainJamesTreeSpace 𝕜 p →L[𝕜] LiteralChainJamesTreeSpace 𝕜 p) : DyadicTreeNode → 𝕜 :=
  jamesTreeBranchCoefficient dyadicFalseRay
    (fun t => literalJamesTreeChainClosed (dyadicFalseRay_isConvex t).1) T

abbrev consecutiveJamesTreeBranchCoefficient
    (T : ConsecutiveJamesTreeSpace 𝕜 p →L[𝕜] ConsecutiveJamesTreeSpace 𝕜 p) : DyadicTreeNode → 𝕜 :=
  jamesTreeBranchCoefficient dyadicFalseRay
    (fun t => consecutiveJamesTreeChainClosed (dyadicFalseRay_isConvex t)) T

theorem exists_literalJamesTree_selected_branch_control
    (T : LiteralChainJamesTreeSpace 𝕜 p →L[𝕜] LiteralChainJamesTreeSpace 𝕜 p)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ Q : LiteralChainJamesTreeSpace 𝕜 p →L[𝕜] LiteralChainJamesTreeSpace 𝕜 p,
      (Q = T ∨ Q = ContinuousLinearMap.id 𝕜 _ - T) ∧
      ∃ e : DyadicSubtreeEmbedding, DyadicBranchControl (literalJamesTreeBranchCoefficient Q) e (1 / 2) ε :=
  exists_jamesTree_selected_branch_control dyadicFalseRay _ dyadicFalseRay_contains T hε

theorem exists_consecutiveJamesTree_selected_branch_control
    (T : ConsecutiveJamesTreeSpace 𝕜 p →L[𝕜] ConsecutiveJamesTreeSpace 𝕜 p)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ Q : ConsecutiveJamesTreeSpace 𝕜 p →L[𝕜] ConsecutiveJamesTreeSpace 𝕜 p,
      (Q = T ∨ Q = ContinuousLinearMap.id 𝕜 _ - T) ∧
      ∃ e : DyadicSubtreeEmbedding, DyadicBranchControl (consecutiveJamesTreeBranchCoefficient Q) e (1 / 2) ε :=
  exists_jamesTree_selected_branch_control dyadicFalseRay _ dyadicFalseRay_contains T hε

end ThesisCommon

import ThesisCommon.Analysis.JamesTreeChainFunctionals

/-! Explicit infinite branches through every dyadic node, valid for both
recorded norms, and the source's actual branch-functional 1/2 dichotomy.
No Ramsey subtree or uniform factorization assertion is assumed. -/
noncomputable section
open Filter Topology
open scoped BigOperators
namespace ThesisCommon
attribute [local instance] Classical.propDecidable

def dyadicFalseRay (u : DyadicTreeNode) : Set DyadicTreeNode :=
  {t | ∃ n : ℕ, t.IsPrefix (u ++ List.replicate n false)}

theorem dyadicFalseRay_contains (u : DyadicTreeNode) : u ∈ dyadicFalseRay u :=
  ⟨0, by simp⟩

theorem dyadicFalseRay_isConvex (u : DyadicTreeNode) : IsConvexTreeChain (dyadicFalseRay u) := by
  have hrep {m n : ℕ} (h : m ≤ n) :
      (u ++ List.replicate m false).IsPrefix (u ++ List.replicate n false) := by
    apply (List.prefix_append_right_inj u).mpr
    refine ⟨List.replicate (n - m) false, ?_⟩
    rw [← List.replicate_add, Nat.add_sub_of_le h]
  constructor
  · intro s hs t ht
    obtain ⟨m, hm⟩ := hs
    obtain ⟨n, hn⟩ := ht
    exact List.prefix_or_prefix_of_prefix
      (hm.trans (hrep (Nat.le_max_left m n)))
      (hn.trans (hrep (Nat.le_max_right m n)))
  · intro s hs t ht v hsv hvt
    obtain ⟨n, hn⟩ := ht
    exact ⟨n, hvt.trans hn⟩

theorem dyadicFalseRay_infinite (u : DyadicTreeNode) : (dyadicFalseRay u).Infinite := by
  have hinj : Function.Injective (fun n : ℕ => u ++ List.replicate n false) := by
    intro m n h
    have hl := congrArg List.length h
    simpa only [List.length_append, List.length_replicate, Nat.add_left_cancel_iff] using hl
  apply (Set.infinite_range_of_injective hinj).mono
  rintro t ⟨n, rfl⟩
  exact ⟨n, List.prefix_rfl⟩

variable {𝕜 : Type*} [RCLike 𝕜] {p : BanachExponent} {S : JamesTreeSegmentFamily}

abbrev literalJamesTreeChainFunctional (p : BanachExponent)
    (B : Set DyadicTreeNode) (hB : IsTreeChain B) : LiteralChainJamesTreeSpace 𝕜 p →L[𝕜] 𝕜 :=
  jamesTreeChainFunctional B (literalJamesTreeChainClosed hB)

abbrev consecutiveJamesTreeChainFunctional (p : BanachExponent)
    (B : Set DyadicTreeNode) (hB : IsConvexTreeChain B) :
    ConsecutiveJamesTreeSpace 𝕜 p →L[𝕜] 𝕜 :=
  jamesTreeChainFunctional B (consecutiveJamesTreeChainClosed hB)

abbrev literalJamesTreeBranchFunctional (p : BanachExponent) (u : DyadicTreeNode) :
    LiteralChainJamesTreeSpace 𝕜 p →L[𝕜] 𝕜 :=
  literalJamesTreeChainFunctional p (dyadicFalseRay u) (dyadicFalseRay_isConvex u).1

abbrev consecutiveJamesTreeBranchFunctional (p : BanachExponent) (u : DyadicTreeNode) :
    ConsecutiveJamesTreeSpace 𝕜 p →L[𝕜] 𝕜 :=
  consecutiveJamesTreeChainFunctional p (dyadicFalseRay u) (dyadicFalseRay_isConvex u)

theorem jamesTreeChainFunctional_level_sums_tendsto (B : Set DyadicTreeNode)
    (hB : JamesTreeChainClosed S B)
    (hS : ∀ N, JamesTreeMaskClosed S (dyadicInitialLevels N))
    (x : SegmentJamesTreeSpace 𝕜 p S) :
    Tendsto (fun N => ∑ t ∈ dyadicInitialFinset N,
      if t ∈ B then jamesTreeCoordinate t x else 0)
      atTop (𝓝 (jamesTreeChainFunctional B hB x)) := by
  classical
  have h := (jamesTreeChainFunctional B hB).continuous.continuousAt.tendsto.comp
    (jamesTree_level_sums_tendsto hS x)
  convert h using 1
  funext N
  simp only [Function.comp_apply, map_sum, map_smul, jamesTreeChainFunctional_unit]
  apply Finset.sum_congr rfl
  intro t ht
  by_cases htB : t ∈ B <;> simp [htB]

theorem jamesTreeChainFunctional_half_dichotomy
    (B : Set DyadicTreeNode) (hB : JamesTreeChainClosed S B)
    (t : DyadicTreeNode) (ht : t ∈ B)
    (T : SegmentJamesTreeSpace 𝕜 p S →L[𝕜] SegmentJamesTreeSpace 𝕜 p S) :
    1 / 2 ≤ ‖jamesTreeChainFunctional B hB (T (jamesTreeUnit t))‖ ∨
      1 / 2 ≤ ‖jamesTreeChainFunctional B hB
        ((ContinuousLinearMap.id 𝕜 (SegmentJamesTreeSpace 𝕜 p S) - T) (jamesTreeUnit t))‖ := by
  have he : jamesTreeChainFunctional B hB (T (jamesTreeUnit t)) +
      jamesTreeChainFunctional B hB
        ((ContinuousLinearMap.id 𝕜 (SegmentJamesTreeSpace 𝕜 p S) - T) (jamesTreeUnit t)) = (1 : 𝕜) := by
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, map_sub,
      jamesTreeChainFunctional_unit, if_pos ht]
    abel
  have hn := norm_add_le
    (jamesTreeChainFunctional B hB (T (jamesTreeUnit t)))
    (jamesTreeChainFunctional B hB
      ((ContinuousLinearMap.id 𝕜 (SegmentJamesTreeSpace 𝕜 p S) - T) (jamesTreeUnit t)))
  rw [he, norm_one] at hn
  by_cases h : 1 / 2 ≤ ‖jamesTreeChainFunctional B hB (T (jamesTreeUnit t))‖
  · exact Or.inl h
  · right
    push_neg at h
    linarith

theorem literalJamesTree_branch_half_dichotomy (p : BanachExponent)
    (T : LiteralChainJamesTreeSpace 𝕜 p →L[𝕜] LiteralChainJamesTreeSpace 𝕜 p)
    (t : DyadicTreeNode) :
    1 / 2 ≤ ‖literalJamesTreeBranchFunctional p t (T (jamesTreeUnit t))‖ ∨
      1 / 2 ≤ ‖literalJamesTreeBranchFunctional p t
        ((ContinuousLinearMap.id 𝕜 (LiteralChainJamesTreeSpace 𝕜 p) - T) (jamesTreeUnit t))‖ :=
  jamesTreeChainFunctional_half_dichotomy _ _ t (dyadicFalseRay_contains t) T

theorem consecutiveJamesTree_branch_half_dichotomy (p : BanachExponent)
    (T : ConsecutiveJamesTreeSpace 𝕜 p →L[𝕜] ConsecutiveJamesTreeSpace 𝕜 p)
    (t : DyadicTreeNode) :
    1 / 2 ≤ ‖consecutiveJamesTreeBranchFunctional p t (T (jamesTreeUnit t))‖ ∨
      1 / 2 ≤ ‖consecutiveJamesTreeBranchFunctional p t
        ((ContinuousLinearMap.id 𝕜 (ConsecutiveJamesTreeSpace 𝕜 p) - T) (jamesTreeUnit t))‖ :=
  jamesTreeChainFunctional_half_dichotomy _ _ t (dyadicFalseRay_contains t) T

end ThesisCommon

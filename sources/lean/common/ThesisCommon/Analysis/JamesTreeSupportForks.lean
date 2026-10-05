import ThesisCommon.Analysis.DyadicDelayedForkSelection
import ThesisCommon.Analysis.JamesTreeConcreteBranches

/-! The initial delayed-fork tree for finitely supported operator columns:
each fork continues the prescribed false branch to the actual support cut.
The branch functional is exactly the finite root-to-fork sum on that column. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon
attribute [local instance] Classical.propDecidable

def dyadicFalseEndpoint (t : DyadicTreeNode) (N : ℕ) : DyadicTreeNode :=
  t++List.replicate (N-t.length) false

theorem dyadicFalseEndpoint_prefix (t : DyadicTreeNode) (N : ℕ) :
    t.IsPrefix (dyadicFalseEndpoint t N) := List.prefix_append _ _

@[simp] theorem dyadicFalseEndpoint_length (t : DyadicTreeNode) {N : ℕ} (hN : t.length≤N) :
    (dyadicFalseEndpoint t N).length=N := by
  simp only [dyadicFalseEndpoint,List.length_append,List.length_replicate]
  omega

theorem dyadicFalseEndpoint_mem (t : DyadicTreeNode) (N : ℕ) :
    dyadicFalseEndpoint t N∈dyadicFalseRay t := ⟨N-t.length,List.prefix_rfl⟩

theorem dyadicFalseRay_initial_interval (t : DyadicTreeNode) {N : ℕ} (hN : t.length≤N) :
    (dyadicInitialFinset N).filter (·∈dyadicFalseRay t) =
      dyadicTreeInterval [] (dyadicFalseEndpoint t N) := by
  classical
  ext x
  rw [Finset.mem_filter,mem_dyadicInitialFinset,mem_dyadicTreeInterval]
  constructor
  · rintro ⟨hxN,hxB⟩
    refine ⟨List.nil_prefix,?_⟩
    rcases (dyadicFalseRay_isConvex t).1 x hxB _ (dyadicFalseEndpoint_mem t N) with h | h
    · exact h
    · have heq := h.eq_of_length (by rw [dyadicFalseEndpoint_length t hN]; exact (hxN.antisymm (by
        simpa only [dyadicFalseEndpoint_length t hN] using h.length_le)).symm)
      rw [heq]
  · rintro ⟨_,hx⟩
    exact ⟨(by simpa only [dyadicFalseEndpoint_length t hN] using hx.length_le),
      ⟨N-t.length,hx⟩⟩

def dyadicSupportFork (N : DyadicTreeNode → ℕ) : DyadicDelayedFork :=
  DyadicDelayedFork.ofExtension (fun t => dyadicFalseEndpoint t (N t))
    (fun t => dyadicFalseEndpoint_prefix t (N t)) []

@[simp] theorem dyadicSupportFork_endpoint (N : DyadicTreeNode → ℕ) (s : DyadicTreeNode) :
    (dyadicSupportFork N).fork s =
      dyadicFalseEndpoint ((dyadicSupportFork N).node s) (N ((dyadicSupportFork N).node s)) := rfl

theorem dyadicSupportFork_comp_endpoint (N : DyadicTreeNode → ℕ)
    (g : DyadicSubtreeEmbedding) (s : DyadicTreeNode) :
    ((dyadicSupportFork N).comp g).fork s =
      dyadicFalseEndpoint (((dyadicSupportFork N).comp g).node s)
        (N (((dyadicSupportFork N).comp g).node s)) := rfl

variable {𝕜 : Type*} [RCLike 𝕜] {p : BanachExponent} {S : JamesTreeSegmentFamily}

theorem jamesTreeBranchFunctional_eq_support_sum (t : DyadicTreeNode) {N : ℕ}
    (hN : t.length≤N) (hL : JamesTreeMaskClosed S (dyadicInitialLevels N))
    (hB : JamesTreeChainClosed S (dyadicFalseRay t))
    (x : SegmentJamesTreeSpace 𝕜 p S) (hx : jamesTreeMask (dyadicInitialLevels N) hL x=x) :
    jamesTreeChainFunctional (dyadicFalseRay t) hB x =
      ∑ u∈dyadicTreeInterval [] (dyadicFalseEndpoint t N), jamesTreeCoordinate u x := by
  classical
  calc
    _ = jamesTreeChainFunctional (dyadicFalseRay t) hB (jamesTreeMask (dyadicInitialLevels N) hL x) := by rw [hx]
    _ = ∑ u∈dyadicInitialFinset N, if u∈dyadicFalseRay t then jamesTreeCoordinate u x else 0 := by
      rw [jamesTreeLevelProjection_finite_sum,map_sum]
      apply Finset.sum_congr rfl
      intro u hu
      rw [map_smul,jamesTreeChainFunctional_unit]
      split_ifs <;> simp
    _ = _ := by rw [← Finset.sum_filter,dyadicFalseRay_initial_interval t hN]

end ThesisCommon

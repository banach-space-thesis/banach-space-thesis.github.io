import ThesisCommon.Analysis.DyadicRootedCells

/-! Exact finite-sum decomposition of a full root path into the earlier
parent path and the current rooted cell. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon

theorem dyadicTreeInterval_root_split {u v : DyadicTreeNode} {b : Bool}
    (huv : (u ++ [b]).IsPrefix v) :
    dyadicTreeInterval [] v = dyadicTreeInterval [] u ∪ dyadicTreeInterval (u ++ [b]) v := by
  ext x
  simp only [Finset.mem_union,mem_dyadicTreeInterval,List.nil_prefix,true_and]
  constructor
  · intro hx
    by_cases hlen : x.length ≤ u.length
    · exact Or.inl (List.prefix_of_prefix_length_le hx ((List.prefix_append _ _).trans huv) hlen)
    · exact Or.inr ⟨List.prefix_of_prefix_length_le huv hx
        (by simp only [List.length_append,List.length_singleton]; omega),hx⟩
  · rintro (hx | ⟨_,hx⟩)
    · exact hx.trans ((List.prefix_append _ _).trans huv)
    · exact hx

theorem dyadicTreeInterval_root_split_disjoint (u v : DyadicTreeNode) (b : Bool) :
    Disjoint (dyadicTreeInterval [] u) (dyadicTreeInterval (u ++ [b]) v) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  have hxu := ((mem_dyadicTreeInterval [] u x).mp hx).2.length_le
  have hux := ((mem_dyadicTreeInterval (u++[b]) v x).mp hy).1.length_le
  simp only [List.length_append,List.length_singleton] at hux
  omega

theorem dyadicRootedCell_full_sum_sub_nil {E : Type*} [AddCommGroup E]
    (e : DyadicSubtreeEmbedding) (a : DyadicTreeNode → E) :
    (∑ t ∈ dyadicTreeInterval [] (e []), a t) - (∑ t ∈ dyadicRootedCell e [], a t) = 0 := by
  rw [dyadicRootedCell_nil,sub_self]

theorem dyadicRootedCell_full_sum_sub_snoc {E : Type*} [AddCommGroup E]
    (e : DyadicSubtreeEmbedding) (s : DyadicTreeNode) (b : Bool) (a : DyadicTreeNode → E) :
    (∑ t ∈ dyadicTreeInterval [] (e (s++[b])), a t) -
      (∑ t ∈ dyadicRootedCell e (s++[b]), a t) = ∑ t ∈ dyadicTreeInterval [] (e s), a t := by
  rw [dyadicRootedCell_snoc,dyadicTreeInterval_root_split (e.split_prefix s b),
    Finset.sum_union (dyadicTreeInterval_root_split_disjoint _ _ _),add_sub_cancel_right]

end ThesisCommon

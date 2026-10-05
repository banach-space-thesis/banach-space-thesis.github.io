import ThesisCommon.Analysis.DyadicTreeIntervals
import ThesisCommon.Analysis.DyadicTreeAntichains
import ThesisCommon.Analysis.JamesTreeBranchTailMasks

/-! Long extensions in every actual embedded dyadic subtree and the
head/cone cover of a finite consecutive branch interval. -/
noncomputable section
namespace ThesisCommon

theorem exists_dyadic_subtree_long_extension
    (f : DyadicTreeNode ↪ DyadicTreeNode)
    (u : DyadicTreeNode) (N : ℕ) :
    ∃ v, u.IsPrefix v ∧ N < (f v).length := by
  let e := (dyadicCombEmbedding u).trans f
  obtain ⟨t, ⟨n,rfl⟩, ht⟩ :=
    (Set.infinite_range_of_injective e.injective).exists_notMem_finite
      (dyadicInitialLevels_finite N)
  exact ⟨dyadicCombEmbedding u n, dyadicCombEmbedding_prefix u n, Nat.lt_of_not_ge ht⟩

theorem dyadicTreeInterval_isConvex (s t : DyadicTreeNode) :
    IsConvexTreeChain (dyadicTreeInterval s t : Set DyadicTreeNode) := by
  constructor
  · intro a ha b hb
    exact List.prefix_or_prefix_of_prefix ((mem_dyadicTreeInterval s t a).mp ha).2
      ((mem_dyadicTreeInterval s t b).mp hb).2
  · intro a ha b hb u hau hub
    exact (mem_dyadicTreeInterval s t u).mpr
      ⟨((mem_dyadicTreeInterval s t a).mp ha).1.trans hau,
        hub.trans ((mem_dyadicTreeInterval s t b).mp hb).2⟩

theorem dyadicTreeInterval_subset_head_cone {s r t : DyadicTreeNode} {N : ℕ}
    (hrt : r.IsPrefix t) (hrN : r.length ≤ N) :
    (dyadicTreeInterval s t : Set DyadicTreeNode) ⊆
      dyadicInitialLevels N ∪ dyadicDescendantCone r := by
  intro u hu
  by_cases huN : u.length ≤ N
  · exact Or.inl huN
  · exact Or.inr (List.prefix_of_prefix_length_le hrt
      ((mem_dyadicTreeInterval s t u).mp hu).2 (by omega))

theorem exists_dyadic_interval_through_cone
    (f : DyadicTreeNode ↪ DyadicTreeNode)
    (hf : ∀ s t, (f s).IsPrefix (f t) ↔ s.IsPrefix t)
    {u r : DyadicTreeNode} (hur : u.IsPrefix r)
    {N M : ℕ} (hrN : (f r).length ≤ N) (hNM : N ≤ M) :
    ∃ v t, r.IsPrefix v ∧ (f u).IsPrefix t ∧ (f r).IsPrefix t ∧
      t.IsPrefix (f v) ∧ t.length = M + 1 ∧ M + 1 < (f v).length ∧
      (dyadicTreeInterval (f u) t : Set DyadicTreeNode) ⊆
        dyadicInitialLevels N ∪ dyadicDescendantCone (f r) := by
  obtain ⟨v, hrv, hv⟩ := exists_dyadic_subtree_long_extension f r (M + 1)
  let t := (f v).take (M + 1)
  have ht : t.length = M + 1 := by simp only [t, List.length_take, Nat.min_eq_left hv.le]
  have hrt : (f r).IsPrefix t := List.prefix_of_prefix_length_le ((hf r v).mpr hrv)
    (List.take_prefix (M + 1) (f v)) (by rw [ht]; omega)
  exact ⟨v,t,hrv,((hf u r).mpr hur).trans hrt,hrt,List.take_prefix _ _,ht,hv,
    dyadicTreeInterval_subset_head_cone hrt hrN⟩

end ThesisCommon

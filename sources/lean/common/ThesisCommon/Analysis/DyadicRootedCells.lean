import ThesisCommon.Analysis.DyadicSelectedCellSegments

/-! Connecting cells with the entire initial root path included. The end
of a cell is a branching fork; a selected basis node may occur strictly
earlier inside that cell, as required by Andrew's support construction. -/
noncomputable section
namespace ThesisCommon

def dyadicRootedCell (e : DyadicSubtreeEmbedding) (s : DyadicTreeNode) : Finset DyadicTreeNode :=
  if s = [] then dyadicTreeInterval [] (e []) else dyadicSelectedCell e s

@[simp] theorem dyadicRootedCell_nil (e : DyadicSubtreeEmbedding) :
    dyadicRootedCell e [] = dyadicTreeInterval [] (e []) := by simp [dyadicRootedCell]

@[simp] theorem dyadicRootedCell_snoc (e : DyadicSubtreeEmbedding) (s : DyadicTreeNode) (b : Bool) :
    dyadicRootedCell e (s++[b]) = dyadicTreeInterval (e s++[b]) (e (s++[b])) := by
  simp [dyadicRootedCell]

theorem dyadicRootedCell_consecutive (e : DyadicSubtreeEmbedding) (s : DyadicTreeNode) :
    IsConsecutiveTreeSegment (dyadicRootedCell e s) := by
  by_cases hs : s=[]
  · subst s; rw [dyadicRootedCell_nil]; exact dyadicTreeInterval_consecutive (List.nil_prefix)
  · simpa only [dyadicRootedCell, if_neg hs] using dyadicSelectedCell_consecutive e s

theorem dyadicSelectedCell_subset_rootedCell (e : DyadicSubtreeEmbedding) (s : DyadicTreeNode) :
    dyadicSelectedCell e s ⊆ dyadicRootedCell e s := by
  by_cases hs : s=[]
  · subst s
    intro x hx
    have hx' : x=e [] := by simpa only [dyadicSelectedCell_nil, Finset.mem_singleton] using hx
    rw [hx',dyadicRootedCell_nil,mem_dyadicTreeInterval]
    exact ⟨List.nil_prefix,List.prefix_rfl⟩
  · simp only [dyadicRootedCell,if_neg hs,Finset.Subset.refl]

theorem dyadicRootedCell_self (e : DyadicSubtreeEmbedding) (s : DyadicTreeNode) :
    e s ∈ dyadicRootedCell e s :=
  dyadicSelectedCell_subset_rootedCell e s (dyadicSelectedCell_self e s)

theorem dyadicRootedCell_prefix_endpoint (e : DyadicSubtreeEmbedding)
    {s x : DyadicTreeNode} (hx : x∈dyadicRootedCell e s) : x.IsPrefix (e s) := by
  by_cases hs : s=[]
  · subst s; exact ((mem_dyadicTreeInterval _ _ _).mp (dyadicRootedCell_nil e ▸ hx)).2
  · exact dyadicSelectedCell_prefix_endpoint e (by simpa only [dyadicRootedCell,if_neg hs] using hx)

theorem dyadicRootedCell_index_prefix (e : DyadicSubtreeEmbedding)
    {s t x : DyadicTreeNode} (hx : x∈dyadicRootedCell e s) (hxt : x.IsPrefix (e t)) :
    s.IsPrefix t := by
  by_cases hs : s=[]
  · subst s; exact List.nil_prefix
  · exact dyadicSelectedCell_index_prefix e
      (by simpa only [dyadicRootedCell,if_neg hs] using hx) hxt

theorem dyadicRootedCell_disjoint (e : DyadicSubtreeEmbedding) :
    Pairwise (fun s t => Disjoint (dyadicRootedCell e s) (dyadicRootedCell e t)) := by
  intro s t hst
  apply Finset.disjoint_left.mpr
  intro x hxs hxt
  have hs := dyadicRootedCell_index_prefix e hxs (dyadicRootedCell_prefix_endpoint e hxt)
  have ht := dyadicRootedCell_index_prefix e hxt (dyadicRootedCell_prefix_endpoint e hxs)
  exact hst (hs.eq_of_length (hs.length_le.antisymm ht.length_le))

theorem dyadicRootedCell_cover_prefix (e : DyadicSubtreeEmbedding)
    (t x : DyadicTreeNode) (hxt : x.IsPrefix (e t)) :
    ∃ s, s.IsPrefix t ∧ x∈dyadicRootedCell e s := by
  rcases List.prefix_or_prefix_of_prefix hxt (e.root_prefix t) with hx | hx
  · exact ⟨[],List.nil_prefix,by
      rw [dyadicRootedCell_nil,mem_dyadicTreeInterval]
      exact ⟨List.nil_prefix,hx⟩⟩
  · obtain ⟨s,hst,hs⟩ := dyadicSelectedCell_cover_prefix e t x hx hxt
    exact ⟨s,hst,dyadicSelectedCell_subset_rootedCell e s hs⟩

theorem dyadicRootedCell_ancestor_prefix (e : DyadicSubtreeEmbedding)
    {s t x : DyadicTreeNode} (hx : x∈dyadicRootedCell e t)
    (hst : s.IsPrefix t) (hne : s≠t) : (e s).IsPrefix x := by
  induction t using List.reverseRecOn with
  | nil => exact (hne (by simpa using hst)).elim
  | append_singleton t b _ =>
    have hlen : s.length ≤ t.length := by
      have hlt : s.length < (t++[b]).length := by
        have := hst.length_le
        by_contra hh
        exact hne (hst.eq_of_length (by omega))
      simp only [List.length_append,List.length_singleton] at hlt
      omega
    have hst' : s.IsPrefix t :=
      List.prefix_of_prefix_length_le hst (List.prefix_append t [b]) hlen
    have hlower := ((mem_dyadicTreeInterval _ _ _).mp (dyadicRootedCell_snoc e t b ▸ hx)).1
    exact ((e.prefix_iff s t).mpr hst').trans ((List.prefix_append _ _).trans hlower)

end ThesisCommon

import ThesisCommon.Analysis.DyadicTreeFrontierUpdates
import ThesisCommon.Analysis.DyadicNodeSplitEmbedding

/-! Grafting arbitrary later ambient roots onto a finite frontier. The
processed nodes stay fixed, and each remaining cone is continued by its
literal suffix after the chosen replacement root. -/
noncomputable section
namespace ThesisCommon

def dyadicTreeFrontierPrefix (n : ℕ) (t : DyadicTreeNode)
    (ht : n ≤ dyadicTreeEnumeration.symm t) : DyadicTreeNode :=
  (existsUnique_dyadicTreeFrontier_prefix n t ht).choose

theorem dyadicTreeFrontierPrefix_mem (n : ℕ) (t : DyadicTreeNode)
    (ht : n ≤ dyadicTreeEnumeration.symm t) :
    dyadicTreeFrontierPrefix n t ht ∈ dyadicTreeFrontier n :=
  (existsUnique_dyadicTreeFrontier_prefix n t ht).choose_spec.1.1

theorem dyadicTreeFrontierPrefix_prefix (n : ℕ) (t : DyadicTreeNode)
    (ht : n ≤ dyadicTreeEnumeration.symm t) :
    (dyadicTreeFrontierPrefix n t ht).IsPrefix t :=
  (existsUnique_dyadicTreeFrontier_prefix n t ht).choose_spec.1.2

theorem dyadicTreeFrontierPrefix_eq (n : ℕ) (t : DyadicTreeNode)
    (ht : n ≤ dyadicTreeEnumeration.symm t) {s : DyadicTreeNode}
    (hs : s ∈ dyadicTreeFrontier n) (hst : s.IsPrefix t) :
    dyadicTreeFrontierPrefix n t ht = s :=
  ((existsUnique_dyadicTreeFrontier_prefix n t ht).choose_spec.2 s ⟨hs,hst⟩).symm

def dyadicFrontierGraftNode (n : ℕ) (e : DyadicSubtreeEmbedding)
    (r : DyadicTreeNode → DyadicTreeNode) (t : DyadicTreeNode) : DyadicTreeNode :=
  if ht : dyadicTreeEnumeration.symm t < n then e t else
    let s := dyadicTreeFrontierPrefix n t (Nat.le_of_not_gt ht)
    r s ++ t.drop s.length

theorem dyadicFrontierGraftNode_processed (n : ℕ) (e : DyadicSubtreeEmbedding)
    (r : DyadicTreeNode → DyadicTreeNode) {t : DyadicTreeNode}
    (ht : dyadicTreeEnumeration.symm t < n) : dyadicFrontierGraftNode n e r t = e t := by
  simp only [dyadicFrontierGraftNode,dif_pos ht]

theorem dyadicFrontierGraftNode_descendant (n : ℕ) (e : DyadicSubtreeEmbedding)
    (r : DyadicTreeNode → DyadicTreeNode) {s t : DyadicTreeNode}
    (hs : s ∈ dyadicTreeFrontier n) (hst : s.IsPrefix t) :
    dyadicFrontierGraftNode n e r t = r s ++ t.drop s.length := by
  have ht : n ≤ dyadicTreeEnumeration.symm t :=
    ((mem_dyadicTreeFrontier n s).mp hs).1.trans (dyadicTreeEnumeration_prefix_index hst)
  simp only [dyadicFrontierGraftNode,dif_neg (not_lt_of_ge ht),
    dyadicTreeFrontierPrefix_eq n t ht hs hst]

theorem dyadicFrontierGraftNode_frontier (n : ℕ) (e : DyadicSubtreeEmbedding)
    (r : DyadicTreeNode → DyadicTreeNode) {s : DyadicTreeNode}
    (hs : s ∈ dyadicTreeFrontier n) : dyadicFrontierGraftNode n e r s = r s := by
  rw [dyadicFrontierGraftNode_descendant n e r hs List.prefix_rfl]
  simp only [List.drop_length,List.append_nil]

theorem dyadicFrontierGraftNode_split (n : ℕ) (e : DyadicSubtreeEmbedding)
    (r : DyadicTreeNode → DyadicTreeNode)
    (hr : ∀ s ∈ dyadicTreeFrontier n, (e s).IsPrefix (r s)) :
    ∀ t b, (dyadicFrontierGraftNode n e r t ++ [b]).IsPrefix
      (dyadicFrontierGraftNode n e r (t ++ [b])) := by
  intro t b
  by_cases ht : dyadicTreeEnumeration.symm t < n
  · rw [dyadicFrontierGraftNode_processed n e r ht]
    by_cases hc : dyadicTreeEnumeration.symm (t ++ [b]) < n
    · rw [dyadicFrontierGraftNode_processed n e r hc]
      exact e.split_prefix t b
    · have hcf : t ++ [b] ∈ dyadicTreeFrontier n := by
        apply (mem_dyadicTreeFrontier n _).mpr
        refine ⟨Nat.le_of_not_gt hc,?_⟩
        intro s hs hne
        exact (dyadicTreeEnumeration_prefix_index (dyadic_proper_prefix_of_child hs hne)).trans_lt ht
      rw [dyadicFrontierGraftNode_frontier n e r hcf]
      exact (e.split_prefix t b).trans (hr _ hcf)
  · let s := dyadicTreeFrontierPrefix n t (Nat.le_of_not_gt ht)
    have hs : s ∈ dyadicTreeFrontier n := dyadicTreeFrontierPrefix_mem n t _
    have hst : s.IsPrefix t := dyadicTreeFrontierPrefix_prefix n t _
    rw [dyadicFrontierGraftNode_descendant n e r hs hst,
      dyadicFrontierGraftNode_descendant n e r hs (hst.trans (List.prefix_append t [b])),
      List.drop_append_of_le_length hst.length_le,List.append_assoc]

def dyadicFrontierGraft (n : ℕ) (e : DyadicSubtreeEmbedding)
    (r : DyadicTreeNode → DyadicTreeNode)
    (hr : ∀ s ∈ dyadicTreeFrontier n, (e s).IsPrefix (r s)) : DyadicSubtreeEmbedding :=
  dyadicSubtreeEmbeddingOfSplit (dyadicFrontierGraftNode n e r)
    (dyadicFrontierGraftNode_split n e r hr)

@[simp] theorem dyadicFrontierGraft_apply (n : ℕ) (e : DyadicSubtreeEmbedding)
    (r : DyadicTreeNode → DyadicTreeNode)
    (hr : ∀ s ∈ dyadicTreeFrontier n, (e s).IsPrefix (r s)) (t : DyadicTreeNode) :
    dyadicFrontierGraft n e r hr t = dyadicFrontierGraftNode n e r t := by
  simp only [dyadicFrontierGraft,dyadicSubtreeEmbeddingOfSplit_apply]

theorem dyadicFrontierGraft_processed (n : ℕ) (e : DyadicSubtreeEmbedding)
    (r : DyadicTreeNode → DyadicTreeNode)
    (hr : ∀ s ∈ dyadicTreeFrontier n, (e s).IsPrefix (r s))
    {t : DyadicTreeNode} (ht : dyadicTreeEnumeration.symm t < n) :
    dyadicFrontierGraft n e r hr t = e t := by
  simpa only [dyadicFrontierGraft_apply] using dyadicFrontierGraftNode_processed n e r ht

theorem dyadicFrontierGraft_frontier (n : ℕ) (e : DyadicSubtreeEmbedding)
    (r : DyadicTreeNode → DyadicTreeNode)
    (hr : ∀ s ∈ dyadicTreeFrontier n, (e s).IsPrefix (r s))
    {t : DyadicTreeNode} (ht : t ∈ dyadicTreeFrontier n) :
    dyadicFrontierGraft n e r hr t = r t := by
  simpa only [dyadicFrontierGraft_apply] using dyadicFrontierGraftNode_frontier n e r ht

theorem dyadicFrontierGraft_descendant (n : ℕ) (e : DyadicSubtreeEmbedding)
    (r : DyadicTreeNode → DyadicTreeNode)
    (hr : ∀ s ∈ dyadicTreeFrontier n, (e s).IsPrefix (r s))
    {s t : DyadicTreeNode} (hs : s ∈ dyadicTreeFrontier n) (hst : s.IsPrefix t) :
    dyadicFrontierGraft n e r hr t = r s ++ t.drop s.length := by
  simpa only [dyadicFrontierGraft_apply] using dyadicFrontierGraftNode_descendant n e r hs hst

end ThesisCommon

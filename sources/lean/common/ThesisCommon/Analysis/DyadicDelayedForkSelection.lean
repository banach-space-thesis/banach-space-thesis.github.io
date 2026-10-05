import ThesisCommon.Analysis.DyadicDelayedFork

/-! Delayed forks are constructed from arbitrary actual endpoint extensions
and are preserved by subsequent strong-subtree selection. This supplies the
support-separating initial tree in the operator argument. -/
noncomputable section
namespace ThesisCommon

theorem dyadicRootedCell_split_prefix (e : DyadicSubtreeEmbedding)
    {s t x : DyadicTreeNode} {b : Bool} (hx : x∈dyadicRootedCell e t)
    (hst : (s++[b]).IsPrefix t) : (e s++[b]).IsPrefix x := by
  by_cases heq : s++[b]=t
  · subst t
    exact ((mem_dyadicTreeInterval _ _ _).mp (dyadicRootedCell_snoc e s b ▸ hx)).1
  · exact (e.split_prefix s b).trans (dyadicRootedCell_ancestor_prefix e hx hst heq)

namespace DyadicDelayedFork

def comp (d : DyadicDelayedFork) (g : DyadicSubtreeEmbedding) : DyadicDelayedFork where
  fork := d.fork.comp g
  node s := d.node (g s)
  node_mem := by
    intro s
    induction s using List.reverseRecOn with
    | nil =>
      rw [dyadicRootedCell_nil,mem_dyadicTreeInterval]
      exact ⟨List.nil_prefix,dyadicRootedCell_prefix_endpoint d.fork (d.node_mem (g []))⟩
    | append_singleton s b _ =>
      rw [dyadicRootedCell_snoc,mem_dyadicTreeInterval]
      exact ⟨dyadicRootedCell_split_prefix d.fork (d.node_mem (g (s++[b])))
        (g.split_prefix s b),dyadicRootedCell_prefix_endpoint d.fork (d.node_mem (g (s++[b])))⟩

@[simp] theorem comp_node (d : DyadicDelayedFork) (g : DyadicSubtreeEmbedding) (s : DyadicTreeNode) :
    (d.comp g).node s = d.node (g s) := rfl

@[simp] theorem comp_fork (d : DyadicDelayedFork) (g : DyadicSubtreeEmbedding) (s : DyadicTreeNode) :
    (d.comp g).fork s = d.fork (g s) := rfl

def ofExtension (l : DyadicTreeNode → DyadicTreeNode) (hl : ∀ t : DyadicTreeNode, t.IsPrefix (l t))
    (r : DyadicTreeNode) : DyadicDelayedFork where
  fork := dyadicExpansionEmbedding (fun t b => l t++[b]) l
    (fun t b => hl (l t++[b])) r
  node s := s.foldl (fun t b => l t++[b]) r
  node_mem := by
    intro s
    induction s using List.reverseRecOn with
    | nil =>
      rw [dyadicRootedCell_nil,mem_dyadicTreeInterval]
      exact ⟨List.nil_prefix,hl r⟩
    | append_singleton s b _ =>
      rw [dyadicRootedCell_snoc,mem_dyadicTreeInterval]
      simp only [List.foldl_append,List.foldl_cons,List.foldl_nil,dyadicExpansionEmbedding_apply]
      exact ⟨List.prefix_rfl,hl _⟩

@[simp] theorem ofExtension_node (l : DyadicTreeNode → DyadicTreeNode)
    (hl : ∀ t : DyadicTreeNode, t.IsPrefix (l t)) (r s : DyadicTreeNode) :
    (ofExtension l hl r).node s = s.foldl (fun t b => l t++[b]) r := rfl

@[simp] theorem ofExtension_fork (l : DyadicTreeNode → DyadicTreeNode)
    (hl : ∀ t : DyadicTreeNode, t.IsPrefix (l t)) (r s : DyadicTreeNode) :
    (ofExtension l hl r).fork s = l ((ofExtension l hl r).node s) := rfl

theorem ofExtension_node_snoc (l : DyadicTreeNode → DyadicTreeNode)
    (hl : ∀ t : DyadicTreeNode, t.IsPrefix (l t)) (r s : DyadicTreeNode) (b : Bool) :
    (ofExtension l hl r).node (s++[b]) = (ofExtension l hl r).fork s++[b] := by
  simp only [ofExtension_node,ofExtension_fork,List.foldl_append,List.foldl_cons,List.foldl_nil]

end DyadicDelayedFork
end ThesisCommon

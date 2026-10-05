import ThesisCommon.Analysis.DyadicRootedCellSegments

/-! Selected basis nodes with genuinely delayed branching forks. A node
lies in its own disjoint connecting cell, before the next fork. Prefix
reflection and injectivity follow from this concrete geometry. -/
noncomputable section
namespace ThesisCommon

structure DyadicDelayedFork where
  fork : DyadicSubtreeEmbedding
  node : DyadicTreeNode → DyadicTreeNode
  node_mem : ∀ s, node s ∈ dyadicRootedCell fork s

namespace DyadicDelayedFork

theorem node_injective (d : DyadicDelayedFork) : Function.Injective d.node := by
  intro s t h
  by_contra hst
  exact Finset.disjoint_left.mp (dyadicRootedCell_disjoint d.fork hst) (d.node_mem s)
    (h ▸ d.node_mem t)

def nodeEmbedding (d : DyadicDelayedFork) : DyadicTreeNode ↪ DyadicTreeNode :=
  ⟨d.node,d.node_injective⟩

theorem node_prefix_iff (d : DyadicDelayedFork) (s t : DyadicTreeNode) :
    (d.node s).IsPrefix (d.node t) ↔ s.IsPrefix t := by
  constructor
  · intro h
    exact dyadicRootedCell_index_prefix d.fork (d.node_mem s)
      (h.trans (dyadicRootedCell_prefix_endpoint d.fork (d.node_mem t)))
  · intro h
    by_cases heq : s=t
    · subst t; exact List.prefix_rfl
    · exact (dyadicRootedCell_prefix_endpoint d.fork (d.node_mem s)).trans
        (dyadicRootedCell_ancestor_prefix d.fork (d.node_mem t) h heq)

@[simp] theorem node_mem_cell_iff (d : DyadicDelayedFork) (s t : DyadicTreeNode) :
    d.node t ∈ dyadicRootedCell d.fork s ↔ t=s := by
  constructor
  · intro ht
    by_contra hts
    exact Finset.disjoint_left.mp (dyadicRootedCell_disjoint d.fork hts) (d.node_mem t) ht
  · rintro rfl; exact d.node_mem t

def pullback (d : DyadicDelayedFork) (A : Finset DyadicTreeNode) : Finset DyadicTreeNode :=
  A.preimage d.nodeEmbedding d.node_injective.injOn

@[simp] theorem mem_pullback (d : DyadicDelayedFork) (s : DyadicTreeNode)
    (A : Finset DyadicTreeNode) : s∈d.pullback A ↔ d.node s∈A := Finset.mem_preimage

theorem pullback_literal (d : DyadicDelayedFork) {A : Finset DyadicTreeNode}
    (hA : IsLiteralTreeSegment A) (hne : (d.pullback A).Nonempty) :
    IsLiteralTreeSegment (d.pullback A) := by
  refine ⟨hne,?_⟩
  intro s hs t ht
  rcases hA.2 (d.node s) ((d.mem_pullback s A).mp hs)
    (d.node t) ((d.mem_pullback t A).mp ht) with h | h
  · exact Or.inl ((d.node_prefix_iff s t).mp h)
  · exact Or.inr ((d.node_prefix_iff t s).mp h)

theorem pullback_consecutive (d : DyadicDelayedFork) {A : Finset DyadicTreeNode}
    (hA : IsConsecutiveTreeSegment A) (hne : (d.pullback A).Nonempty) :
    IsConsecutiveTreeSegment (d.pullback A) := by
  refine ⟨d.pullback_literal hA.1 hne,?_⟩
  intro s hs t ht u hsu hut
  apply (d.mem_pullback u A).mpr
  exact hA.2 (d.node s) ((d.mem_pullback s A).mp hs)
    (d.node t) ((d.mem_pullback t A).mp ht) (d.node u)
    ((d.node_prefix_iff s u).mpr hsu) ((d.node_prefix_iff u t).mpr hut)

theorem pullback_disjoint (d : DyadicDelayedFork) {A B : Finset DyadicTreeNode}
    (hAB : Disjoint A B) : Disjoint (d.pullback A) (d.pullback B) := by
  apply Finset.disjoint_left.mpr
  intro t ht hu
  exact Finset.disjoint_left.mp hAB ((d.mem_pullback t A).mp ht) ((d.mem_pullback t B).mp hu)

@[simp] theorem pullback_cell (d : DyadicDelayedFork) (s : DyadicTreeNode) :
    d.pullback (dyadicRootedCell d.fork s) = {s} := by
  classical
  ext t
  simp only [mem_pullback,node_mem_cell_iff,Finset.mem_singleton]

end DyadicDelayedFork
end ThesisCommon

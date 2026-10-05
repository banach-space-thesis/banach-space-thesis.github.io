import ThesisCommon.Analysis.DyadicRootedCells

/-! Replacing each selected node by its disjoint segment cell preserves
both segment conventions and disjointness of finite test families. -/
noncomputable section
namespace ThesisCommon

def dyadicRootedCells (e : DyadicSubtreeEmbedding) (A : Finset DyadicTreeNode) : Finset DyadicTreeNode :=
  A.biUnion (dyadicRootedCell e)

@[simp] theorem mem_dyadicRootedCells (e : DyadicSubtreeEmbedding) (A : Finset DyadicTreeNode)
    (x : DyadicTreeNode) : x ∈ dyadicRootedCells e A ↔ ∃ s ∈ A, x ∈ dyadicRootedCell e s :=
  Finset.mem_biUnion

theorem dyadicRootedCells_literal (e : DyadicSubtreeEmbedding) {A : Finset DyadicTreeNode}
    (hA : IsLiteralTreeSegment A) : IsLiteralTreeSegment (dyadicRootedCells e A) := by
  constructor
  · obtain ⟨s, hs⟩ := hA.1
    exact ⟨e s, (mem_dyadicRootedCells e A (e s)).mpr ⟨s, hs, dyadicRootedCell_self e s⟩⟩
  · intro x hx y hy
    obtain ⟨s, hs, hxs⟩ := (mem_dyadicRootedCells e A x).mp hx
    obtain ⟨t, ht, hyt⟩ := (mem_dyadicRootedCells e A y).mp hy
    rcases hA.2 s hs t ht with hst | hts
    · exact List.prefix_or_prefix_of_prefix
        ((dyadicRootedCell_prefix_endpoint e hxs).trans ((e.prefix_iff _ _).mpr hst))
        (dyadicRootedCell_prefix_endpoint e hyt)
    · exact List.prefix_or_prefix_of_prefix (dyadicRootedCell_prefix_endpoint e hxs)
        ((dyadicRootedCell_prefix_endpoint e hyt).trans ((e.prefix_iff _ _).mpr hts))

theorem dyadicRootedCells_consecutive (e : DyadicSubtreeEmbedding) {A : Finset DyadicTreeNode}
    (hA : IsConsecutiveTreeSegment A) : IsConsecutiveTreeSegment (dyadicRootedCells e A) := by
  refine ⟨dyadicRootedCells_literal e hA.1, ?_⟩
  intro x hx y hy z hxz hzy
  obtain ⟨s, hs, hxs⟩ := (mem_dyadicRootedCells e A x).mp hx
  obtain ⟨t, ht, hyt⟩ := (mem_dyadicRootedCells e A y).mp hy
  obtain ⟨u, hut, hzu⟩ := dyadicRootedCell_cover_prefix e t z
    (hzy.trans (dyadicRootedCell_prefix_endpoint e hyt))
  have hsu := dyadicRootedCell_index_prefix e hxs
    (hxz.trans (dyadicRootedCell_prefix_endpoint e hzu))
  exact (mem_dyadicRootedCells e A z).mpr ⟨u, hA.2 s hs t ht u hsu hut, hzu⟩

theorem dyadicRootedCells_disjoint (e : DyadicSubtreeEmbedding) {A B : Finset DyadicTreeNode}
    (hAB : Disjoint A B) : Disjoint (dyadicRootedCells e A) (dyadicRootedCells e B) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨s, hs, hxs⟩ := (mem_dyadicRootedCells e A x).mp hx
  obtain ⟨t, ht, hxt⟩ := (mem_dyadicRootedCells e B x).mp hy
  by_cases hst : s = t
  · subst t
    exact Finset.disjoint_left.mp hAB hs ht
  · exact Finset.disjoint_left.mp (dyadicRootedCell_disjoint e hst) hxs hxt

end ThesisCommon

import ThesisCommon.Analysis.DyadicSelectedCells

/-! Replacing each selected node by its disjoint segment cell preserves
both segment conventions and disjointness of finite test families. -/
noncomputable section
namespace ThesisCommon

def dyadicSelectedCells (e : DyadicSubtreeEmbedding) (A : Finset DyadicTreeNode) : Finset DyadicTreeNode :=
  A.biUnion (dyadicSelectedCell e)

@[simp] theorem mem_dyadicSelectedCells (e : DyadicSubtreeEmbedding) (A : Finset DyadicTreeNode)
    (x : DyadicTreeNode) : x ∈ dyadicSelectedCells e A ↔ ∃ s ∈ A, x ∈ dyadicSelectedCell e s :=
  Finset.mem_biUnion

theorem dyadicSelectedCells_literal (e : DyadicSubtreeEmbedding) {A : Finset DyadicTreeNode}
    (hA : IsLiteralTreeSegment A) : IsLiteralTreeSegment (dyadicSelectedCells e A) := by
  constructor
  · obtain ⟨s, hs⟩ := hA.1
    exact ⟨e s, (mem_dyadicSelectedCells e A (e s)).mpr ⟨s, hs, dyadicSelectedCell_self e s⟩⟩
  · intro x hx y hy
    obtain ⟨s, hs, hxs⟩ := (mem_dyadicSelectedCells e A x).mp hx
    obtain ⟨t, ht, hyt⟩ := (mem_dyadicSelectedCells e A y).mp hy
    rcases hA.2 s hs t ht with hst | hts
    · exact List.prefix_or_prefix_of_prefix
        ((dyadicSelectedCell_prefix_endpoint e hxs).trans ((e.prefix_iff _ _).mpr hst))
        (dyadicSelectedCell_prefix_endpoint e hyt)
    · exact List.prefix_or_prefix_of_prefix (dyadicSelectedCell_prefix_endpoint e hxs)
        ((dyadicSelectedCell_prefix_endpoint e hyt).trans ((e.prefix_iff _ _).mpr hts))

theorem dyadicSelectedCells_consecutive (e : DyadicSubtreeEmbedding) {A : Finset DyadicTreeNode}
    (hA : IsConsecutiveTreeSegment A) : IsConsecutiveTreeSegment (dyadicSelectedCells e A) := by
  refine ⟨dyadicSelectedCells_literal e hA.1, ?_⟩
  intro x hx y hy z hxz hzy
  obtain ⟨s, hs, hxs⟩ := (mem_dyadicSelectedCells e A x).mp hx
  obtain ⟨t, ht, hyt⟩ := (mem_dyadicSelectedCells e A y).mp hy
  obtain ⟨u, hut, hzu⟩ := dyadicSelectedCell_cover_prefix e t z
    ((dyadicSelectedCell_root_prefix e hxs).trans hxz)
    (hzy.trans (dyadicSelectedCell_prefix_endpoint e hyt))
  have hsu := dyadicSelectedCell_index_prefix e hxs
    (hxz.trans (dyadicSelectedCell_prefix_endpoint e hzu))
  exact (mem_dyadicSelectedCells e A z).mpr ⟨u, hA.2 s hs t ht u hsu hut, hzu⟩

theorem dyadicSelectedCells_disjoint (e : DyadicSubtreeEmbedding) {A B : Finset DyadicTreeNode}
    (hAB : Disjoint A B) : Disjoint (dyadicSelectedCells e A) (dyadicSelectedCells e B) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨s, hs, hxs⟩ := (mem_dyadicSelectedCells e A x).mp hx
  obtain ⟨t, ht, hxt⟩ := (mem_dyadicSelectedCells e B x).mp hy
  by_cases hst : s = t
  · subst t
    exact Finset.disjoint_left.mp hAB hs ht
  · exact Finset.disjoint_left.mp (dyadicSelectedCell_disjoint e hst) hxs hxt

end ThesisCommon

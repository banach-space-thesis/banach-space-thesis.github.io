import ThesisCommon.Analysis.DyadicSelectedCellSegments
import Mathlib.Data.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Preimage

/-! Pullback of tests along an actual selected strong subtree. Both segment
conventions are preserved; the cell above each selected node reads precisely
that node from an inserted finitely supported vector. -/
noncomputable section
namespace ThesisCommon

def selectedPullback (e : DyadicSubtreeEmbedding) (A : Finset DyadicTreeNode) :
    Finset DyadicTreeNode :=
  A.preimage e.toEmbedding e.toEmbedding.injective.injOn

@[simp] theorem mem_selectedPullback (e : DyadicSubtreeEmbedding)
    (t : DyadicTreeNode) (A : Finset DyadicTreeNode) :
    t ∈ selectedPullback e A ↔ e t ∈ A := Finset.mem_preimage

theorem literalTreeSegment_selectedPullback {A : Finset DyadicTreeNode}
    (hA : IsLiteralTreeSegment A) (e : DyadicSubtreeEmbedding)
    (hne : (selectedPullback e A).Nonempty) :
    IsLiteralTreeSegment (selectedPullback e A) := by
  refine ⟨hne, ?_⟩
  intro s hs t ht
  rcases hA.2 (e s) ((mem_selectedPullback e s A).mp hs)
    (e t) ((mem_selectedPullback e t A).mp ht) with h | h
  · exact Or.inl ((e.prefix_iff s t).mp h)
  · exact Or.inr ((e.prefix_iff t s).mp h)

theorem consecutiveTreeSegment_selectedPullback {A : Finset DyadicTreeNode}
    (hA : IsConsecutiveTreeSegment A) (e : DyadicSubtreeEmbedding)
    (hne : (selectedPullback e A).Nonempty) :
    IsConsecutiveTreeSegment (selectedPullback e A) := by
  refine ⟨literalTreeSegment_selectedPullback hA.1 e hne, ?_⟩
  intro s hs t ht v hsv hvt
  apply (mem_selectedPullback e v A).mpr
  exact hA.2 (e s) ((mem_selectedPullback e s A).mp hs)
    (e t) ((mem_selectedPullback e t A).mp ht) (e v)
    ((e.prefix_iff s v).mpr hsv) ((e.prefix_iff v t).mpr hvt)

theorem selectedPullback_disjoint (e : DyadicSubtreeEmbedding)
    {A B : Finset DyadicTreeNode} (h : Disjoint A B) :
    Disjoint (selectedPullback e A) (selectedPullback e B) := by
  apply Finset.disjoint_left.mpr
  intro t htA htB
  exact Finset.disjoint_left.mp h ((mem_selectedPullback e t A).mp htA)
    ((mem_selectedPullback e t B).mp htB)

theorem sum_mapDomain_selected {𝕜 : Type*} [AddCommMonoid 𝕜]
    (e : DyadicSubtreeEmbedding) (A : Finset DyadicTreeNode) (a : DyadicTreeNode →₀ 𝕜) :
    ∑ t ∈ A, (Finsupp.mapDomain e.toEmbedding a) t =
      ∑ t ∈ selectedPullback e A, a t := by
  classical
  have h := Finset.sum_preimage e.toEmbedding A e.toEmbedding.injective.injOn
    (Finsupp.mapDomain e.toEmbedding a)
    (fun t _ ht => Finsupp.mapDomain_notin_range a t ht)
  simpa only [selectedPullback, Finsupp.mapDomain_apply e.toEmbedding.injective]
    using h.symm

@[simp] theorem selectedPullback_cell (e : DyadicSubtreeEmbedding) (s : DyadicTreeNode) :
    selectedPullback e (dyadicSelectedCell e s) = {s} := by
  classical
  ext t
  simp only [mem_selectedPullback, dyadicSelectedCell_image_iff, Finset.mem_singleton]

end ThesisCommon

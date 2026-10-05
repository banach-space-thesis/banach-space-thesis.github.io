import ThesisCommon.Analysis.JamesTreeSegments
import Mathlib.Data.Finset.Image

/-! Genuine prefix subtrees preserve both recorded segment conventions.
These common structural facts do not choose the manuscript's intended norm. -/
noncomputable section
namespace ThesisCommon

def dyadicPrefixEmbedding (u : DyadicTreeNode) : DyadicTreeNode ↪ DyadicTreeNode where
  toFun t := u ++ t
  inj' := fun _ _ h => List.append_cancel_left h

@[simp] theorem dyadicPrefixEmbedding_apply (u t : DyadicTreeNode) :
    dyadicPrefixEmbedding u t = u ++ t := rfl

theorem literalTreeSegment_prefix {A : Finset DyadicTreeNode}
    (hA : IsLiteralTreeSegment A) (u : DyadicTreeNode) :
    IsLiteralTreeSegment (A.map (dyadicPrefixEmbedding u)) := by
  classical
  refine ⟨hA.1.map, ?_⟩
  intro s hs t ht
  obtain ⟨s', hs', rfl⟩ := Finset.mem_map.mp hs
  obtain ⟨t', ht', rfl⟩ := Finset.mem_map.mp ht
  simpa only [dyadicPrefixEmbedding_apply, List.prefix_append_right_inj] using hA.2 s' hs' t' ht'

theorem consecutiveTreeSegment_prefix {A : Finset DyadicTreeNode}
    (hA : IsConsecutiveTreeSegment A) (u : DyadicTreeNode) :
    IsConsecutiveTreeSegment (A.map (dyadicPrefixEmbedding u)) := by
  classical
  refine ⟨literalTreeSegment_prefix hA.1 u, ?_⟩
  intro s hs t ht v hsv hvt
  obtain ⟨s', hs', rfl⟩ := Finset.mem_map.mp hs
  obtain ⟨t', ht', rfl⟩ := Finset.mem_map.mp ht
  have huv : u.IsPrefix v := (List.prefix_append u s').trans hsv
  obtain ⟨w, rfl⟩ := huv
  have hsw : s'.IsPrefix w := (List.prefix_append_right_inj u).mp hsv
  have hwt : w.IsPrefix t' := (List.prefix_append_right_inj u).mp hvt
  exact Finset.mem_map.mpr ⟨w, hA.2 s' hs' t' ht' w hsw hwt, rfl⟩

theorem literalTreeSegment_filter_prefix {A : Finset DyadicTreeNode}
    (hA : IsLiteralTreeSegment A) (u : DyadicTreeNode)
    (hne : (A.filter (fun t => u.IsPrefix t)).Nonempty) :
    IsLiteralTreeSegment (A.filter (fun t => u.IsPrefix t)) := by
  classical
  exact ⟨hne, fun s hs t ht => hA.2 s (Finset.mem_filter.mp hs).1 t (Finset.mem_filter.mp ht).1⟩

theorem consecutiveTreeSegment_filter_prefix {A : Finset DyadicTreeNode}
    (hA : IsConsecutiveTreeSegment A) (u : DyadicTreeNode)
    (hne : (A.filter (fun t => u.IsPrefix t)).Nonempty) :
    IsConsecutiveTreeSegment (A.filter (fun t => u.IsPrefix t)) := by
  classical
  refine ⟨literalTreeSegment_filter_prefix hA.1 u hne, ?_⟩
  intro s hs t ht v hsv hvt
  obtain ⟨hs, hus⟩ := Finset.mem_filter.mp hs
  obtain ⟨ht, _⟩ := Finset.mem_filter.mp ht
  exact Finset.mem_filter.mpr ⟨hA.2 s hs t ht v hsv hvt, hus.trans hsv⟩

def JamesTreeTest.prefix {S : JamesTreeSegmentFamily} (T : JamesTreeTest S)
    (u : DyadicTreeNode)
    (hS : ∀ A, S.allows A → S.allows (A.map (dyadicPrefixEmbedding u))) : JamesTreeTest S where
  count := T.count
  segment j := (T.segment j).map (dyadicPrefixEmbedding u)
  allowed j := hS _ (T.allowed j)
  disjoint := by
    intro i j hij
    apply Finset.disjoint_left.mpr
    intro t ht hi
    obtain ⟨s, hs, rfl⟩ := Finset.mem_map.mp ht
    obtain ⟨r, hr, heq⟩ := Finset.mem_map.mp hi
    have hrs : r = s := (dyadicPrefixEmbedding u).injective heq
    subst r
    exact Finset.disjoint_left.mp (T.disjoint hij) hs hr

def literalJamesTreeTestPrefix (T : JamesTreeTest literalTreeSegmentFamily)
    (u : DyadicTreeNode) : JamesTreeTest literalTreeSegmentFamily :=
  T.prefix u (fun _ h => literalTreeSegment_prefix h u)

def consecutiveJamesTreeTestPrefix (T : JamesTreeTest consecutiveTreeSegmentFamily)
    (u : DyadicTreeNode) : JamesTreeTest consecutiveTreeSegmentFamily :=
  T.prefix u (fun _ h => consecutiveTreeSegment_prefix h u)

end ThesisCommon

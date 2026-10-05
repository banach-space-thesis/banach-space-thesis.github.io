import ThesisCommon.Analysis.DyadicSubtreeEmbeddings
import ThesisCommon.Analysis.JamesTreeFiniteLevels

/-! Actual finite intervals of the dyadic prefix order and the split
reflection property of the concrete subtree embeddings. -/
noncomputable section
namespace ThesisCommon

def dyadicTreeInterval (s t : DyadicTreeNode) : Finset DyadicTreeNode :=
  (dyadicInitialFinset t.length).filter (fun u => s.IsPrefix u ∧ u.IsPrefix t)

@[simp] theorem mem_dyadicTreeInterval (s t u : DyadicTreeNode) :
    u ∈ dyadicTreeInterval s t ↔ s.IsPrefix u ∧ u.IsPrefix t := by
  classical
  simp only [dyadicTreeInterval, Finset.mem_filter, mem_dyadicInitialFinset]
  exact ⟨fun h => h.2, fun h => ⟨h.2.length_le, h⟩⟩

theorem dyadicTreeInterval_consecutive {s t : DyadicTreeNode} (hst : s.IsPrefix t) :
    IsConsecutiveTreeSegment (dyadicTreeInterval s t) := by
  refine ⟨⟨⟨t, (mem_dyadicTreeInterval s t t).mpr ⟨hst, List.prefix_rfl⟩⟩, ?_⟩, ?_⟩
  · intro u hu v hv
    exact List.prefix_or_prefix_of_prefix ((mem_dyadicTreeInterval s t u).mp hu).2
      ((mem_dyadicTreeInterval s t v).mp hv).2
  · intro u hu v hv w huw hwv
    exact (mem_dyadicTreeInterval s t w).mpr
      ⟨((mem_dyadicTreeInterval s t u).mp hu).1.trans huw,
        hwv.trans ((mem_dyadicTreeInterval s t v).mp hv).2⟩

theorem dyadic_split_eq_of_common_extension {r t : DyadicTreeNode} {a b : Bool}
    (ha : (r ++ [a]).IsPrefix t) (hb : (r ++ [b]).IsPrefix t) : a = b := by
  rcases List.prefix_or_prefix_of_prefix ha hb with h | h
  · simpa using (List.prefix_append_right_inj r).mp h
  · exact (show b = a by simpa using (List.prefix_append_right_inj r).mp h).symm

theorem DyadicSubtreeEmbedding.split_prefix_iff (e : DyadicSubtreeEmbedding)
    (s t : DyadicTreeNode) (b : Bool) :
    (e s ++ [b]).IsPrefix (e t) ↔ (s ++ [b]).IsPrefix t := by
  constructor
  · intro h
    have hst : s.IsPrefix t := (e.prefix_iff s t).mp ((List.prefix_append (e s) [b]).trans h)
    obtain ⟨r, rfl⟩ := hst
    cases r with
    | nil =>
      have hlen := h.length_le
      simp only [List.append_nil, List.length_append, List.length_singleton] at hlen
      omega
    | cons a r =>
      have ha : (e s ++ [a]).IsPrefix (e (s ++ a :: r)) :=
        (e.split_prefix s a).trans ((e.prefix_iff _ _).mpr
          (by exact ⟨r, by simp only [List.append_assoc, List.singleton_append]⟩))
      have hab := dyadic_split_eq_of_common_extension h ha
      subst a
      exact ⟨r, by simp only [List.append_assoc, List.singleton_append]⟩
  · intro h
    exact (e.split_prefix s b).trans ((e.prefix_iff _ _).mpr h)

end ThesisCommon

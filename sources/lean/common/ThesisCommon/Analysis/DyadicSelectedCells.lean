import ThesisCommon.Analysis.DyadicTreeIntervals

/-! Disjoint finite segment cells attached to the nodes of a selected
subtree. They partition its connecting paths, and each cell contains exactly
its own selected node. -/
noncomputable section
namespace ThesisCommon

def dyadicSelectedCell (e : DyadicSubtreeEmbedding) (s : DyadicTreeNode) : Finset DyadicTreeNode :=
  match s.reverse with
  | [] => {e []}
  | b :: r => dyadicTreeInterval (e r.reverse ++ [b]) (e s)

@[simp] theorem dyadicSelectedCell_nil (e : DyadicSubtreeEmbedding) :
    dyadicSelectedCell e [] = {e []} := rfl

@[simp] theorem dyadicSelectedCell_snoc (e : DyadicSubtreeEmbedding) (s : DyadicTreeNode) (b : Bool) :
    dyadicSelectedCell e (s ++ [b]) = dyadicTreeInterval (e s ++ [b]) (e (s ++ [b])) := by
  simp [dyadicSelectedCell, List.reverse_append]

theorem dyadicSelectedCell_consecutive (e : DyadicSubtreeEmbedding) (s : DyadicTreeNode) :
    IsConsecutiveTreeSegment (dyadicSelectedCell e s) := by
  induction s using List.reverseRecOn with
  | nil => exact consecutiveTreeSegment_singleton (e [])
  | append_singleton s b _ =>
    rw [dyadicSelectedCell_snoc]
    exact dyadicTreeInterval_consecutive (e.split_prefix s b)

theorem dyadicSelectedCell_self (e : DyadicSubtreeEmbedding) (s : DyadicTreeNode) :
    e s ∈ dyadicSelectedCell e s := by
  induction s using List.reverseRecOn with
  | nil => simp
  | append_singleton s b _ =>
    rw [dyadicSelectedCell_snoc, mem_dyadicTreeInterval]
    exact ⟨e.split_prefix s b, List.prefix_rfl⟩

theorem dyadicSelectedCell_prefix_endpoint (e : DyadicSubtreeEmbedding)
    {s x : DyadicTreeNode} (hx : x ∈ dyadicSelectedCell e s) : x.IsPrefix (e s) := by
  induction s using List.reverseRecOn with
  | nil =>
    have h : x = e [] := by simpa only [dyadicSelectedCell_nil, Finset.mem_singleton] using hx
    rw [h]
  | append_singleton s b _ =>
    exact ((mem_dyadicTreeInterval _ _ _).mp (dyadicSelectedCell_snoc e s b ▸ hx)).2

theorem dyadicSelectedCell_root_prefix (e : DyadicSubtreeEmbedding)
    {s x : DyadicTreeNode} (hx : x ∈ dyadicSelectedCell e s) : (e []).IsPrefix x := by
  induction s using List.reverseRecOn with
  | nil =>
    have h : x = e [] := by simpa only [dyadicSelectedCell_nil, Finset.mem_singleton] using hx
    rw [h]
  | append_singleton s b _ =>
    have h := ((mem_dyadicTreeInterval _ _ _).mp (dyadicSelectedCell_snoc e s b ▸ hx)).1
    exact (e.root_prefix s).trans ((List.prefix_append (e s) [b]).trans h)

theorem dyadicSelectedCell_index_prefix (e : DyadicSubtreeEmbedding)
    {s t x : DyadicTreeNode} (hx : x ∈ dyadicSelectedCell e s) (hxt : x.IsPrefix (e t)) :
    s.IsPrefix t := by
  induction s using List.reverseRecOn with
  | nil => simp
  | append_singleton s b _ =>
    have h := ((mem_dyadicTreeInterval _ _ _).mp (dyadicSelectedCell_snoc e s b ▸ hx)).1
    exact (e.split_prefix_iff s t b).mp (h.trans hxt)

theorem dyadicSelectedCell_disjoint (e : DyadicSubtreeEmbedding) :
    Pairwise (fun s t => Disjoint (dyadicSelectedCell e s) (dyadicSelectedCell e t)) := by
  intro s t hst
  apply Finset.disjoint_left.mpr
  intro x hxs hxt
  have hs := dyadicSelectedCell_index_prefix e hxs (dyadicSelectedCell_prefix_endpoint e hxt)
  have ht := dyadicSelectedCell_index_prefix e hxt (dyadicSelectedCell_prefix_endpoint e hxs)
  exact hst (hs.eq_of_length (hs.length_le.antisymm ht.length_le))

@[simp] theorem dyadicSelectedCell_image_iff (e : DyadicSubtreeEmbedding) (s t : DyadicTreeNode) :
    e t ∈ dyadicSelectedCell e s ↔ t = s := by
  constructor
  · intro h
    have hts := (e.prefix_iff t s).mp (dyadicSelectedCell_prefix_endpoint e h)
    have hst := dyadicSelectedCell_index_prefix e h List.prefix_rfl
    exact hts.eq_of_length (hts.length_le.antisymm hst.length_le)
  · rintro rfl
    exact dyadicSelectedCell_self e t

theorem dyadicSelectedCell_cover_prefix (e : DyadicSubtreeEmbedding)
    (t x : DyadicTreeNode) (hroot : (e []).IsPrefix x) (hxt : x.IsPrefix (e t)) :
    ∃ s, s.IsPrefix t ∧ x ∈ dyadicSelectedCell e s := by
  induction t using List.reverseRecOn with
  | nil =>
    have h : x = e [] := hxt.eq_of_length (hxt.length_le.antisymm hroot.length_le)
    exact ⟨[], List.prefix_rfl, by simpa only [h] using dyadicSelectedCell_self e []⟩
  | append_singleton t b ih =>
    by_cases hp : x.IsPrefix (e t)
    · obtain ⟨s, hs, hx⟩ := ih hp
      exact ⟨s, hs.trans (List.prefix_append t [b]), hx⟩
    · have hept : (e t).IsPrefix (e (t ++ [b])) :=
        (e.prefix_iff _ _).mpr (List.prefix_append t [b])
      have hpx : (e t).IsPrefix x :=
        (List.prefix_or_prefix_of_prefix hxt hept).resolve_left hp
      have hlen : (e t).length < x.length := by
        by_contra h
        have heq := hpx.eq_of_length (by have := hpx.length_le; omega)
        exact hp (by rw [← heq])
      have hlower : (e t ++ [b]).IsPrefix x :=
        List.prefix_of_prefix_length_le (e.split_prefix t b) hxt
          (by simpa only [List.length_append, List.length_singleton] using hlen)
      refine ⟨t ++ [b], List.prefix_rfl, ?_⟩
      rw [dyadicSelectedCell_snoc, mem_dyadicTreeInterval]
      exact ⟨hlower, hxt⟩

end ThesisCommon

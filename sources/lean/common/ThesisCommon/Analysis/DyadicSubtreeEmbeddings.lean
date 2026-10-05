import ThesisCommon.Analysis.JamesTreeSegments

/-! Actual dyadic subtree embeddings with preserved left/right splits.
The recursive construction works for arbitrary state spaces and will be
used to fuse successively selected subtrees. -/
noncomputable section
namespace ThesisCommon

structure DyadicSubtreeEmbedding where
  toEmbedding : DyadicTreeNode ↪ DyadicTreeNode
  prefix_iff : ∀ s t, (toEmbedding s).IsPrefix (toEmbedding t) ↔ s.IsPrefix t
  split_prefix : ∀ s b, (toEmbedding s ++ [b]).IsPrefix (toEmbedding (s ++ [b]))

instance : CoeFun DyadicSubtreeEmbedding (fun _ => DyadicTreeNode → DyadicTreeNode) :=
  ⟨fun e => e.toEmbedding⟩

namespace DyadicSubtreeEmbedding

def cone (u : DyadicTreeNode) : DyadicSubtreeEmbedding where
  toEmbedding := ⟨fun s => u ++ s, fun _ _ h => List.append_cancel_left h⟩
  prefix_iff := fun _ _ => List.prefix_append_right_inj u
  split_prefix := fun s b => by
    change ((u ++ s) ++ [b]).IsPrefix (u ++ (s ++ [b]))
    rw [List.append_assoc]

def comp (f g : DyadicSubtreeEmbedding) : DyadicSubtreeEmbedding where
  toEmbedding := g.toEmbedding.trans f.toEmbedding
  prefix_iff := fun s t => (f.prefix_iff _ _).trans (g.prefix_iff s t)
  split_prefix := fun s b => (f.split_prefix (g s) b).trans
    ((f.prefix_iff _ _).mpr (g.split_prefix s b))

@[simp] theorem comp_apply (f g : DyadicSubtreeEmbedding) (s : DyadicTreeNode) :
    f.comp g s = f (g s) := rfl

@[simp] theorem cone_apply (u s : DyadicTreeNode) : cone u s = u ++ s := rfl

theorem root_prefix (e : DyadicSubtreeEmbedding) (s : DyadicTreeNode) :
    (e []).IsPrefix (e s) := (e.prefix_iff [] s).mpr (by simp)

end DyadicSubtreeEmbedding

section Expansion
variable {σ : Type*} (step : σ → Bool → σ) (node : σ → DyadicTreeNode)
  (hs : ∀ r b, (node r ++ [b]).IsPrefix (node (step r b)))
include hs

theorem dyadicExpansion_root_prefix (r : σ) (s : DyadicTreeNode) :
    (node r).IsPrefix (node (s.foldl step r)) := by
  induction s generalizing r with
  | nil => exact List.prefix_rfl
  | cons b s ih =>
    exact (List.prefix_append (node r) [b]).trans ((hs r b).trans (ih (step r b)))

theorem dyadicExpansion_prefix_iff (r : σ) (s t : DyadicTreeNode) :
    (node (s.foldl step r)).IsPrefix (node (t.foldl step r)) ↔ s.IsPrefix t := by
  induction s generalizing r t with
  | nil =>
    simp only [List.foldl_nil, List.nil_prefix, iff_true]
    exact dyadicExpansion_root_prefix step node hs r t
  | cons a s ih =>
    cases t with
    | nil =>
      simp only [List.foldl_cons, List.foldl_nil, List.prefix_nil, List.cons_ne_nil, iff_false]
      intro h
      have hlen := ((hs r a).trans (dyadicExpansion_root_prefix step node hs (step r a) s)).length_le
      have hlen' := h.length_le
      simp only [List.length_append, List.length_singleton] at hlen
      omega
    | cons b t =>
      simp only [List.foldl_cons, List.cons_prefix_cons]
      constructor
      · intro h
        have ha := (hs r a).trans (dyadicExpansion_root_prefix step node hs (step r a) s)
        have hb := (hs r b).trans (dyadicExpansion_root_prefix step node hs (step r b) t)
        have hab : a = b := by
          rcases List.prefix_or_prefix_of_prefix (ha.trans h) hb with h' | h'
          · simpa using (List.prefix_append_right_inj (node r)).mp h'
          · exact (show b = a by simpa using (List.prefix_append_right_inj (node r)).mp h').symm
        subst b
        exact ⟨rfl, (ih (step r a) t).mp h⟩
      · rintro ⟨rfl, h⟩
        exact (ih (step r a) t).mpr h

def dyadicExpansionEmbedding (r : σ) : DyadicSubtreeEmbedding where
  toEmbedding := {
    toFun := fun s => node (s.foldl step r)
    inj' := by
      intro s t h
      dsimp only at h
      have hst := (dyadicExpansion_prefix_iff step node hs r s t).mp
        (show (node (s.foldl step r)).IsPrefix (node (t.foldl step r)) by rw [h])
      have hts := (dyadicExpansion_prefix_iff step node hs r t s).mp
        (show (node (t.foldl step r)).IsPrefix (node (s.foldl step r)) by rw [h])
      exact hst.eq_of_length (hst.length_le.antisymm hts.length_le) }
  prefix_iff := dyadicExpansion_prefix_iff step node hs r
  split_prefix := fun s b => by
    change (node (s.foldl step r) ++ [b]).IsPrefix (node ((s ++ [b]).foldl step r))
    simpa only [List.foldl_append, List.foldl_cons, List.foldl_nil] using hs (s.foldl step r) b

@[simp] theorem dyadicExpansionEmbedding_apply (r : σ) (s : DyadicTreeNode) :
    dyadicExpansionEmbedding step node hs r s = node (s.foldl step r) := rfl

end Expansion
end ThesisCommon

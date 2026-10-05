import ThesisCommon.Analysis.DyadicDelayedForkSelection
import ThesisCommon.Analysis.DyadicTreeFrontierUpdates

/-! The lower endpoints of the actual connecting cells, including the
initial root interval, and their stability under a frontier update. -/
noncomputable section
namespace ThesisCommon

def dyadicCellAnchor (e : DyadicSubtreeEmbedding) (s : DyadicTreeNode) : DyadicTreeNode :=
  match s.reverse with
  | [] => []
  | b :: r => e r.reverse ++ [b]

@[simp] theorem dyadicCellAnchor_nil (e : DyadicSubtreeEmbedding) :
    dyadicCellAnchor e [] = [] := rfl

@[simp] theorem dyadicCellAnchor_snoc (e : DyadicSubtreeEmbedding)
    (s : DyadicTreeNode) (b : Bool) :
    dyadicCellAnchor e (s++[b]) = e s++[b] := by
  simp [dyadicCellAnchor,List.reverse_append]

theorem dyadicRootedCell_eq_interval (e : DyadicSubtreeEmbedding) (s : DyadicTreeNode) :
    dyadicRootedCell e s = dyadicTreeInterval (dyadicCellAnchor e s) (e s) := by
  induction s using List.reverseRecOn with
  | nil => simp only [dyadicRootedCell_nil,dyadicCellAnchor_nil]
  | append_singleton s b _ => simp only [dyadicRootedCell_snoc,dyadicCellAnchor_snoc]

theorem dyadicCellAnchor_prefix_node (d : DyadicDelayedFork)
    (e : DyadicSubtreeEmbedding) (s : DyadicTreeNode) :
    (dyadicCellAnchor (d.fork.comp e) s).IsPrefix (d.node (e s)) := by
  have h := (d.comp e).node_mem s
  rw [dyadicRootedCell_eq_interval,mem_dyadicTreeInterval] at h
  exact h.1

theorem dyadicCellAnchor_eq_of_frontier_agreement (d : DyadicDelayedFork)
    (n : ℕ) (e e' : DyadicSubtreeEmbedding)
    (he : ∀ t, dyadicTreeEnumeration.symm t < n → e' t=e t)
    {s : DyadicTreeNode} (hs : s∈dyadicTreeFrontier n) :
    dyadicCellAnchor (d.fork.comp e') s = dyadicCellAnchor (d.fork.comp e) s := by
  induction s using List.reverseRecOn with
  | nil => simp only [dyadicCellAnchor_nil]
  | append_singleton s b _ =>
    rw [dyadicCellAnchor_snoc,dyadicCellAnchor_snoc]
    have hidx := ((mem_dyadicTreeFrontier n _).mp hs).2 s (List.prefix_append _ _)
      (by intro h; have := congrArg List.length h; simp only [List.length_append,List.length_singleton] at this; omega)
    change d.fork (e' s)++[b]=d.fork (e s)++[b]
    rw [he s hidx]

theorem dyadicDelayedFork_child_node_length (d : DyadicDelayedFork)
    (e : DyadicSubtreeEmbedding) (s : DyadicTreeNode) (b : Bool) :
    (d.fork (e s)).length < (d.node (e (s++[b]))).length := by
  have h := dyadicRootedCell_split_prefix d.fork (d.node_mem (e (s++[b])))
    (e.split_prefix s b)
  have hh := h.length_le
  simp only [List.length_append,List.length_singleton] at hh
  omega

end ThesisCommon

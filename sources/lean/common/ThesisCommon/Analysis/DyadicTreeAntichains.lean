import ThesisCommon.Analysis.JamesTreeAntichainNorms

/-! An explicit infinite antichain of strict descendants of any dyadic node.
Prefix-preserving and prefix-reflecting embeddings carry it into any genuine
embedded subtree. -/
noncomputable section
namespace ThesisCommon

theorem dyadic_comb_prefix_iff (n m : ℕ) :
    (List.replicate n false ++ [true]).IsPrefix (List.replicate m false ++ [true]) ↔ n = m := by
  induction n generalizing m with
  | zero => cases m <;> simp [List.replicate_succ]
  | succ n ih => cases m <;> simp [List.replicate_succ, ih]

def dyadicCombEmbedding (u : DyadicTreeNode) : ℕ ↪ DyadicTreeNode where
  toFun n := u ++ (List.replicate n false ++ [true])
  inj' := by
    intro n m h
    have hlen := congrArg List.length h
    simpa only [List.length_append, List.length_replicate, List.length_singleton,
      Nat.add_left_cancel_iff, Nat.add_right_cancel_iff] using hlen

theorem dyadicCombEmbedding_antichain (u : DyadicTreeNode) :
    IsTreeAntichainEmbedding (dyadicCombEmbedding u) := by
  intro n m hnm h
  apply hnm
  exact (dyadic_comb_prefix_iff n m).mp ((List.prefix_append_right_inj u).mp h)

theorem dyadicCombEmbedding_prefix (u : DyadicTreeNode) (n : ℕ) :
    u.IsPrefix (dyadicCombEmbedding u n) := ⟨_, rfl⟩

theorem dyadicCombEmbedding_ne (u : DyadicTreeNode) (n : ℕ) :
    dyadicCombEmbedding u n ≠ u := by
  intro h
  have hlen := congrArg List.length h
  simp only [dyadicCombEmbedding, Function.Embedding.coeFn_mk, List.length_append,
    List.length_replicate, List.length_singleton] at hlen
  omega

theorem treeAntichainEmbedding_comp (f : DyadicTreeNode ↪ DyadicTreeNode)
    (hf : ∀ s t, (f s).IsPrefix (f t) → s.IsPrefix t)
    {ι : Type*} (e : ι ↪ DyadicTreeNode) (he : IsTreeAntichainEmbedding e) :
    IsTreeAntichainEmbedding (e.trans f) :=
  fun i j hij h => he i j hij (hf _ _ h)

end ThesisCommon

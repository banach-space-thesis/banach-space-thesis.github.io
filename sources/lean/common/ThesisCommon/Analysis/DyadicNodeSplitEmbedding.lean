import ThesisCommon.Analysis.DyadicSubtreeEmbeddings

/-! Every actual node map preserving the two immediate split directions
determines a strong prefix-order embedding. -/
noncomputable section
namespace ThesisCommon

theorem dyadic_append_fold (s t : DyadicTreeNode) :
    t.foldl (fun u b => u ++ [b]) s = s ++ t := by
  induction t generalizing s with
  | nil => simp only [List.foldl_nil,List.append_nil]
  | cons b t ih =>
    simp only [List.foldl_cons,ih,List.append_assoc,List.singleton_append]

def dyadicSubtreeEmbeddingOfSplit (f : DyadicTreeNode → DyadicTreeNode)
    (hf : ∀ s b, (f s ++ [b]).IsPrefix (f (s ++ [b]))) : DyadicSubtreeEmbedding :=
  dyadicExpansionEmbedding (fun s b => s ++ [b]) f hf []

@[simp] theorem dyadicSubtreeEmbeddingOfSplit_apply (f : DyadicTreeNode → DyadicTreeNode)
    (hf : ∀ s b, (f s ++ [b]).IsPrefix (f (s ++ [b]))) (s : DyadicTreeNode) :
    dyadicSubtreeEmbeddingOfSplit f hf s = f s := by
  simp only [dyadicSubtreeEmbeddingOfSplit,dyadicExpansionEmbedding_apply,
    dyadic_append_fold,List.nil_append]

end ThesisCommon

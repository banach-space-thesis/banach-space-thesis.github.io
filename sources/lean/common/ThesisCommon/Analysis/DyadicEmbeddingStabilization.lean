import ThesisCommon.Analysis.DyadicTreeFrontierOrder
import ThesisCommon.Analysis.DyadicNodeSplitEmbedding

/-! Stabilization of actual strong subtree embeddings when every processed
node is kept fixed. The limiting tree reads each node after its processing
stage, and its split identities hold at one common finite later stage. -/
noncomputable section
namespace ThesisCommon

theorem dyadicEmbeddingStages_eq (e : ℕ → DyadicSubtreeEmbedding)
    (he : ∀ n t, dyadicTreeEnumeration.symm t < n → e (n+1) t = e n t)
    {t : DyadicTreeNode} {m n : ℕ} (ht : dyadicTreeEnumeration.symm t < m) (hmn : m ≤ n) :
    e n t = e m t := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hmn
  clear hmn
  induction k with
  | zero => rfl
  | succ k ih =>
    exact (he (m+k) t (ht.trans_le (Nat.le_add_right m k))).trans ih

def dyadicStabilizedNode (e : ℕ → DyadicSubtreeEmbedding) (t : DyadicTreeNode) : DyadicTreeNode :=
  e (dyadicTreeEnumeration.symm t + 1) t

theorem dyadicStabilizedNode_eq_stage (e : ℕ → DyadicSubtreeEmbedding)
    (he : ∀ n t, dyadicTreeEnumeration.symm t < n → e (n+1) t = e n t)
    {t : DyadicTreeNode} {n : ℕ} (ht : dyadicTreeEnumeration.symm t < n) :
    dyadicStabilizedNode e t = e n t :=
  (dyadicEmbeddingStages_eq e he (Nat.lt_succ_self _) (Nat.succ_le_of_lt ht)).symm

theorem dyadicStabilizedNode_split (e : ℕ → DyadicSubtreeEmbedding)
    (he : ∀ n t, dyadicTreeEnumeration.symm t < n → e (n+1) t = e n t) :
    ∀ t b, (dyadicStabilizedNode e t ++ [b]).IsPrefix (dyadicStabilizedNode e (t ++ [b])) := by
  intro t b
  let N := max (dyadicTreeEnumeration.symm t) (dyadicTreeEnumeration.symm (t ++ [b])) + 1
  have ht : dyadicTreeEnumeration.symm t < N := Nat.lt_succ_of_le (le_max_left _ _)
  have hc : dyadicTreeEnumeration.symm (t ++ [b]) < N := Nat.lt_succ_of_le (le_max_right _ _)
  rw [dyadicStabilizedNode_eq_stage e he ht,dyadicStabilizedNode_eq_stage e he hc]
  exact (e N).split_prefix t b

def dyadicStabilizedEmbedding (e : ℕ → DyadicSubtreeEmbedding)
    (he : ∀ n t, dyadicTreeEnumeration.symm t < n → e (n+1) t = e n t) : DyadicSubtreeEmbedding :=
  dyadicSubtreeEmbeddingOfSplit (dyadicStabilizedNode e) (dyadicStabilizedNode_split e he)

@[simp] theorem dyadicStabilizedEmbedding_apply (e : ℕ → DyadicSubtreeEmbedding)
    (he : ∀ n t, dyadicTreeEnumeration.symm t < n → e (n+1) t = e n t) (t : DyadicTreeNode) :
    dyadicStabilizedEmbedding e he t = e (dyadicTreeEnumeration.symm t+1) t := by
  simp only [dyadicStabilizedEmbedding,dyadicSubtreeEmbeddingOfSplit_apply,dyadicStabilizedNode]

theorem dyadicStabilizedEmbedding_eq_stage (e : ℕ → DyadicSubtreeEmbedding)
    (he : ∀ n t, dyadicTreeEnumeration.symm t < n → e (n+1) t = e n t)
    {t : DyadicTreeNode} {n : ℕ} (ht : dyadicTreeEnumeration.symm t < n) :
    dyadicStabilizedEmbedding e he t = e n t := by
  simpa only [dyadicStabilizedEmbedding,dyadicSubtreeEmbeddingOfSplit_apply] using
    dyadicStabilizedNode_eq_stage e he ht

end ThesisCommon

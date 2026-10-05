import ThesisCommon.Analysis.SupportingTree
import ThesisCommon.Analysis.NatTreeEmbedding

/-! The first construction in CKL selection: backward infinite support
produces an actual full infinitely splitting subtree of supporting terminals.
This contains no off-diagonal or isometry assertion.
-/
noncomputable section
namespace ThesisCommon

/-- Backward support constructs all successor injections coherently. -/
theorem InfinitelySupported.exists_tree {n : ℕ} {P : (Fin n → ℕ) → Prop}
    (h : InfinitelySupported n P) :
    ∃ f : NatTreeEmbedding n, ∀ t, P (f.map t) := by
  classical
  induction n with
  | zero =>
    refine ⟨PUnit.unit, ?_⟩
    intro t
    have ht : t = Fin.elim0 := Subsingleton.elim _ _
    simpa only [NatTreeEmbedding.map, ht] using h
  | succ n ih =>
    let A : Set ℕ := {i | InfinitelySupported n (fun t => P (Fin.cons i t))}
    have hA : A.Infinite := h
    let g : ℕ ↪ A := hA.natEmbedding A
    have hg (i : ℕ) : ∃ f : NatTreeEmbedding n,
        ∀ t, P (Fin.cons (g i).val (f.map t)) := ih (g i).property
    choose f hf using hg
    let e : ℕ ↪ ℕ := g.trans (Function.Embedding.subtype _)
    refine ⟨(e, f), ?_⟩
    intro t
    exact hf (t 0) (Fin.tail t)

end ThesisCommon

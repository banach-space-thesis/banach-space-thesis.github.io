import ThesisCommon.Analysis.NatTreeEmbedding

/-! Composition of full tree embeddings and thinning only the last-level
successors. Earlier levels remain unchanged, so the resulting subtree still
splits infinitely at every node.
-/
noncomputable section
namespace ThesisCommon
namespace NatTreeEmbedding

def comp : {n : ℕ} → NatTreeEmbedding n → NatTreeEmbedding n → NatTreeEmbedding n
  | 0, _, _ => PUnit.unit
  | _ + 1, f, g => (g.1.trans f.1, fun i => comp (f.2 (g.1 i)) (g.2 i))

theorem map_comp {n : ℕ} (f g : NatTreeEmbedding n) (t : Fin n → ℕ) :
    (f.comp g).map t = f.map (g.map t) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Fin.cons (n := n) (α := fun _ => ℕ) (f.1 (g.1 (t 0)))
      (((f.2 (g.1 (t 0))).comp (g.2 (t 0))).map (Fin.tail t)) = _
    simp only [map, Fin.cons_zero, Fin.tail_cons, ih]

/-- Prescribe an independent injection of final successors below each
prefix, keeping every earlier coordinate unchanged. -/
def leafReindex : {n : ℕ} → ((Fin n → ℕ) → (ℕ ↪ ℕ)) → NatTreeEmbedding (n + 1)
  | 0, f => (f Fin.elim0, fun _ => PUnit.unit)
  | _ + 1, f => (Function.Embedding.refl ℕ, fun i => leafReindex (fun p => f (Fin.cons i p)))

theorem map_leafReindex_snoc {n : ℕ} (f : (Fin n → ℕ) → (ℕ ↪ ℕ))
    (p : Fin n → ℕ) (j : ℕ) :
    (leafReindex f).map (Fin.snoc p j) = Fin.snoc p (f p j) := by
  induction n with
  | zero =>
    have hp : p = Fin.elim0 := Subsingleton.elim _ _
    subst p
    funext i
    have hi : i = Fin.last 0 := Fin.ext (by omega)
    subst i
    rfl
  | succ n ih =>
    rw [← Fin.cons_self_tail p, ← Fin.cons_snoc_eq_snoc_cons]
    change Fin.cons (n := n + 1) (α := fun _ => ℕ) (p 0)
      ((leafReindex (fun q => f (Fin.cons (p 0) q))).map
      (Fin.snoc (Fin.tail p) j)) = _
    rw [ih, Fin.cons_snoc_eq_snoc_cons]

theorem map_leafReindex {n : ℕ} (f : (Fin n → ℕ) → (ℕ ↪ ℕ)) (t : Fin (n + 1) → ℕ) :
    (leafReindex f).map t = Fin.snoc (Fin.init t) (f (Fin.init t) (t (Fin.last n))) := by
  conv_lhs => rw [← Fin.snoc_init_self t]
  exact map_leafReindex_snoc f _ _

end NatTreeEmbedding
end ThesisCommon

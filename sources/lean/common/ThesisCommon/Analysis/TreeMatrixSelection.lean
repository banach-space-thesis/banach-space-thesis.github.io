import ThesisCommon.Analysis.TreeLeafReindex
import ThesisCommon.Analysis.MatrixFiberSelection

/-! Simultaneous matrix selection on a full finite-depth subtree. Enumerate
all domain terminals and choose their images one by one from the prescribed
final-successor fibre. Injectivity gives infinitely many successors in every
fibre, while earlier levels are unchanged. Thus no arbitrary subsequence is
substituted for the required full tree.
-/
noncomputable section
open Filter Topology
namespace ThesisCommon

theorem tree_matrix_selection {n : ℕ} (e : ℕ ≃ (Fin (n + 1) → ℕ))
    (g : NatTreeEmbedding (n + 1)) (w : ℕ → ℕ → ℝ)
    (hrow : ∀ m, Tendsto (w m) atTop (𝓝 0))
    (hcol : ∀ m, Tendsto (fun k => w k m) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ f : NatTreeEmbedding (n + 1),
      (∀ t, ∃ s, f.map t = g.map s) ∧
      ∀ i j, i ≠ j → w (e.symm (f.map (e i))) (e.symm (f.map (e j))) <
        ε / (2 : ℝ) ^ (i + j + 3) := by
  classical
  let c (k j : ℕ) : ℕ := e.symm (g.map (Fin.snoc (Fin.init (e k)) j))
  have hc (k : ℕ) : Function.Injective (c k) := by
    intro i j hij
    have ht := g.map_injective (e.symm.injective hij)
    simpa only [Fin.snoc_last] using congrFun ht (Fin.last n)
  obtain ⟨r, hr, hmem, hsmall⟩ := matrix_fiber_selection w hrow hcol
    (fun k => Set.range (c k)) (fun k => Set.infinite_range_of_injective (hc k)) hε
  choose a ha using hmem
  have ha' (k : ℕ) : e.symm (g.map (Fin.snoc (Fin.init (e k)) (a k))) = r k := ha k
  let lastMap (p : Fin n → ℕ) : ℕ ↪ ℕ :=
    { toFun := fun j => a (e.symm (Fin.snoc p j))
      inj' := by
        intro i j hij
        dsimp only at hij
        have hei := ha' (e.symm (Fin.snoc p i))
        have hej := ha' (e.symm (Fin.snoc p j))
        simp only [e.apply_symm_apply, Fin.init_snoc] at hei hej
        have he : r (e.symm (Fin.snoc p i)) = r (e.symm (Fin.snoc p j)) := by
          rw [← hei, ← hej, hij]
        have ht := e.symm.injective (hr.injective he)
        simpa only [Fin.snoc_last] using congrFun ht (Fin.last n) }
  let f := g.comp (NatTreeEmbedding.leafReindex lastMap)
  have hf (k : ℕ) : e.symm (f.map (e k)) = r k := by
    rw [NatTreeEmbedding.map_comp, NatTreeEmbedding.map_leafReindex]
    change e.symm (g.map (Fin.snoc (Fin.init (e k))
      (a (e.symm (Fin.snoc (Fin.init (e k)) ((e k) (Fin.last n))))))) = r k
    rw [Fin.snoc_init_self, e.symm_apply_apply]
    exact ha' k
  refine ⟨f, ?_, ?_⟩
  · intro t
    exact ⟨(NatTreeEmbedding.leafReindex lastMap).map t, NatTreeEmbedding.map_comp g _ t⟩
  · intro i j hij
    rw [hf, hf]
    exact hsmall i j hij

end ThesisCommon

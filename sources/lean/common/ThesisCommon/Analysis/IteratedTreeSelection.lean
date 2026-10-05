import ThesisCommon.Analysis.IteratedSchauderWeaklyNull
import ThesisCommon.Analysis.SupportingSubtree
import ThesisCommon.Analysis.TreeMatrixSelection
import ThesisCommon.Analysis.IteratedTreeCompression

/-! CKL selection on the actual iterated space. Backward support gives an
initial full subtree. Thinning its last-level fibres gives all off-diagonal
estimates simultaneously while retaining the diagonal support condition.
-/
noncomputable section
open Filter Topology
universe u v
namespace ThesisCommon
variable {𝕜 : Type u} [RCLike 𝕜]

theorem iterated_tree_selection (first : BasisSumFactor.{u,v} 𝕜)
    (tail : List (BasisSumFactor.{u,v} 𝕜))
    (h : ∀ F ∈ first :: tail, F.basis.HasSymmetricNorm ∧ ¬ F.basis.EquivalentEllOne)
    (T : (iteratedSchauderSum first tail).Carrier →L[𝕜]
      (iteratedSchauderSum first tail).Carrier) {η : ℝ} (hη : 0 < η)
    (hs : InfinitelySupported (tail.length + 1) (fun t => (1 / 2 : ℝ) ≤
      ‖iteratedBasisCoordinate first tail t (T (iteratedBasisVector first tail t))‖)) :
    ∃ f : NatTreeEmbedding (tail.length + 1),
      (∀ t, (1 / 2 : ℝ) ≤ ‖iteratedBasisCoordinate first tail (f.map t)
        (T (iteratedBasisVector first tail (f.map t)))‖) ∧
      ∀ i j, i ≠ j → ‖iteratedBasisCoordinate first tail
        (f.map (natTupleEnumeration tail.length i))
        (T (iteratedBasisVector first tail (f.map (natTupleEnumeration tail.length j))))‖ <
          η / (2 : ℝ) ^ (i + j + 3) := by
  obtain ⟨g, hg⟩ := hs.exists_tree
  let e := natTupleEnumeration tail.length
  let w (i j : ℕ) := ‖iteratedBasisCoordinate first tail (e i)
    (T (iteratedBasisVector first tail (e j)))‖
  have hrow (i : ℕ) : Tendsto (w i) atTop (𝓝 0) := by
    simpa only [norm_zero] using (iterated_matrix_row_tendsto_zero first tail h T (e i)).norm
  have hcol (j : ℕ) : Tendsto (fun i => w i j) atTop (𝓝 0) := by
    simpa only [norm_zero] using (iterated_matrix_column_tendsto_zero first tail T (e j)).norm
  obtain ⟨f, hfg, hf⟩ := tree_matrix_selection e g w hrow hcol hη
  refine ⟨f, ?_, ?_⟩
  · intro t
    obtain ⟨s, hs⟩ := hfg t
    rw [hs]
    exact hg s
  · intro i j hij
    have hh := hf i j hij
    simpa only [w, e.apply_symm_apply] using hh

end ThesisCommon

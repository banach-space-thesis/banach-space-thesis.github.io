import ThesisCommon.Analysis.SchauderBasis
import Mathlib.Analysis.InnerProductSpace.l2Space

/-! A normalized Schauder basis whose coordinates are inner products gives
an actual countable Hilbert representation. Density follows from its checked
partial-sum expansion, rather than an additional completeness premise. -/
noncomputable section
open Filter Topology
namespace ThesisCommon
namespace NormalizedSchauderBasis
variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X]
  [InnerProductSpace 𝕜 X] [CompleteSpace X]

theorem dense_topologicalClosure (b : NormalizedSchauderBasis 𝕜 X) :
    ⊤ ≤ (Submodule.span 𝕜 (Set.range b.vector)).topologicalClosure := by
  intro x _
  apply (Submodule.span 𝕜 (Set.range b.vector)).isClosed_topologicalClosure.mem_of_tendsto
    (b.expansion x)
  apply Filter.Eventually.of_forall
  intro N
  apply Submodule.sum_mem
  intro n _
  exact Submodule.smul_mem _ _
    (Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨n, rfl⟩))

def toHilbertBasis (b : NormalizedSchauderBasis 𝕜 X)
    (hc : ∀ n x, b.coord n x = inner 𝕜 (b.vector n) x) : HilbertBasis ℕ 𝕜 X :=
  HilbertBasis.mk (orthonormal_iff_ite.mpr (by
    intro i j
    rw [← hc, b.biorthogonal])) b.dense_topologicalClosure

end NormalizedSchauderBasis
end ThesisCommon

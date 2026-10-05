import ThesisCommon.Analysis.ALFragmentMetric
import ThesisCommon.Analysis.BooleanDensityHomogeneity

/-! Density-homogeneous decomposition of the genuine Boolean algebra of
positive fragments.  The density is computed in the ambient norm metric.
These results make no assertion that a homogeneous component has already
been classified as a product probability algebra. -/
noncomputable section
open Set
namespace ThesisCommon
variable {E : Type*} [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E]
  [HasSolidNorm E]

instance positiveFragmentTopologicalLattice (e : E) [Fact (0 ≤ e)] :
    TopologicalLattice (PositiveFragmentAlgebra e) where
  continuous_inf := by
    apply (isometry_positiveFragmentValue e).isEmbedding.continuous_iff.mpr
    exact ((isometry_positiveFragmentValue e).continuous.comp continuous_fst).inf
      ((isometry_positiveFragmentValue e).continuous.comp continuous_snd)
  continuous_sup := by
    apply (isometry_positiveFragmentValue e).isEmbedding.continuous_iff.mpr
    exact ((isometry_positiveFragmentValue e).continuous.comp continuous_fst).sup
      ((isometry_positiveFragmentValue e).continuous.comp continuous_snd)

theorem exists_homogeneous_positiveFragment_le {e : E} [Fact (0 ≤ e)]
    {a : PositiveFragmentAlgebra e} (ha : a ≠ ⊥) :
    ∃ b : PositiveFragmentAlgebra e, b ≤ a ∧ IsDensityHomogeneous b :=
  exists_densityHomogeneous_le ha

theorem exists_homogeneous_positiveFragment_decomposition (e : E) [Fact (0 ≤ e)] :
    ∃ s : Set (PositiveFragmentAlgebra e),
      (∀ a ∈ s, IsDensityHomogeneous a) ∧ s.Pairwise Disjoint ∧ IsLUB s ⊤ :=
  exists_disjoint_densityHomogeneous_isLUB_top

end ThesisCommon

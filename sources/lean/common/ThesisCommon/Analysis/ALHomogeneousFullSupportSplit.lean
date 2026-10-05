import ThesisCommon.Analysis.ALFragmentRelativeSplitting
import ThesisCommon.Analysis.BooleanRelativeFullSupportSplit

/-! Every fragment of a homogeneous component can actually be partitioned
into two disjoint fragments with the same full support relative to any
closed Boolean subalgebra of strictly smaller density.  The partition is
constructed; no relative nonatomicity assumption is added. -/
noncomputable section
open Set
namespace ThesisCommon
universe u
variable {E : Type u} [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E]
  [HasSolidNorm E] [CompleteSpace E] [OrderClosedTopology E]

theorem homogeneous_exists_partition_same_relativeHull
    (hAL : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x+y‖ = ‖x‖+‖y‖)
    {e : E} [Fact (0 ≤ e)] {a : PositiveFragmentAlgebra e}
    (ha : IsDensityHomogeneous a)
    (S : BooleanSubalgebra (PositiveFragmentAlgebra e))
    (hS : IsClosed (S : Set (PositiveFragmentAlgebra e)))
    (hden : topologicalDensity S < principalDensity a)
    (b : PositiveFragmentAlgebra e) (hba : b ≤ a) :
    ∃ u v : PositiveFragmentAlgebra e, u ⊔ v = b ∧ Disjoint u v ∧
      alFragmentRelativeHull hAL S hS u = alFragmentRelativeHull hAL S hS b ∧
      alFragmentRelativeHull hAL S hS v = alFragmentRelativeHull hAL S hS b := by
  apply exists_boolean_partition_same_relativeHull
    (positiveFragment_exists_isLUB_of_normCompletion hAL) S (alFragmentRelativeHull hAL S hS)
    (alFragmentRelativeHull_spec hAL S hS) b
  intro r hr hrb
  exact homogeneous_exists_disjoint_same_relativeHull hAL ha S hS hden hr (hrb.trans hba)

end ThesisCommon


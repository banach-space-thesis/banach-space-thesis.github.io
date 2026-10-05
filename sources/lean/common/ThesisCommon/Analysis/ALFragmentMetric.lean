import ThesisCommon.Analysis.ALFragmentBoolean
import ThesisCommon.Analysis.LatticeDisjointness
import Mathlib.Order.SymmDiff
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.UniformSpace.UniformEmbedding

/-! The fragment Boolean algebra carries the actual ambient metric and is
complete. Boolean symmetric difference corresponds to lattice modulus of
the ambient difference. -/
noncomputable section
open Set
open scoped symmDiff
namespace ThesisCommon
variable {E : Type*} [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E]

theorem positiveFragmentValue_disjoint {e : E} [Fact (0 ≤ e)]
    (a b : PositiveFragmentAlgebra e) (h : Disjoint a b) :
    positiveFragmentValue a ⊓ positiveFragmentValue b = 0 := by
  have h' := congrArg positiveFragmentValue h.eq_bot
  simpa only [positiveFragmentValue_inf, positiveFragmentValue_bot] using h'

theorem positiveFragmentValue_sup_of_disjoint {e : E} [Fact (0 ≤ e)]
    (a b : PositiveFragmentAlgebra e) (h : Disjoint a b) :
    positiveFragmentValue (a ⊔ b) = positiveFragmentValue a + positiveFragmentValue b := by
  rw [positiveFragmentValue_sup]
  have h' := inf_add_sup (positiveFragmentValue a) (positiveFragmentValue b)
  rwa [positiveFragmentValue_disjoint a b h, zero_add] at h'

theorem positiveFragmentValue_sdiff {e : E} [Fact (0 ≤ e)]
    (a b : PositiveFragmentAlgebra e) :
    positiveFragmentValue (a \ b) = positiveFragmentValue a - positiveFragmentValue (a ⊓ b) := by
  have h := positiveFragmentValue_sup_of_disjoint (a ⊓ b) (a \ b) disjoint_inf_sdiff
  rw [sup_inf_sdiff] at h
  apply eq_sub_iff_add_eq.mpr
  simpa only [add_comm] using h.symm

theorem positiveFragmentValue_symmDiff {e : E} [Fact (0 ≤ e)]
    (a b : PositiveFragmentAlgebra e) :
    positiveFragmentValue (a ∆ b) = |positiveFragmentValue a - positiveFragmentValue b| := by
  have heq : positiveFragmentValue a - positiveFragmentValue b =
      positiveFragmentValue (a \ b) - positiveFragmentValue (b \ a) := by
    rw [positiveFragmentValue_sdiff, positiveFragmentValue_sdiff, inf_comm b a]
    abel
  rw [symmDiff_def, positiveFragmentValue_sup_of_disjoint _ _ disjoint_sdiff_sdiff, heq,
    lattice_abs_sub_of_disjoint (by
      rw [abs_of_nonneg (positiveFragmentValue_nonneg _),
        abs_of_nonneg (positiveFragmentValue_nonneg _)]
      exact positiveFragmentValue_disjoint _ _ disjoint_sdiff_sdiff),
    abs_of_nonneg (positiveFragmentValue_nonneg _), abs_of_nonneg (positiveFragmentValue_nonneg _)]

instance positiveFragmentMetric (e : E) [Fact (0 ≤ e)] : MetricSpace (PositiveFragmentAlgebra e) :=
  MetricSpace.induced positiveFragmentValue (positiveFragmentValue_injective e) inferInstance

omit [IsOrderedAddMonoid E] in
theorem isometry_positiveFragmentValue (e : E) [Fact (0 ≤ e)] :
    Isometry (positiveFragmentValue (e := e)) :=
  MetricSpace.isometry_induced positiveFragmentValue (positiveFragmentValue_injective e)

variable [HasSolidNorm E]

theorem isClosed_positiveFragments (e : E) : IsClosed {a : E | IsPositiveFragment a e} :=
  isClosed_Ici.inter (isClosed_Iic.inter
    (isClosed_eq (continuous_id.inf (continuous_const.sub continuous_id)) continuous_const))

omit [HasSolidNorm E] in
theorem range_positiveFragmentValue (e : E) [Fact (0 ≤ e)] :
    range (positiveFragmentValue (e := e)) = {a : E | IsPositiveFragment a e} := by
  ext a
  constructor
  · rintro ⟨b, rfl⟩
    exact positiveFragmentValue_isFragment b
  · intro ha
    exact ⟨positiveFragmentOf ha, rfl⟩

instance positiveFragmentComplete [CompleteSpace E] (e : E) [Fact (0 ≤ e)] :
    CompleteSpace (PositiveFragmentAlgebra e) := by
  apply (isometry_positiveFragmentValue e).isUniformInducing.completeSpace
  rw [range_positiveFragmentValue]
  exact (isClosed_positiveFragments e).isComplete

end ThesisCommon

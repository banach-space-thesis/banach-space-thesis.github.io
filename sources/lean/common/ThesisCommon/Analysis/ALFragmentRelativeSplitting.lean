import ThesisCommon.Analysis.ALFragmentOrderCompleteness
import ThesisCommon.Analysis.BooleanRelativeDensity
import ThesisCommon.Analysis.BooleanRelativeHull

/-! Actual relative support and relative nonatomic splitting in homogeneous
AL fragment algebras.  For a closed subalgebra of smaller density, every
nonzero subfragment has disjoint nonzero pieces with the same relative
support.  This is qualitative splitting; exact prescribed conditional mass
division is a further step. -/
noncomputable section
open Set
namespace ThesisCommon
universe u
variable {E : Type u} [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E]
  [HasSolidNorm E] [CompleteSpace E] [OrderClosedTopology E]
variable (hAL : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x+y‖ = ‖x‖+‖y‖)
variable {e : E} [Fact (0 ≤ e)]

/-- The actual least cover in a metric-closed Boolean subalgebra. -/
def alFragmentRelativeHull (S : BooleanSubalgebra (PositiveFragmentAlgebra e))
    (hS : IsClosed (S : Set (PositiveFragmentAlgebra e)))
    (a : PositiveFragmentAlgebra e) : PositiveFragmentAlgebra e :=
  (positiveFragment_exists_relativeHull hAL S hS a).choose

theorem alFragmentRelativeHull_spec (S : BooleanSubalgebra (PositiveFragmentAlgebra e))
    (hS : IsClosed (S : Set (PositiveFragmentAlgebra e)))
    (a : PositiveFragmentAlgebra e) :
    alFragmentRelativeHull hAL S hS a ∈ S ∧ a ≤ alFragmentRelativeHull hAL S hS a ∧
      ∀ b ∈ S, a ≤ b → alFragmentRelativeHull hAL S hS a ≤ b :=
  (positiveFragment_exists_relativeHull hAL S hS a).choose_spec

theorem homogeneous_exists_disjoint_same_relativeHull
    {a : PositiveFragmentAlgebra e} (ha : IsDensityHomogeneous a)
    (S : BooleanSubalgebra (PositiveFragmentAlgebra e))
    (hS : IsClosed (S : Set (PositiveFragmentAlgebra e)))
    (hden : topologicalDensity S < principalDensity a)
    {b : PositiveFragmentAlgebra e} (hb : b ≠ ⊥) (hba : b ≤ a) :
    ∃ u v : PositiveFragmentAlgebra e, u ≤ b ∧ v ≤ b ∧ Disjoint u v ∧
      u ≠ ⊥ ∧ v ≠ ⊥ ∧
      alFragmentRelativeHull hAL S hS u = alFragmentRelativeHull hAL S hS v := by
  obtain ⟨c, hcb, ε, hε, hsep⟩ :=
    homogeneous_exists_positive_distance_from_subalgebra ha S hden hb hba
  have hc : ∀ s ∈ S, c ≠ b ⊓ s := by
    intro s hs heq
    have h := hsep ⟨s, hs⟩
    rw [inf_comm s b, ← heq, dist_self] at h
    exact hε.not_ge h
  let H := alFragmentRelativeHull hAL S hS
  have hH := alFragmentRelativeHull_spec hAL S hS
  obtain ⟨u, v, hub, hvb, huv, heq, hne⟩ :=
    exists_disjoint_same_booleanRelativeHull S H hH hcb hc
  have hu : u ≠ ⊥ := by
    intro h
    exact hne ((booleanRelativeHull_eq_bot_iff S H hH u).mpr h)
  have hv : v ≠ ⊥ := by
    intro h
    exact hne (heq.trans ((booleanRelativeHull_eq_bot_iff S H hH v).mpr h))
  exact ⟨u, v, hub, hvb, huv, hu, hv, heq⟩

end ThesisCommon

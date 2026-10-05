import ThesisCommon.Analysis.ALFragmentSubalgebraIndicators
import ThesisCommon.Analysis.ALFragmentIndicatorLattice
import ThesisCommon.Analysis.L1SubsigmaConditionalMass
import ThesisCommon.Analysis.ALFragmentRelativeSplitting

/-! Actual conditional masses of fragments and their relative support tests.
Conditional mass is obtained by applying the genuine L1 conditional
expectation to the Stone indicator, not by positing a vector measure. -/
noncomputable section
open MeasureTheory Set Filter
namespace ThesisCommon
variable {E : Type*} [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E]
  [HasSolidNorm E]
variable (hAL : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x+y‖ = ‖x‖+‖y‖)
variable (e : E) [Fact (0 ≤ e)]

def alFragmentConditionalMass (S : BooleanSubalgebra (PositiveFragmentAlgebra e))
    (a : PositiveFragmentAlgebra e) : Lp ℝ 1 (alFragmentMeasure hAL e) :=
  lOneSubsigmaProjection (alFragmentMeasure hAL e) (booleanSubalgebraStoneMeasurableSpace_le S)
    (alFragmentIndicator hAL e a)

theorem alFragmentConditionalMass_nonneg (S : BooleanSubalgebra (PositiveFragmentAlgebra e))
    (a : PositiveFragmentAlgebra e) : 0 ≤ alFragmentConditionalMass hAL e S a :=
  lOneSubsigmaProjection_nonneg _ _ (alFragmentIndicator_nonneg hAL e a)

theorem alFragmentConditionalMass_eq_zero_iff (S : BooleanSubalgebra (PositiveFragmentAlgebra e))
    (a : PositiveFragmentAlgebra e) : alFragmentConditionalMass hAL e S a = 0 ↔ a = ⊥ := by
  rw [alFragmentConditionalMass,
    lOneSubsigmaProjection_eq_zero_iff_of_nonneg _ _ (alFragmentIndicator_nonneg hAL e a),
    ← alFragmentIndicator_bot hAL e, (isometry_alFragmentIndicator hAL e).injective.eq_iff]

theorem alFragmentConditionalMass_sup_of_disjoint
    (S : BooleanSubalgebra (PositiveFragmentAlgebra e)) (a b : PositiveFragmentAlgebra e)
    (hab : Disjoint a b) :
    alFragmentConditionalMass hAL e S (a ⊔ b) =
      alFragmentConditionalMass hAL e S a + alFragmentConditionalMass hAL e S b := by
  simp only [alFragmentConditionalMass, alFragmentIndicator_sup_of_disjoint hAL e a b hab, map_add]

theorem alFragmentConditionalMass_inf_of_mem
    (S : BooleanSubalgebra (PositiveFragmentAlgebra e)) (a b : PositiveFragmentAlgebra e)
    (hb : b ∈ S) :
    alFragmentConditionalMass hAL e S (a ⊓ b) =
      lpCut (booleanStoneSet b) (measurableSet_booleanStoneSet b)
        (alFragmentConditionalMass hAL e S a) := by
  unfold alFragmentConditionalMass
  rw [← alFragmentIndicator_stoneCut]
  exact lOneSubsigmaProjection_cut _ _ _ (measurableSet_booleanStoneSet_of_mem_subalgebra S hb) _

omit [HasSolidNorm E] in
theorem alFragmentConditionalMass_aestronglyMeasurable
    (S : BooleanSubalgebra (PositiveFragmentAlgebra e)) (a : PositiveFragmentAlgebra e) :
    AEStronglyMeasurable[booleanSubalgebraStoneMeasurableSpace S]
      (alFragmentConditionalMass hAL e S a) (alFragmentMeasure hAL e) :=
  lOneSubsigmaProjection_mem _ _ _

theorem alFragmentConditionalMass_cut_eq_zero_iff_relativeHull
    [CompleteSpace E] [OrderClosedTopology E]
    (S : BooleanSubalgebra (PositiveFragmentAlgebra e))
    (hS : IsClosed (S : Set (PositiveFragmentAlgebra e)))
    (a b : PositiveFragmentAlgebra e) (hb : b ∈ S) :
    lpCut (booleanStoneSet b) (measurableSet_booleanStoneSet b)
        (alFragmentConditionalMass hAL e S a) = 0 ↔
      alFragmentRelativeHull hAL S hS a ⊓ b = ⊥ := by
  rw [← alFragmentConditionalMass_inf_of_mem hAL e S a b hb,
    alFragmentConditionalMass_eq_zero_iff,
    ← booleanRelativeHull_inf_of_mem S (alFragmentRelativeHull hAL S hS)
      (alFragmentRelativeHull_spec hAL S hS) a hb,
    booleanRelativeHull_eq_bot_iff S (alFragmentRelativeHull hAL S hS)
      (alFragmentRelativeHull_spec hAL S hS)]

end ThesisCommon

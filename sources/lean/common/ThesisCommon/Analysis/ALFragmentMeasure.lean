import ThesisCommon.Analysis.ALFragmentMetric
import ThesisCommon.Analysis.BooleanStoneMeasure
import ThesisCommon.Analysis.MeasureAlgebraIndicators
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-! The actual finite measure representing the fragment Boolean algebra.
The fragment-to-indicator map is isometric. Completeness of fragments and
density of the generating algebra give a fragment for every measurable set. -/
noncomputable section
open MeasureTheory Set
open scoped symmDiff
namespace ThesisCommon

theorem booleanStoneSet_symmDiff {B : Type*} [BooleanAlgebra B] (a b : B) :
    booleanStoneSet (a ∆ b) = booleanStoneSet a ∆ booleanStoneSet b := by
  simp only [symmDiff_def, sdiff_eq, booleanStoneSet_sup, booleanStoneSet_inf, booleanStoneSet_compl]
  rfl

variable {E : Type*} [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E]
variable (hAL : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x+y‖ = ‖x‖+‖y‖)

def alFragmentMeasure (e : E) [Fact (0 ≤ e)] : Measure (BooleanStonePoint (PositiveFragmentAlgebra e)) :=
  booleanStoneMeasure positiveFragmentMass (positiveFragmentMass_bot e)
    (positiveFragmentMass_sup_of_disjoint hAL)

instance alFragmentMeasureFinite (e : E) [Fact (0 ≤ e)] : IsFiniteMeasure (alFragmentMeasure hAL e) :=
  isFiniteMeasure_booleanStoneMeasure positiveFragmentMass (positiveFragmentMass_bot e)
    (positiveFragmentMass_sup_of_disjoint hAL) (positiveFragmentMass_ne_top _)

theorem alFragmentMeasure_apply (e : E) [Fact (0 ≤ e)] (a : PositiveFragmentAlgebra e) :
    alFragmentMeasure hAL e (booleanStoneSet a) = ENNReal.ofReal ‖positiveFragmentValue a‖ :=
  booleanStoneMeasure_apply _ _ _ a

def alFragmentIndicator (e : E) [Fact (0 ≤ e)] (a : PositiveFragmentAlgebra e) :
    Lp ℝ 1 (alFragmentMeasure hAL e) :=
  indicatorConstLp 1 (measurableSet_booleanStoneSet a) (measure_ne_top _ _) (1 : ℝ)

theorem alFragmentIndicator_eq_lOneIndicator (e : E) [Fact (0 ≤ e)] (a : PositiveFragmentAlgebra e) :
    alFragmentIndicator hAL e a =
      lOneIndicator (alFragmentMeasure hAL e) (booleanStoneSet a) (measurableSet_booleanStoneSet a) := by
  rw [alFragmentIndicator, indicatorConstLp_eq_smul_lOneIndicator, one_smul]

variable [HasSolidNorm E]

theorem isometry_alFragmentIndicator (e : E) [Fact (0 ≤ e)] : Isometry (alFragmentIndicator hAL e) := by
  apply Isometry.of_dist_eq
  intro a b
  rw [alFragmentIndicator, alFragmentIndicator, dist_indicatorConstLp_eq_norm,
    norm_indicatorConstLp (by norm_num : (1 : ENNReal) ≠ 0) (by norm_num : (1 : ENNReal) ≠ ⊤)]
  simp only [norm_one, ENNReal.toReal_one, div_one, Real.rpow_one, one_mul]
  change (alFragmentMeasure hAL e (booleanStoneSet a ∆ booleanStoneSet b)).toReal = dist a b
  rw [← booleanStoneSet_symmDiff, alFragmentMeasure_apply, ENNReal.toReal_ofReal (norm_nonneg _),
    positiveFragmentValue_symmDiff, norm_abs_eq_norm]
  exact (dist_eq_norm (positiveFragmentValue a) (positiveFragmentValue b)).symm

theorem exists_fragment_of_measurableSet [CompleteSpace E] (e : E) [Fact (0 ≤ e)]
    (s : Set (BooleanStonePoint (PositiveFragmentAlgebra e))) (hs : MeasurableSet s) :
    ∃ a : PositiveFragmentAlgebra e, alFragmentIndicator hAL e a =
      lOneIndicator (alFragmentMeasure hAL e) s hs := by
  let μ := alFragmentMeasure hAL e
  have hd : μ.MeasureDense (booleanStoneAlgebra (PositiveFragmentAlgebra e)) :=
    Measure.MeasureDense.of_generateFrom_isSetAlgebra_finite μ booleanStoneAlgebra_isSetAlgebra rfl
  letI : Fact ((1 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  have hc := hd.indicatorConstLp_subset_closure 1 (1 : ℝ)
    ⟨s, hs, measure_ne_top μ s, rfl⟩
  have hclosed : IsClosed (range (alFragmentIndicator hAL e)) :=
    (isometry_alFragmentIndicator hAL e).isClosedEmbedding.isClosed_range
  have hmem : indicatorConstLp 1 hs (measure_ne_top μ s) (1 : ℝ) ∈
      range (alFragmentIndicator hAL e) := by
    apply closure_minimal ?_ hclosed hc
    rintro f ⟨t, ht, hμt, rfl⟩
    obtain ⟨a, rfl⟩ := ht
    exact ⟨a, rfl⟩
  rw [indicatorConstLp_eq_smul_lOneIndicator, one_smul] at hmem
  exact hmem

end ThesisCommon

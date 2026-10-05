import ThesisCommon.Analysis.ALMeasurableFragments
import Mathlib.Order.BooleanSubalgebra
import Mathlib.MeasureTheory.Measure.Trim

/-! A closed Boolean subalgebra of AL fragments is exactly the family of
fragments represented by sets in its generated Stone sigma algebra. The
representative statement is modulo null sets; no completion of the generated
sigma algebra is silently assumed. -/
noncomputable section
open MeasureTheory Set Filter
open scoped symmDiff
namespace ThesisCommon

variable {B : Type*} [BooleanAlgebra B]

def booleanSubalgebraStoneSets (S : BooleanSubalgebra B) :
    Set (Set (BooleanStonePoint B)) := booleanStoneSet '' (S : Set B)

theorem booleanSubalgebraStoneSets_isSetAlgebra (S : BooleanSubalgebra B) :
    IsSetAlgebra (booleanSubalgebraStoneSets S) where
  empty_mem := ⟨⊥, S.bot_mem, booleanStoneSet_bot⟩
  compl_mem := by
    rintro s ⟨a, ha, rfl⟩
    exact ⟨aᶜ, S.compl_mem ha, booleanStoneSet_compl a⟩
  union_mem := by
    rintro s t ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a ⊔ b, S.sup_mem ha hb, booleanStoneSet_sup a b⟩

def booleanSubalgebraStoneMeasurableSpace (S : BooleanSubalgebra B) :
    MeasurableSpace (BooleanStonePoint B) :=
  MeasurableSpace.generateFrom (booleanSubalgebraStoneSets S)

theorem booleanSubalgebraStoneMeasurableSpace_le (S : BooleanSubalgebra B) :
    booleanSubalgebraStoneMeasurableSpace S ≤ booleanStoneMeasurableSpace := by
  apply MeasurableSpace.generateFrom_le
  rintro s ⟨a, _, rfl⟩
  exact measurableSet_booleanStoneSet a

theorem measurableSet_booleanStoneSet_of_mem_subalgebra
    (S : BooleanSubalgebra B) {a : B} (ha : a ∈ S) :
    MeasurableSet[booleanSubalgebraStoneMeasurableSpace S] (booleanStoneSet a) :=
  MeasurableSpace.measurableSet_generateFrom ⟨a, ha, rfl⟩

variable {E : Type*} [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E]
  [HasSolidNorm E]
variable (hAL : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x+y‖ = ‖x‖+‖y‖)
variable (e : E) [Fact (0 ≤ e)]

theorem dist_positiveFragment_eq_measure_symmDiff (a b : PositiveFragmentAlgebra e) :
    dist a b = (alFragmentMeasure hAL e).real (booleanStoneSet a ∆ booleanStoneSet b) := by
  rw [Measure.real, ← booleanStoneSet_symmDiff, alFragmentMeasure_apply,
    ENNReal.toReal_ofReal (norm_nonneg _), positiveFragmentValue_symmDiff,
    norm_abs_eq_norm]
  exact dist_eq_norm (positiveFragmentValue a) (positiveFragmentValue b)

variable [CompleteSpace E]

theorem alMeasurableFragment_mem_closed_subalgebra
    (S : BooleanSubalgebra (PositiveFragmentAlgebra e))
    (hS : IsClosed (S : Set (PositiveFragmentAlgebra e)))
    (s : Set (BooleanStonePoint (PositiveFragmentAlgebra e)))
    (hs : MeasurableSet[booleanSubalgebraStoneMeasurableSpace S] s) :
    alMeasurableFragment hAL e s (booleanSubalgebraStoneMeasurableSpace_le S s hs) ∈ S := by
  let μ := alFragmentMeasure hAL e
  let hm := booleanSubalgebraStoneMeasurableSpace_le S
  have hd := @Measure.MeasureDense.of_generateFrom_isSetAlgebra_finite _
    (booleanSubalgebraStoneMeasurableSpace S) (μ.trim hm) _
    (isFiniteMeasure_trim hm) (booleanSubalgebraStoneSets_isSetAlgebra S) rfl
  change alMeasurableFragment hAL e s (hm s hs) ∈ (S : Set (PositiveFragmentAlgebra e))
  rw [← hS.closure_eq]
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨t, ⟨a, ha, hat⟩, ht⟩ := @Measure.MeasureDense.approx _
    (booleanSubalgebraStoneMeasurableSpace S) (μ.trim hm) _ hd s hs
    (@measure_ne_top _ (booleanSubalgebraStoneMeasurableSpace S) (μ.trim hm)
      (isFiniteMeasure_trim hm) s) ε hε
  subst t
  refine ⟨a, ha, ?_⟩
  rw [dist_positiveFragment_eq_measure_symmDiff hAL e]
  have heq : booleanStoneSet (alMeasurableFragment hAL e s (hm s hs)) ∆
      booleanStoneSet a =ᵐ[μ] s ∆ booleanStoneSet a := by
    filter_upwards [alMeasurableFragment_stoneSet_ae hAL e s (hm s hs)] with x hx
    change (x ∈ booleanStoneSet (alMeasurableFragment hAL e s (hm s hs)) ∆
      booleanStoneSet a) = (x ∈ s ∆ booleanStoneSet a)
    change (x ∈ booleanStoneSet (alMeasurableFragment hAL e s (hm s hs))) = (x ∈ s) at hx
    simp only [Set.mem_symmDiff, hx]
  rw [Measure.real, measure_congr heq]
  have ht' : μ (s ∆ booleanStoneSet a) < ENNReal.ofReal ε := by
    rwa [trim_measurableSet_eq hm
      (hs.symmDiff (measurableSet_booleanStoneSet_of_mem_subalgebra S ha))] at ht
  exact (ENNReal.toReal_lt_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mpr ht' |>.trans_eq
    (ENNReal.toReal_ofReal hε.le)

theorem mem_closed_subalgebra_iff_measurable_representative
    (S : BooleanSubalgebra (PositiveFragmentAlgebra e))
    (hS : IsClosed (S : Set (PositiveFragmentAlgebra e)))
    (a : PositiveFragmentAlgebra e) :
    a ∈ S ↔ ∃ s : Set (BooleanStonePoint (PositiveFragmentAlgebra e)),
      MeasurableSet[booleanSubalgebraStoneMeasurableSpace S] s ∧
      booleanStoneSet a =ᵐ[alFragmentMeasure hAL e] s := by
  constructor
  · intro ha
    exact ⟨booleanStoneSet a, measurableSet_booleanStoneSet_of_mem_subalgebra S ha,
      Filter.EventuallyEq.rfl⟩
  · rintro ⟨s, hs, ha⟩
    have heq : a = alMeasurableFragment hAL e s
        (booleanSubalgebraStoneMeasurableSpace_le S s hs) := by
      apply alFragment_eq_of_stoneSet_ae hAL e
      exact ha.trans (alMeasurableFragment_stoneSet_ae hAL e s _).symm
    rw [heq]
    exact alMeasurableFragment_mem_closed_subalgebra hAL e S hS s hs

end ThesisCommon

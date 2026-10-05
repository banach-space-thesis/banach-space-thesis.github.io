import ThesisCommon.Analysis.ALFragmentMeasure

/-! Measurable sets in the finite Stone measure have unique lattice fragments,
up to null sets. Their values form the vector content used to construct the
principal-band L1 representation. -/
noncomputable section
open MeasureTheory Set Filter
namespace ThesisCommon
variable {E : Type*} [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E]
  [HasSolidNorm E] [CompleteSpace E]
variable (hAL : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x+y‖ = ‖x‖+‖y‖)
variable (e : E) [Fact (0 ≤ e)]

def alMeasurableFragment (s : Set (BooleanStonePoint (PositiveFragmentAlgebra e)))
    (hs : MeasurableSet s) : PositiveFragmentAlgebra e :=
  (exists_fragment_of_measurableSet hAL e s hs).choose

theorem alMeasurableFragment_indicator (s : Set (BooleanStonePoint (PositiveFragmentAlgebra e)))
    (hs : MeasurableSet s) :
    alFragmentIndicator hAL e (alMeasurableFragment hAL e s hs) =
      lOneIndicator (alFragmentMeasure hAL e) s hs :=
  (exists_fragment_of_measurableSet hAL e s hs).choose_spec

theorem alMeasurableFragment_stoneSet_ae (s : Set (BooleanStonePoint (PositiveFragmentAlgebra e)))
    (hs : MeasurableSet s) :
    booleanStoneSet (alMeasurableFragment hAL e s hs) =ᵐ[alFragmentMeasure hAL e] s := by
  have heq := alMeasurableFragment_indicator hAL e s hs
  rw [alFragmentIndicator_eq_lOneIndicator] at heq
  have h := Lp.ext_iff.mp heq
  filter_upwards [h, lOneIndicator_coe (μ := alFragmentMeasure hAL e)
    (booleanStoneSet (alMeasurableFragment hAL e s hs)) (measurableSet_booleanStoneSet _),
    lOneIndicator_coe (μ := alFragmentMeasure hAL e) s hs] with x hx ha hb
  rw [ha, hb] at hx
  change (x ∈ booleanStoneSet (alMeasurableFragment hAL e s hs)) = (x ∈ s)
  by_cases hxa : x ∈ booleanStoneSet (alMeasurableFragment hAL e s hs) <;>
    by_cases hxs : x ∈ s <;> simp_all

omit [CompleteSpace E] in
theorem alFragment_eq_of_stoneSet_ae (a b : PositiveFragmentAlgebra e)
    (h : booleanStoneSet a =ᵐ[alFragmentMeasure hAL e] booleanStoneSet b) : a = b := by
  apply (isometry_alFragmentIndicator hAL e).injective
  simp only [alFragmentIndicator_eq_lOneIndicator]
  exact lOneIndicator_eq_of_ae _ _ h

theorem alMeasurableFragment_stoneSet (a : PositiveFragmentAlgebra e) :
    alMeasurableFragment hAL e (booleanStoneSet a) (measurableSet_booleanStoneSet a) = a := by
  apply alFragment_eq_of_stoneSet_ae hAL e
  exact alMeasurableFragment_stoneSet_ae hAL e _ _

theorem alMeasurableFragment_empty :
    alMeasurableFragment hAL e ∅ MeasurableSet.empty = ⊥ := by
  simpa only [booleanStoneSet_bot] using alMeasurableFragment_stoneSet hAL e ⊥

theorem alMeasurableFragment_union
    (s t : Set (BooleanStonePoint (PositiveFragmentAlgebra e)))
    (hs : MeasurableSet s) (ht : MeasurableSet t) :
    alMeasurableFragment hAL e (s ∪ t) (hs.union ht) =
      alMeasurableFragment hAL e s hs ⊔ alMeasurableFragment hAL e t ht := by
  apply alFragment_eq_of_stoneSet_ae hAL e
  rw [booleanStoneSet_sup]
  filter_upwards [alMeasurableFragment_stoneSet_ae hAL e (s ∪ t) (hs.union ht),
    alMeasurableFragment_stoneSet_ae hAL e s hs,
    alMeasurableFragment_stoneSet_ae hAL e t ht] with x hu hsx htx
  exact hu.trans (congrArg₂ Or hsx htx).symm

theorem alMeasurableFragment_disjoint
    (s t : Set (BooleanStonePoint (PositiveFragmentAlgebra e)))
    (hs : MeasurableSet s) (ht : MeasurableSet t) (hst : Disjoint s t) :
    Disjoint (alMeasurableFragment hAL e s hs) (alMeasurableFragment hAL e t ht) := by
  apply disjoint_iff.mpr
  apply alFragment_eq_of_stoneSet_ae hAL e
  rw [booleanStoneSet_inf, booleanStoneSet_bot]
  filter_upwards [alMeasurableFragment_stoneSet_ae hAL e s hs,
    alMeasurableFragment_stoneSet_ae hAL e t ht] with x hsx htx
  change (booleanStoneSet (alMeasurableFragment hAL e s hs) x ∧
    booleanStoneSet (alMeasurableFragment hAL e t ht) x) = False
  rw [hsx, htx]
  apply propext
  exact ⟨fun h => Set.disjoint_left.mp hst h.1 h.2, False.elim⟩

theorem norm_alMeasurableFragment
    (s : Set (BooleanStonePoint (PositiveFragmentAlgebra e))) (hs : MeasurableSet s) :
    ‖positiveFragmentValue (alMeasurableFragment hAL e s hs)‖ =
      (alFragmentMeasure hAL e).real s := by
  have h := measure_congr (alMeasurableFragment_stoneSet_ae hAL e s hs)
  rw [alFragmentMeasure_apply] at h
  simpa only [Measure.real, ENNReal.toReal_ofReal (norm_nonneg _)] using
    congrArg ENNReal.toReal h

end ThesisCommon

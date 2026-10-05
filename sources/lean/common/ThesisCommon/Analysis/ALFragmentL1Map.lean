import ThesisCommon.Analysis.ALMeasurableFragments
import Mathlib.MeasureTheory.Integral.SetToL1
import Mathlib.Analysis.Normed.Operator.Mul

/-! The actual bounded positive map from the finite Stone L1 space into the
original complete real lattice, obtained from its measurable fragments. -/
noncomputable section
open Set MeasureTheory
open scoped Classical
namespace ThesisCommon
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Lattice E] [IsOrderedAddMonoid E] [HasSolidNorm E] [CompleteSpace E]
variable (hAL : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x+y‖ = ‖x‖+‖y‖)
variable (e : E) [Fact (0 ≤ e)]

def alFragmentVectorContent (s : Set (BooleanStonePoint (PositiveFragmentAlgebra e))) :
    ℝ →L[ℝ] E :=
  if hs : MeasurableSet s then
    ContinuousLinearMap.toSpanSingleton ℝ (positiveFragmentValue (alMeasurableFragment hAL e s hs))
  else 0

theorem alFragmentVectorContent_apply
    (s : Set (BooleanStonePoint (PositiveFragmentAlgebra e))) (hs : MeasurableSet s) (c : ℝ) :
    alFragmentVectorContent hAL e s c =
      c • positiveFragmentValue (alMeasurableFragment hAL e s hs) := by
  simp only [alFragmentVectorContent, dif_pos hs, ContinuousLinearMap.toSpanSingleton_apply]

theorem alFragmentVectorContent_finMeasAdditive :
    FinMeasAdditive (alFragmentMeasure hAL e) (alFragmentVectorContent hAL e) := by
  intro s t hs ht _ _ hst
  apply ContinuousLinearMap.ext
  intro c
  rw [alFragmentVectorContent_apply _ _ _ (hs.union ht), ContinuousLinearMap.add_apply,
    alFragmentVectorContent_apply _ _ _ hs, alFragmentVectorContent_apply _ _ _ ht,
    alMeasurableFragment_union hAL e s t hs ht, positiveFragmentValue_sup_of_disjoint _ _
      (alMeasurableFragment_disjoint hAL e s t hs ht hst), smul_add]

theorem alFragmentVectorContent_dominated :
    DominatedFinMeasAdditive (alFragmentMeasure hAL e) (alFragmentVectorContent hAL e) 1 := by
  refine ⟨alFragmentVectorContent_finMeasAdditive hAL e, ?_⟩
  intro s hs _
  rw [alFragmentVectorContent, dif_pos hs, ContinuousLinearMap.norm_toSpanSingleton,
    norm_alMeasurableFragment, one_mul]

def alFragmentL1Map : Lp ℝ 1 (alFragmentMeasure hAL e) →L[ℝ] E :=
  L1.setToL1 (alFragmentVectorContent_dominated hAL e)

theorem alFragmentL1Map_indicator
    (s : Set (BooleanStonePoint (PositiveFragmentAlgebra e))) (hs : MeasurableSet s) :
    alFragmentL1Map hAL e (lOneIndicator (alFragmentMeasure hAL e) s hs) =
      positiveFragmentValue (alMeasurableFragment hAL e s hs) := by
  have h := L1.setToL1_indicatorConstLp (alFragmentVectorContent_dominated hAL e)
    hs (measure_ne_top _ _) (1 : ℝ)
  rw [indicatorConstLp_eq_smul_lOneIndicator, one_smul,
    alFragmentVectorContent_apply, one_smul] at h
  exact h

theorem alFragmentL1Map_fragment (a : PositiveFragmentAlgebra e) :
    alFragmentL1Map hAL e (alFragmentIndicator hAL e a) = positiveFragmentValue a := by
  rw [alFragmentIndicator_eq_lOneIndicator, alFragmentL1Map_indicator, alMeasurableFragment_stoneSet]

theorem alFragmentL1Map_norm_le (f : Lp ℝ 1 (alFragmentMeasure hAL e)) :
    ‖alFragmentL1Map hAL e f‖ ≤ ‖f‖ := by
  simpa only [one_mul] using
    L1.norm_setToL1_le_mul_norm (alFragmentVectorContent_dominated hAL e) zero_le_one f

variable [IsOrderedModule ℝ E]

theorem alFragmentL1Map_nonneg {f : Lp ℝ 1 (alFragmentMeasure hAL e)} (hf : 0 ≤ f) :
    0 ≤ alFragmentL1Map hAL e f := by
  apply L1.setToL1_nonneg (alFragmentVectorContent_dominated hAL e) _ hf
  intro s hs _ c hc
  rw [alFragmentVectorContent_apply _ _ _ hs]
  exact smul_nonneg hc (positiveFragmentValue_nonneg _)

end ThesisCommon

import ThesisCommon.Analysis.L1OrderUnitLInfinity
import ThesisCommon.Analysis.BooleanStoneContinuousLpOrder
import ThesisCommon.Analysis.ContinuousMapLpComplexification

/-! An actual compact extremally disconnected model for L-infinity of every
finite measure. Both scalar representations are onto linear isometries. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal
namespace ThesisCommon
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]

theorem lOneUnitStoneMeasure_positive (a : L1UnitFragments μ) (ha : a ≠ ⊥) :
    0 < lOneUnitStoneMeasure μ (booleanStoneSet a) := by
  rw [lOneUnitStoneMeasure, alFragmentMeasure_apply, ENNReal.ofReal_pos, norm_pos_iff]
  intro h
  apply ha
  apply positiveFragmentValue_injective (lOneUnit μ)
  simpa only [positiveFragmentValue_bot] using h

theorem lOneUnitStoneMeasure_represents_sets (A : Set (L1UnitStone μ)) (hA : MeasurableSet A) :
    ∃ a : L1UnitFragments μ, A =ᵐ[lOneUnitStoneMeasure μ] booleanStoneSet a :=
  ⟨alMeasurableFragment (lOne_norm_add_of_nonneg μ) (lOneUnit μ) A hA,
    (alMeasurableFragment_stoneSet_ae (lOne_norm_add_of_nonneg μ) (lOneUnit μ) A hA).symm⟩

def realStoneLInfinityEquiv : C(L1UnitStone μ, ℝ) ≃ₗᵢ[ℝ] Lp ℝ ∞ μ :=
  (booleanStoneContinuousLInfinityEquiv (𝕜 := ℝ) (lOneUnitStoneMeasure μ)
    (lOneUnitStoneMeasure_positive μ) (lOneUnitStoneMeasure_represents_sets μ)).trans
    (lOneOrderUnitLInfinityEquiv (lOneUnitStoneEquiv μ)
      (lOneUnitStoneEquiv_nonneg μ) (lOneUnitStoneEquiv_one μ))

theorem realStoneLInfinityEquiv_nonneg (f : C(L1UnitStone μ, ℝ)) :
    0 ≤ realStoneLInfinityEquiv μ f ↔ 0 ≤ f := by
  change 0 ≤ lOneOrderUnitLInfinityEquiv (lOneUnitStoneEquiv μ)
    (lOneUnitStoneEquiv_nonneg μ) (lOneUnitStoneEquiv_one μ)
    (booleanStoneContinuousLInfinityEquiv (𝕜 := ℝ) (lOneUnitStoneMeasure μ)
      (lOneUnitStoneMeasure_positive μ) (lOneUnitStoneMeasure_represents_sets μ) f) ↔ 0 ≤ f
  rw [lOneOrderUnitLInfinityEquiv_nonneg, booleanStoneContinuousLInfinityEquiv_nonneg]

theorem realStoneLInfinityEquiv_one : realStoneLInfinityEquiv μ 1 = linftyOne μ := by
  have h : booleanStoneContinuousLInfinityEquiv (𝕜 := ℝ) (lOneUnitStoneMeasure μ)
      (lOneUnitStoneMeasure_positive μ) (lOneUnitStoneMeasure_represents_sets μ) (1 : C(_, ℝ)) =
      linftyOne (lOneUnitStoneMeasure μ) := by
    apply Lp.ext
    filter_upwards [booleanStoneContinuousLInfinityIsometry_coe (𝕜 := ℝ) (lOneUnitStoneMeasure μ)
      (lOneUnitStoneMeasure_positive μ) (1 : C(_, ℝ)),
      linftyOne_coe (μ := lOneUnitStoneMeasure μ)] with p hp ho
    exact hp.trans ho.symm
  change lOneOrderUnitLInfinityEquiv (lOneUnitStoneEquiv μ)
    (lOneUnitStoneEquiv_nonneg μ) (lOneUnitStoneEquiv_one μ)
    (booleanStoneContinuousLInfinityEquiv (𝕜 := ℝ) (lOneUnitStoneMeasure μ)
      (lOneUnitStoneMeasure_positive μ) (lOneUnitStoneMeasure_represents_sets μ) 1) = _
  rw [h, lOneOrderUnitLInfinityEquiv_one]

def complexStoneLInfinityEquiv : C(L1UnitStone μ, ℂ) ≃ₗᵢ[ℂ] Lp ℂ ∞ μ :=
  continuousMapLpComplexificationEquiv (realStoneLInfinityEquiv μ)
    (realStoneLInfinityEquiv_nonneg μ)

end ThesisCommon

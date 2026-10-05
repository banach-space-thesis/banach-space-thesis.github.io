import ThesisCommon.Analysis.MeasureDensityL1
import ThesisCommon.Analysis.L1IndicatorExt
import Mathlib.MeasureTheory.Integral.SetToL1
import Mathlib.MeasureTheory.Measure.Prod

/-! A positive bounded real L1 operator constructed from a finite product
measure with dominated first marginal and absolutely continuous second marginal.
The construction extends the Radon--Nikodym densities of rectangle slices;
no topological or countable-generation hypotheses are imposed. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ThesisCommon
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

def productSliceMeasure (ρ : Measure (X × Y)) (a : Set X) : Measure Y :=
  (ρ.restrict (a ×ˢ univ)).snd

instance productSliceMeasure_finite (ρ : Measure (X × Y)) [IsFiniteMeasure ρ] (a : Set X) :
    IsFiniteMeasure (productSliceMeasure ρ a) := by
  unfold productSliceMeasure
  infer_instance

theorem productSliceMeasure_apply (ρ : Measure (X × Y)) (a : Set X)
    (b : Set Y) (hb : MeasurableSet b) :
    productSliceMeasure ρ a b = ρ (a ×ˢ b) := by
  rw [productSliceMeasure, Measure.snd_apply hb, Measure.restrict_apply (measurable_snd hb)]
  congr 1
  ext z
  simp [and_comm]

theorem productSliceMeasure_univ (ρ : Measure (X × Y)) (a : Set X) (ha : MeasurableSet a) :
    productSliceMeasure ρ a univ = ρ.fst a := by
  rw [productSliceMeasure_apply ρ a univ MeasurableSet.univ, Measure.fst_apply ha]
  congr 1
  ext z
  simp

theorem productSliceMeasure_le_snd (ρ : Measure (X × Y)) (a : Set X) :
    productSliceMeasure ρ a ≤ ρ.snd :=
  Measure.snd_mono Measure.restrict_le_self

theorem productSliceMeasure_absolutelyContinuous (ρ : Measure (X × Y)) {ν : Measure Y}
    (hAC : ρ.snd ≪ ν) (a : Set X) : productSliceMeasure ρ a ≪ ν :=
  (Measure.absolutelyContinuous_of_le (productSliceMeasure_le_snd ρ a)).trans hAC

theorem productSliceMeasure_union (ρ : Measure (X × Y)) (a b : Set X)
    (hb : MeasurableSet b) (hab : Disjoint a b) :
    productSliceMeasure ρ (a ∪ b) = productSliceMeasure ρ a + productSliceMeasure ρ b := by
  apply Measure.ext
  intro s hs
  rw [Measure.add_apply, productSliceMeasure_apply ρ (a ∪ b) s hs,
    productSliceMeasure_apply ρ a s hs, productSliceMeasure_apply ρ b s hs, union_prod]
  apply measure_union _ (hb.prod hs)
  exact Set.disjoint_left.mpr fun z hz hz' => Set.disjoint_left.mp hab hz.1 hz'.1

variable (μ : Measure X) (ν : Measure Y) (ρ : Measure (X × Y))
variable [IsFiniteMeasure μ] [SigmaFinite ν] [IsFiniteMeasure ρ]
variable (C : ℝ) (hC : 0 ≤ C) (hfst : ρ.fst ≤ ENNReal.ofReal C • μ) (hsnd : ρ.snd ≪ ν)

def productMeasureIndicatorMap (a : Set X) : ℝ →L[ℝ] Lp ℝ 1 ν := by
  classical
  exact if MeasurableSet a then
    ContinuousLinearMap.toSpanSingleton ℝ (measureDensityL1 (productSliceMeasure ρ a) ν)
  else 0

omit [SigmaFinite ν] in
theorem productMeasureIndicatorMap_apply (a : Set X) (ha : MeasurableSet a) (c : ℝ) :
    productMeasureIndicatorMap ν ρ a c = c • measureDensityL1 (productSliceMeasure ρ a) ν := by
  simp only [productMeasureIndicatorMap, if_pos ha, ContinuousLinearMap.toSpanSingleton_apply]

omit [IsFiniteMeasure μ] in
theorem productMeasureIndicatorMap_finMeasAdditive :
    FinMeasAdditive μ (productMeasureIndicatorMap ν ρ) := by
  intro a b ha hb _ _ hab
  apply ContinuousLinearMap.ext
  intro c
  rw [productMeasureIndicatorMap_apply ν ρ _ (ha.union hb), ContinuousLinearMap.add_apply,
    productMeasureIndicatorMap_apply ν ρ _ ha, productMeasureIndicatorMap_apply ν ρ _ hb,
    ← smul_add]
  simp only [productSliceMeasure_union ρ a b hb hab, measureDensityL1_add]

include hC hfst hsnd in
theorem productMeasureIndicatorMap_dominated :
    DominatedFinMeasAdditive μ (productMeasureIndicatorMap ν ρ) C := by
  refine ⟨productMeasureIndicatorMap_finMeasAdditive μ ν ρ, ?_⟩
  intro a ha _
  rw [productMeasureIndicatorMap, if_pos ha, ContinuousLinearMap.norm_toSpanSingleton,
    norm_measureDensityL1 _ _ (productSliceMeasure_absolutelyContinuous ρ hsnd a),
    productSliceMeasure_univ ρ a ha]
  have h := ENNReal.toReal_mono (show (ENNReal.ofReal C • μ) a ≠ ∞ by
      rw [Measure.smul_apply, smul_eq_mul]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top μ a))
    (hfst a)
  simpa only [Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hC, Measure.real] using h

def operatorOfProductMeasure : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν :=
  L1.setToL1 (productMeasureIndicatorMap_dominated μ ν ρ C hC hfst hsnd)

theorem operatorOfProductMeasure_indicator (a : Set X) (ha : MeasurableSet a) :
    operatorOfProductMeasure μ ν ρ C hC hfst hsnd (lOneIndicator μ a ha) =
      measureDensityL1 (productSliceMeasure ρ a) ν := by
  have h := L1.setToL1_indicatorConstLp
    (productMeasureIndicatorMap_dominated μ ν ρ C hC hfst hsnd) ha (measure_ne_top μ a) (1 : ℝ)
  rw [indicatorConstLp_eq_smul_lOneIndicator, one_smul,
    productMeasureIndicatorMap_apply ν ρ a ha, one_smul] at h
  exact h

theorem operatorOfProductMeasure_nonneg {f : Lp ℝ 1 μ} (hf : 0 ≤ f) :
    0 ≤ operatorOfProductMeasure μ ν ρ C hC hfst hsnd f := by
  apply L1.setToL1_nonneg (productMeasureIndicatorMap_dominated μ ν ρ C hC hfst hsnd) _ hf
  intro a ha _ c hc
  rw [productMeasureIndicatorMap_apply ν ρ a ha]
  exact smul_nonneg hc (measureDensityL1_nonneg _ _)

theorem operatorOfProductMeasure_norm_le :
    ‖operatorOfProductMeasure μ ν ρ C hC hfst hsnd‖ ≤ C :=
  L1.norm_setToL1_le (productMeasureIndicatorMap_dominated μ ν ρ C hC hfst hsnd) hC

theorem operatorOfProductMeasure_rectangle (a : Set X) (ha : MeasurableSet a)
    (b : Set Y) (hb : MeasurableSet b) :
    (∫ y in b, operatorOfProductMeasure μ ν ρ C hC hfst hsnd (lOneIndicator μ a ha) y ∂ν) =
      (ρ (a ×ˢ b)).toReal := by
  rw [operatorOfProductMeasure_indicator, measureDensityL1_setIntegral _ _
    (productSliceMeasure_absolutelyContinuous ρ hsnd a) b hb,
    productSliceMeasure_apply ρ a b hb]

theorem operatorOfProductMeasure_rectangle_ofReal (a : Set X) (ha : MeasurableSet a)
    (b : Set Y) (hb : MeasurableSet b) :
    ENNReal.ofReal (∫ y in b,
      operatorOfProductMeasure μ ν ρ C hC hfst hsnd (lOneIndicator μ a ha) y ∂ν) = ρ (a ×ˢ b) := by
  rw [operatorOfProductMeasure_rectangle μ ν ρ C hC hfst hsnd a ha b hb,
    ENNReal.ofReal_toReal (measure_ne_top ρ _)]

theorem operatorOfProductMeasure_unique (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν)
    (hS : ∀ a ha b, MeasurableSet b →
      (∫ y in b, S (lOneIndicator μ a ha) y ∂ν) = (ρ (a ×ˢ b)).toReal) :
    S = operatorOfProductMeasure μ ν ρ C hC hfst hsnd := by
  apply lOne_continuousLinearMap_ext_indicators
  intro a ha
  apply lOne_eq_of_setIntegrals_eq
  intro b hb _
  rw [hS a ha b hb, operatorOfProductMeasure_rectangle μ ν ρ C hC hfst hsnd a ha b hb]

end ThesisCommon

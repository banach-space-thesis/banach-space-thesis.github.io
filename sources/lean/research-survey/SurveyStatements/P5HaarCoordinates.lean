import SurveyStatements.P5HaarNorm
import SurveyStatements.P5Support.LpHaarCoefficient

/-! Bounded coefficient maps on the actual scalar and mixed Bochner spaces.
Their values are defined by Haar integration, rather than formal coordinates. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped ENNReal

namespace SurveyStatements.P5

theorem dyadicChildren_disjoint (I : DyadicIndex) :
    Disjoint (dyadicLeft I) (dyadicRight I) := by
  apply Set.disjoint_left.mpr
  intro x hL hR
  exact not_lt_of_ge hR.1 hL.2

theorem dyadicChildren_union (I : DyadicIndex) :
    dyadicLeft I ∪ dyadicRight I = dyadicInterval I := by
  ext x
  constructor
  · rintro (h | h)
    · exact ⟨h.1, h.2.trans_le (dyadicEndpoints I).2.2.1⟩
    · exact ⟨(dyadicEndpoints I).2.1.trans h.1, h.2⟩
  · intro h
    by_cases hm : x < dyadicMiddle I
    · exact Or.inl ⟨h.1, hm⟩
    · exact Or.inr ⟨le_of_not_gt hm, h.2⟩

theorem dyadicInterval_measure_ne_zero (I : DyadicIndex) :
    unitIntervalMeasure (dyadicInterval I) ≠ 0 := by
  intro h
  have hr := dyadicInterval_real_measure I
  rw [Measure.real, h, ENNReal.toReal_zero] at hr
  exact (ne_of_gt (by positivity : 0 < ((2 : ℝ) ^ I.1)⁻¹)) hr.symm

variable (𝕜 : Type*) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)]

def dyadicHaarCoordinate (I : DyadicIndex) : Lp 𝕜 p unitIntervalMeasure →L[𝕜] 𝕜 :=
  P5Support.lpHaarCoefficient (dyadicLeft I) (dyadicRight I)
    measurableSet_Ico measurableSet_Ico (dyadicChildren_disjoint I)

theorem dyadicHaarCoordinate_self (I : DyadicIndex) :
    dyadicHaarCoordinate 𝕜 p I (dyadicHaar 𝕜 p I) = 1 := by
  exact P5Support.lpHaarCoefficient_self _ _ _ _ _
    (by rw [dyadicChildren_union]; exact dyadicInterval_measure_ne_zero I)

theorem norm_dyadicHaarCoordinate_le (I : DyadicIndex) :
    ‖dyadicHaarCoordinate 𝕜 p I‖ ≤ (2 : ℝ) ^ I.1 := by
  have h := P5Support.norm_lpHaarCoefficient_le (𝕜 := 𝕜) (p := p)
    (μ := unitIntervalMeasure) (dyadicLeft I) (dyadicRight I)
    measurableSet_Ico measurableSet_Ico (dyadicChildren_disjoint I)
  rw [dyadicChildren_union, dyadicInterval_real_measure, inv_inv] at h
  exact h

theorem innerFunctional_tensor (L : Lp 𝕜 1 unitIntervalMeasure →L[𝕜] 𝕜)
    (g : Lp 𝕜 1 unitIntervalMeasure) (x : Lp 𝕜 p unitIntervalMeasure) :
    L.compLpL p unitIntervalMeasure (tensorWith g x) = (L g) • x := by
  apply Lp.ext
  filter_upwards [L.coeFn_compLpL (tensorWith g x), tensorWith_ae g x,
    Lp.coeFn_smul (L g) x] with s hL ht hs
  change (L.compLpL p unitIntervalMeasure (tensorWith g x)) s = ((L g) • x) s
  rw [hL, ht, hs, map_smul]
  exact mul_comm _ _

def productHaarCoordinate (I J : DyadicIndex) : MixedNorm 𝕜 p →L[𝕜] 𝕜 :=
  (dyadicHaarCoordinate 𝕜 p I).comp
    ((dyadicHaarCoordinate 𝕜 1 J).compLpL p unitIntervalMeasure)

theorem productHaarCoordinate_tensor (I J : DyadicIndex)
    (g : Lp 𝕜 1 unitIntervalMeasure) (x : Lp 𝕜 p unitIntervalMeasure) :
    productHaarCoordinate 𝕜 p I J (tensorWith g x) =
      dyadicHaarCoordinate 𝕜 1 J g * dyadicHaarCoordinate 𝕜 p I x := by
  change dyadicHaarCoordinate 𝕜 p I
    ((dyadicHaarCoordinate 𝕜 1 J).compLpL p unitIntervalMeasure (tensorWith g x)) = _
  rw [innerFunctional_tensor, map_smul]
  rfl

theorem productHaarCoordinate_self (I J : DyadicIndex) :
    productHaarCoordinate 𝕜 p I J (productHaar 𝕜 p I J) = 1 := by
  rw [productHaar, productHaarCoordinate_tensor, dyadicHaarCoordinate_self,
    dyadicHaarCoordinate_self, mul_one]

theorem norm_productHaarCoordinate_le (I J : DyadicIndex) :
    ‖productHaarCoordinate 𝕜 p I J‖ ≤ (2 : ℝ) ^ I.1 * (2 : ℝ) ^ J.1 := by
  calc
    _ ≤ ‖dyadicHaarCoordinate 𝕜 p I‖ *
        ‖(dyadicHaarCoordinate 𝕜 1 J).compLpL p unitIntervalMeasure‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖dyadicHaarCoordinate 𝕜 p I‖ * ‖dyadicHaarCoordinate 𝕜 1 J‖ :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_compLpL_le _) (norm_nonneg _)
    _ ≤ _ := mul_le_mul (norm_dyadicHaarCoordinate_le 𝕜 p I)
      (norm_dyadicHaarCoordinate_le 𝕜 1 J) (norm_nonneg _) (by positivity)

end SurveyStatements.P5

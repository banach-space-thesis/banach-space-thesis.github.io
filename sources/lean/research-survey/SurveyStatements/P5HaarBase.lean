import SurveyStatements.P5Tensors
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Actual dyadic Haar elements in scalar Lp and their elementary product
tensors in the mixed Bochner space. Density and basis/multiplier estimates
are separate obligations, not assumed in these definitions. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal

namespace SurveyStatements.P5

/-- A dyadic interval is indexed by its level and its position at that level. -/
abbrev DyadicIndex := Σ n : ℕ, Fin (2 ^ n)

def dyadicStart (I : DyadicIndex) : ℝ := (I.2.val : ℝ) / (2 : ℝ) ^ I.1
def dyadicMiddle (I : DyadicIndex) : ℝ := ((I.2.val : ℝ) + 1 / 2) / (2 : ℝ) ^ I.1
def dyadicEnd (I : DyadicIndex) : ℝ := ((I.2.val : ℝ) + 1) / (2 : ℝ) ^ I.1
def dyadicLeft (I : DyadicIndex) : Set ℝ := Ico (dyadicStart I) (dyadicMiddle I)
def dyadicRight (I : DyadicIndex) : Set ℝ := Ico (dyadicMiddle I) (dyadicEnd I)

theorem dyadicEndpoints (I : DyadicIndex) :
    0 ≤ dyadicStart I ∧ dyadicStart I ≤ dyadicMiddle I ∧
      dyadicMiddle I ≤ dyadicEnd I ∧ dyadicEnd I ≤ 1 := by
  have hpow : 0 < (2 : ℝ) ^ I.1 := by positivity
  have hk : (I.2.val : ℝ) + 1 ≤ (2 : ℝ) ^ I.1 := by
    exact_mod_cast Nat.succ_le_of_lt I.2.isLt
  refine ⟨by unfold dyadicStart; positivity, ?_, ?_, ?_⟩
  · unfold dyadicStart dyadicMiddle
    exact (div_le_div_iff_of_pos_right hpow).mpr (by linarith)
  · unfold dyadicMiddle dyadicEnd
    exact (div_le_div_iff_of_pos_right hpow).mpr (by linarith)
  · unfold dyadicEnd
    exact (div_le_one hpow).mpr hk

theorem dyadicLeft_subset (I : DyadicIndex) : dyadicLeft I ⊆ Icc (0 : ℝ) 1 := by
  intro x hx
  have h := dyadicEndpoints I
  exact ⟨h.1.trans hx.1, hx.2.le.trans (h.2.2.1.trans h.2.2.2)⟩

theorem dyadicRight_subset (I : DyadicIndex) : dyadicRight I ⊆ Icc (0 : ℝ) 1 := by
  intro x hx
  have h := dyadicEndpoints I
  exact ⟨(h.1.trans h.2.1).trans hx.1, hx.2.le.trans h.2.2.2⟩

theorem dyadicLeft_measure (I : DyadicIndex) :
    unitIntervalMeasure (dyadicLeft I) = ENNReal.ofReal (dyadicMiddle I - dyadicStart I) := by
  rw [unitIntervalMeasure, Measure.restrict_apply
      (show MeasurableSet (dyadicLeft I) from measurableSet_Ico),
    inter_eq_left.mpr (dyadicLeft_subset I)]
  exact Real.volume_Ico

theorem dyadicRight_measure (I : DyadicIndex) :
    unitIntervalMeasure (dyadicRight I) = ENNReal.ofReal (dyadicEnd I - dyadicMiddle I) := by
  rw [unitIntervalMeasure, Measure.restrict_apply
      (show MeasurableSet (dyadicRight I) from measurableSet_Ico),
    inter_eq_left.mpr (dyadicRight_subset I)]
  exact Real.volume_Ico

theorem dyadicChildren_equal_measure (I : DyadicIndex) :
    unitIntervalMeasure (dyadicLeft I) = unitIntervalMeasure (dyadicRight I) := by
  rw [dyadicLeft_measure, dyadicRight_measure]
  congr 1
  unfold dyadicStart dyadicMiddle dyadicEnd
  ring

variable (𝕜 : Type*) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- The sign-valued Haar vector `1_(I⁺) - 1_(I⁻)` as a genuine Lp element. -/
def dyadicHaar (I : DyadicIndex) : Lp 𝕜 p unitIntervalMeasure :=
  indicatorConstLp p (s := dyadicLeft I) measurableSet_Ico (measure_ne_top _ _) (1 : 𝕜) -
    indicatorConstLp p (s := dyadicRight I) measurableSet_Ico (measure_ne_top _ _) (1 : 𝕜)

theorem dyadicHaar_integral_zero (I : DyadicIndex) :
    probabilityLpIntegral (𝕜 := 𝕜) (dyadicHaar 𝕜 p I) = 0 := by
  rw [dyadicHaar, map_sub, probabilityLpIntegral_indicator, probabilityLpIntegral_indicator]
  simp only [Measure.real, dyadicChildren_equal_measure, sub_self]

theorem dyadicHaar_mean_zero (I : DyadicIndex) :
    probabilityLpMean (𝕜 := 𝕜) (dyadicHaar 𝕜 p I) = 0 := by
  rw [probabilityLpMean_apply, dyadicHaar_integral_zero]
  exact map_zero (Lp.constL p unitIntervalMeasure 𝕜)

/-- Product Haar vector with the inner factor in L1 and outer factor in Lp. -/
def productHaar (I J : DyadicIndex) : MixedNorm 𝕜 p :=
  tensorWith (dyadicHaar 𝕜 1 J) (dyadicHaar 𝕜 p I)

theorem productHaar_mem_doublyZeroMean (I J : DyadicIndex) :
    productHaar 𝕜 p I J ∈ DoublyZeroMean 𝕜 p :=
  tensor_mem_doublyZeroMean _ _ (dyadicHaar_mean_zero 𝕜 1 J)
    (dyadicHaar_mean_zero 𝕜 p I)

/-- The actual closed product-Haar span used in the source. -/
def ProductHaarSpace : Submodule 𝕜 (MixedNorm 𝕜 p) :=
  (Submodule.span 𝕜 (Set.range (fun IJ : DyadicIndex × DyadicIndex =>
    productHaar 𝕜 p IJ.1 IJ.2))).topologicalClosure

theorem productHaarSpace_le_doublyZeroMean :
    ProductHaarSpace 𝕜 p ≤ DoublyZeroMean 𝕜 p := by
  refine Submodule.topologicalClosure_minimal _ ?_ (doublyZeroMean_isClosed 𝕜 p)
  apply Submodule.span_le.mpr
  rintro _ ⟨IJ, rfl⟩
  exact productHaar_mem_doublyZeroMean 𝕜 p IJ.1 IJ.2

end SurveyStatements.P5

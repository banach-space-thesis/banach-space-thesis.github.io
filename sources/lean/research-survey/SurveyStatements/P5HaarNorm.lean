import SurveyStatements.P5HaarBase

/-! Exact norms of the genuine Haar and product-Haar vectors. These supply
the normalization used in coefficient and multiplier arguments. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped ENNReal

namespace SurveyStatements.P5

def dyadicInterval (I : DyadicIndex) : Set ℝ := Ico (dyadicStart I) (dyadicEnd I)

theorem dyadicInterval_subset (I : DyadicIndex) : dyadicInterval I ⊆ Icc (0 : ℝ) 1 := by
  intro x hx
  exact ⟨(dyadicEndpoints I).1.trans hx.1, hx.2.le.trans (dyadicEndpoints I).2.2.2⟩

theorem dyadicInterval_real_measure (I : DyadicIndex) :
    unitIntervalMeasure.real (dyadicInterval I) = ((2 : ℝ) ^ I.1)⁻¹ := by
  have hpow : 0 < (2 : ℝ) ^ I.1 := by positivity
  have hwidth : dyadicEnd I - dyadicStart I = ((2 : ℝ) ^ I.1)⁻¹ := by
    unfold dyadicEnd dyadicStart
    ring
  rw [Measure.real, unitIntervalMeasure, Measure.restrict_apply
      (show MeasurableSet (dyadicInterval I) from measurableSet_Ico),
    inter_eq_left.mpr (dyadicInterval_subset I), dyadicInterval, Real.volume_Ico, hwidth,
    ENNReal.toReal_ofReal (inv_nonneg.mpr hpow.le)]

variable (𝕜 : Type*) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)]

theorem norm_dyadicHaar_eq_indicator (I : DyadicIndex) :
    ‖dyadicHaar 𝕜 p I‖ =
      ‖indicatorConstLp p (s := dyadicInterval I) measurableSet_Ico
        (measure_ne_top unitIntervalMeasure _) (1 : 𝕜)‖ := by
  let fLeft := indicatorConstLp p (s := dyadicLeft I) measurableSet_Ico
    (measure_ne_top unitIntervalMeasure _) (1 : 𝕜)
  let fRight := indicatorConstLp p (s := dyadicRight I) measurableSet_Ico
    (measure_ne_top unitIntervalMeasure _) (1 : 𝕜)
  let f := indicatorConstLp p (s := dyadicInterval I) measurableSet_Ico
    (measure_ne_top unitIntervalMeasure _) (1 : 𝕜)
  have hnorm : ∀ᵐ x ∂unitIntervalMeasure, ‖(dyadicHaar 𝕜 p I) x‖ = ‖f x‖ := by
    filter_upwards [Lp.coeFn_sub fLeft fRight,
      indicatorConstLp_coeFn (p := p) (hs := (show MeasurableSet (dyadicLeft I) from measurableSet_Ico))
        (hμs := measure_ne_top unitIntervalMeasure _) (c := (1 : 𝕜)),
      indicatorConstLp_coeFn (p := p) (hs := (show MeasurableSet (dyadicRight I) from measurableSet_Ico))
        (hμs := measure_ne_top unitIntervalMeasure _) (c := (1 : 𝕜)),
      indicatorConstLp_coeFn (p := p) (hs := (show MeasurableSet (dyadicInterval I) from measurableSet_Ico))
        (hμs := measure_ne_top unitIntervalMeasure _) (c := (1 : 𝕜))]
      with x hsub hLeft hRight hf
    change ‖(fLeft - fRight) x‖ = ‖f x‖
    rw [hsub]
    change ‖fLeft x - fRight x‖ = ‖f x‖
    change fLeft x = (dyadicLeft I).indicator (fun _ => (1 : 𝕜)) x at hLeft
    change fRight x = (dyadicRight I).indicator (fun _ => (1 : 𝕜)) x at hRight
    change f x = (dyadicInterval I).indicator (fun _ => (1 : 𝕜)) x at hf
    rw [hLeft, hRight, hf]
    have he := dyadicEndpoints I
    by_cases hxLeft : x ∈ dyadicLeft I
    · have hxRight : x ∉ dyadicRight I := by
        intro h
        exact not_lt_of_ge h.1 hxLeft.2
      have hx : x ∈ dyadicInterval I := ⟨hxLeft.1, hxLeft.2.trans_le he.2.2.1⟩
      simp [hxLeft, hxRight, hx]
    · by_cases hxRight : x ∈ dyadicRight I
      · have hx : x ∈ dyadicInterval I := ⟨he.2.1.trans hxRight.1, hxRight.2⟩
        simp [hxLeft, hxRight, hx]
      · have hx : x ∉ dyadicInterval I := by
          intro h
          by_cases hm : x < dyadicMiddle I
          · exact hxLeft ⟨h.1, hm⟩
          · exact hxRight ⟨le_of_not_gt hm, h.2⟩
        simp [hxLeft, hxRight, hx]
  exact congrArg ENNReal.toReal (eLpNorm_congr_norm_ae (p := p) hnorm)

theorem norm_dyadicHaar (hp : p ≠ ∞) (I : DyadicIndex) :
    ‖dyadicHaar 𝕜 p I‖ = (((2 : ℝ) ^ I.1)⁻¹) ^ (1 / p.toReal) := by
  rw [norm_dyadicHaar_eq_indicator, norm_indicatorConstLp
    (ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ≥0∞) < 1) Fact.out)) hp,
    norm_one, one_mul, dyadicInterval_real_measure]

theorem norm_dyadicHaar_one (I : DyadicIndex) :
    ‖dyadicHaar 𝕜 1 I‖ = ((2 : ℝ) ^ I.1)⁻¹ := by
  simpa using norm_dyadicHaar 𝕜 1 (by norm_num) I

theorem norm_tensorWith (g : Lp 𝕜 1 unitIntervalMeasure)
    (x : Lp 𝕜 p unitIntervalMeasure) : ‖tensorWith g x‖ = ‖g‖ * ‖x‖ := by
  have heq : ∀ᵐ s ∂unitIntervalMeasure,
      ‖(tensorWith g x) s‖ = ‖((‖g‖ : 𝕜) • x) s‖ := by
    filter_upwards [tensorWith_ae g x, Lp.coeFn_smul (‖g‖ : 𝕜) x] with s ht hs
    rw [ht, hs]
    simp only [Pi.smul_apply, norm_smul, RCLike.norm_ofReal,
      abs_of_nonneg (norm_nonneg g), mul_comm]
  have hn : ‖tensorWith g x‖ = ‖(‖g‖ : 𝕜) • x‖ :=
    congrArg ENNReal.toReal (eLpNorm_congr_norm_ae (p := p) heq)
  rw [hn, norm_smul, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg g)]

theorem norm_productHaar (hp : p ≠ ∞) (I J : DyadicIndex) :
    ‖productHaar 𝕜 p I J‖ = ((2 : ℝ) ^ J.1)⁻¹ *
      (((2 : ℝ) ^ I.1)⁻¹) ^ (1 / p.toReal) := by
  rw [productHaar, norm_tensorWith, norm_dyadicHaar_one, norm_dyadicHaar 𝕜 p hp]

end SurveyStatements.P5


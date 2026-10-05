import ThesisCommon.Analysis.L1BoundedRangeDomination
import ThesisCommon.Analysis.SupportedWeakEssentialNormRestriction

/-! Restriction and support consequences of domination by a zero-extended
positive operator. These apply with arbitrary input and ambient measures. -/
noncomputable section
open MeasureTheory Filter
open scoped ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}

theorem lebesgueL1Restrict_mono (Θ : Set Y) :
    Monotone (lebesgueLpRestrict (𝕜 := ℝ) (E := ℝ) (p := 1) (μ := ν) Θ) := by
  intro f g hfg
  apply (Lp.coeFn_le _ _).mp
  filter_upwards [lebesgueLpRestrict_coe (𝕜 := ℝ) Θ f,
    lebesgueLpRestrict_coe (𝕜 := ℝ) Θ g,
    ae_restrict_of_ae ((Lp.coeFn_le _ _).mpr hfg)] with y hf hg hfg
  simpa only [hf, hg] using hfg

theorem lebesgueL1Restrict_abs (Θ : Set Y) (f : Lp ℝ 1 ν) :
    lebesgueLpRestrict (𝕜 := ℝ) Θ |f| = |lebesgueLpRestrict (𝕜 := ℝ) Θ f| := by
  apply Lp.ext
  filter_upwards [lebesgueLpRestrict_coe (𝕜 := ℝ) Θ |f|,
    lebesgueLpRestrict_coe (𝕜 := ℝ) Θ f, ae_restrict_of_ae (Lp.coeFn_abs f),
    Lp.coeFn_abs (lebesgueLpRestrict (𝕜 := ℝ) Θ f)] with y hr hf ha hb
  simp only [hr, hf, ha, hb]

theorem l1OperatorSupportedOn_of_abs_le_extend
    (Θ : Set Y) (hΘ : MeasurableSet Θ)
    {W : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν}
    {H : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 (ν.restrict Θ)}
    (hWH : |W| ≤ (lebesgueLpExtend (𝕜 := ℝ) Θ hΘ).toContinuousLinearMap.comp H) :
    L1OperatorSupportedOn Θ W := by
  intro f
  have hd : |W f| ≤ lebesgueLpExtend (𝕜 := ℝ) Θ hΘ (H |f|) :=
    (lOneOperatorModulus_dominates W f).trans
      (by simpa only [abs_lOneOperator_eq] using hWH |f| (abs_nonneg f))
  filter_upwards [ae_restrict_of_ae ((Lp.coeFn_le _ _).mpr hd),
    ae_restrict_of_ae (Lp.coeFn_abs (W f)),
    l1OperatorSupportedOn_extend Θ hΘ H |f|] with y hd ha hz
  change W f y = 0
  change |W f| y ≤ lebesgueLpExtend (𝕜 := ℝ) Θ hΘ (H |f|) y at hd
  rw [ha] at hd
  change lebesgueLpExtend (𝕜 := ℝ) Θ hΘ (H |f|) y = 0 at hz
  rw [hz] at hd
  exact abs_eq_zero.mp (le_antisymm hd (abs_nonneg _))

theorem abs_restrict_lOneOperator_le_of_abs_le_extend
    (Θ : Set Y) (hΘ : MeasurableSet Θ)
    {W : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν}
    {H : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 (ν.restrict Θ)}
    (hWH : |W| ≤ (lebesgueLpExtend (𝕜 := ℝ) Θ hΘ).toContinuousLinearMap.comp H) :
    |(lebesgueLpRestrict (𝕜 := ℝ) Θ).comp W| ≤ H := by
  rw [abs_lOneOperator_eq]
  apply lOneOperatorModulus_least
  intro f hf
  have hd₁ : |W f| ≤ lOneOperatorModulus W f := by
    simpa only [abs_of_nonneg hf] using lOneOperatorModulus_dominates W f
  have hd : |W f| ≤ lebesgueLpExtend (𝕜 := ℝ) Θ hΘ (H f) := hd₁.trans
    (by simpa only [abs_lOneOperator_eq] using hWH f hf)
  have h := lebesgueL1Restrict_mono Θ hd
  simpa only [lebesgueL1Restrict_abs, lebesgueLpRestrict_extend,
    ContinuousLinearMap.comp_apply] using h

theorem HasPositiveBoundedRangeApproximants.weaklyCompact_of_abs_le_extend
    (Θ : Set Y) (hΘ : MeasurableSet Θ) [IsFiniteMeasure (ν.restrict Θ)]
    {W : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν}
    {H : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 (ν.restrict Θ)}
    (hH : HasPositiveBoundedRangeApproximants H)
    (hWH : |W| ≤ (lebesgueLpExtend (𝕜 := ℝ) Θ hΘ).toContinuousLinearMap.comp H) :
    IsWeaklyCompactOperator W := by
  have hs := l1OperatorSupportedOn_of_abs_le_extend Θ hΘ hWH
  have hr := hH.weaklyCompact_of_abs_le (abs_restrict_lOneOperator_le_of_abs_le_extend Θ hΘ hWH)
  exact (weaklyCompact_lOneOperator_restrict_range_iff W Θ hΘ hs).mp hr

end ThesisCommon

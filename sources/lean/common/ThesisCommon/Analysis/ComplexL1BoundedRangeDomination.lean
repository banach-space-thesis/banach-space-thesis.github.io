import ThesisCommon.Analysis.L1SupportedDomination
import ThesisCommon.Analysis.ComplexL1WeakCompact
import ThesisCommon.Analysis.ComplexL1BandMembership

/-! Genuine complex weak compactness from positive bounded-range
approximants to a dominating real operator. The input measure is arbitrary;
only the output localization must have finite measure. -/
noncomputable section
open MeasureTheory Filter
open scoped ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}

theorem complexL1Operator_bounded_range_of_modulus_le
    {W : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν} {B : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν}
    (hWB : complexL1OperatorModulus W ≤ B)
    {C : ℝ} (hB : ∀ f, ∀ᵐ y ∂ν, ‖B f y‖ ≤ C * ‖f‖) :
    ∀ f, ∀ᵐ y ∂ν, ‖W f y‖ ≤ C * ‖f‖ := by
  intro f
  have hd : complexL1Modulus (W f) ≤ B (complexL1Modulus f) :=
    (complexL1OperatorModulus_dominates W f).trans
      (hWB _ (complexL1Modulus_nonneg f))
  filter_upwards [(Lp.coeFn_le _ _).mpr hd, complexL1Modulus_coe (W f),
    hB (complexL1Modulus f)] with y hd hm hb
  change complexL1Modulus (W f) y ≤ B (complexL1Modulus f) y at hd
  rw [hm] at hd
  exact hd.trans ((le_abs_self _).trans (by simpa only [norm_complexL1Modulus] using hb))

theorem HasPositiveBoundedRangeApproximants.weaklyCompact_of_complex_modulus_le
    [IsFiniteMeasure ν]
    {W : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν} {H : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν}
    (hH : HasPositiveBoundedRangeApproximants H) (hWH : complexL1OperatorModulus W ≤ H) :
    IsWeaklyCompactOperator W := by
  apply (weaklyCompact_complexL1_components_iff W).mpr
  exact ⟨hH.weaklyCompact_of_abs_le ((abs_complexL1OperatorRe_le_modulus W).trans hWH),
    hH.weaklyCompact_of_abs_le ((abs_complexL1OperatorIm_le_modulus W).trans hWH)⟩

theorem l1OperatorSupportedOn_of_complex_modulus_le_extend
    (Θ : Set Y) (hΘ : MeasurableSet Θ)
    {W : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν}
    {H : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 (ν.restrict Θ)}
    (hWH : complexL1OperatorModulus W ≤
      (lebesgueLpExtend (𝕜 := ℝ) Θ hΘ).toContinuousLinearMap.comp H) :
    L1OperatorSupportedOn Θ W := by
  intro f
  have hd : complexL1Modulus (W f) ≤
      lebesgueLpExtend (𝕜 := ℝ) Θ hΘ (H (complexL1Modulus f)) :=
    (complexL1OperatorModulus_dominates W f).trans
      (hWH _ (complexL1Modulus_nonneg f))
  filter_upwards [ae_restrict_of_ae ((Lp.coeFn_le _ _).mpr hd),
    ae_restrict_of_ae (complexL1Modulus_coe (W f)),
    l1OperatorSupportedOn_extend Θ hΘ H (complexL1Modulus f)] with y hd hm hz
  change W f y = 0
  change complexL1Modulus (W f) y ≤
    lebesgueLpExtend (𝕜 := ℝ) Θ hΘ (H (complexL1Modulus f)) y at hd
  rw [hm] at hd
  change lebesgueLpExtend (𝕜 := ℝ) Θ hΘ (H (complexL1Modulus f)) y = 0 at hz
  rw [hz] at hd
  exact norm_eq_zero.mp (le_antisymm hd (norm_nonneg _))

theorem HasPositiveBoundedRangeApproximants.weaklyCompact_of_complex_modulus_le_extend
    (Θ : Set Y) (hΘ : MeasurableSet Θ) [IsFiniteMeasure (ν.restrict Θ)]
    {W : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν}
    {H : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 (ν.restrict Θ)}
    (hH : HasPositiveBoundedRangeApproximants H)
    (hWH : complexL1OperatorModulus W ≤
      (lebesgueLpExtend (𝕜 := ℝ) Θ hΘ).toContinuousLinearMap.comp H) :
    IsWeaklyCompactOperator W := by
  apply (weaklyCompact_complexL1_components_iff W).mpr
  exact ⟨hH.weaklyCompact_of_abs_le_extend Θ hΘ
      ((abs_complexL1OperatorRe_le_modulus W).trans hWH),
    hH.weaklyCompact_of_abs_le_extend Θ hΘ
      ((abs_complexL1OperatorIm_le_modulus W).trans hWH)⟩

end ThesisCommon

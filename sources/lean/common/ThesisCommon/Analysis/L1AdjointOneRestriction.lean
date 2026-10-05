import ThesisCommon.Analysis.L1AdjointOneNormCriterion
import ThesisCommon.Analysis.LebesgueLpRestrictions

/-! Zero extension preserves the actual positive adjoint-at-one mass.
This gives the column norm criterion for a finite output part inside an
arbitrary ambient measure space. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}

theorem lebesgueL1Extend_nonneg (Θ : Set Y) (hΘ : MeasurableSet Θ)
    (f : Lp ℝ 1 (ν.restrict Θ)) (hf : 0 ≤ f) :
    0 ≤ lebesgueLpExtend (𝕜 := ℝ) Θ hΘ f := by
  apply (Lp.coeFn_nonneg _).mp
  filter_upwards [lebesgueLpExtend_coe (𝕜 := ℝ) Θ hΘ f,
    (ae_restrict_iff' hΘ).mp ((Lp.coeFn_nonneg f).mpr hf)] with y he hy
  rw [he]
  by_cases hyΘ : y ∈ Θ
  · simpa only [indicator_of_mem hyΘ] using hy hyΘ
  · simp only [indicator_of_notMem hyΘ, Pi.zero_apply, le_refl]

theorem integral_lebesgueL1Extend (Θ : Set Y) (hΘ : MeasurableSet Θ)
    (f : Lp ℝ 1 (ν.restrict Θ)) :
    (∫ y, lebesgueLpExtend (𝕜 := ℝ) Θ hΘ f y ∂ν) = ∫ y, f y ∂ν.restrict Θ := by
  rw [integral_congr_ae (lebesgueLpExtend_coe (𝕜 := ℝ) Θ hΘ f), integral_indicator hΘ]

theorem lebesgueL1Extend_comp_nonneg (Θ : Set Y) (hΘ : MeasurableSet Θ)
    {K : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 (ν.restrict Θ)} (hK : 0 ≤ K) :
    0 ≤ (lebesgueLpExtend (𝕜 := ℝ) Θ hΘ).toContinuousLinearMap.comp K :=
  fun f hf => lebesgueL1Extend_nonneg Θ hΘ (K f) (hK f hf)

variable [IsFiniteMeasure μ]

theorem positiveAdjointOne_extend (Θ : Set Y) (hΘ : MeasurableSet Θ)
    (K : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 (ν.restrict Θ)) (hK : 0 ≤ K) :
    positiveAdjointOne ((lebesgueLpExtend (𝕜 := ℝ) Θ hΘ).toContinuousLinearMap.comp K)
      (lebesgueL1Extend_comp_nonneg Θ hΘ hK) = positiveAdjointOne K hK := by
  apply linftyL1Pairing_injective
  apply ContinuousLinearMap.ext
  intro f
  rw [positiveAdjointOne_pairing_apply, positiveAdjointOne_pairing_apply]
  exact integral_lebesgueL1Extend Θ hΘ (K f)

theorem norm_positive_add_extended_integral_le_iff (Θ : Set Y) (hΘ : MeasurableSet Θ)
    [SFinite (ν.restrict Θ)]
    {S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν}
    {K : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 (ν.restrict Θ)} {k : X × Y → ℝ}
    (hS : 0 ≤ S) (hK : 0 ≤ K) (hk : IsIntegralKernel k K) {C : ℝ} (hC : 0 ≤ C) :
    ‖S + (lebesgueLpExtend (𝕜 := ℝ) Θ hΘ).toContinuousLinearMap.comp K‖ ≤ C ↔
      ∀ᵐ x ∂μ, positiveAdjointOneDensity S hS x + (∫ y, k (x, y) ∂ν.restrict Θ) ≤ C := by
  let R := S + (lebesgueLpExtend (𝕜 := ℝ) Θ hΘ).toContinuousLinearMap.comp K
  have hR : 0 ≤ R := add_nonneg hS (lebesgueL1Extend_comp_nonneg Θ hΘ hK)
  have heq : positiveAdjointOne R hR =ᵐ[μ] fun x =>
      positiveAdjointOneDensity S hS x + ∫ y, k (x, y) ∂ν.restrict Θ := by
    rw [positiveAdjointOne_add S _ hS (lebesgueL1Extend_comp_nonneg Θ hΘ hK),
      positiveAdjointOne_extend Θ hΘ K hK]
    filter_upwards [Lp.coeFn_add (positiveAdjointOne S hS) (positiveAdjointOne K hK),
      positiveAdjointOne_coe S hS, hk.positiveAdjointOne_eq_column_ae hK] with x h1 h2 h3
    simp only [h1, Pi.add_apply, h2, h3]
  constructor
  · intro hnorm
    filter_upwards [heq, linfty_ae_norm_le_norm (positiveAdjointOne R hR)] with x hx hb
    rw [norm_positiveAdjointOne] at hb
    rw [← hx]
    exact (le_abs_self _).trans (hb.trans hnorm)
  · intro hb
    rw [← norm_positiveAdjointOne R hR]
    apply linfty_norm_le_of_ae_bound _ hC
    filter_upwards [heq, hb, (Lp.coeFn_nonneg _).mpr (positiveAdjointOne_nonneg R hR)]
      with x hx hb hp
    rw [Real.norm_of_nonneg hp, hx]
    exact hb

theorem positive_extended_integral_tail_mass_le_norm (Θ : Set Y) (hΘ : MeasurableSet Θ)
    [SFinite (ν.restrict Θ)]
    {S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν}
    {K : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 (ν.restrict Θ)} {k : X × Y → ℝ}
    (hS : 0 ≤ S) (hk : IsIntegralKernel k K) (hpos : ∀ z, 0 ≤ k z) (r : ℝ) :
    ∀ᵐ x ∂μ, positiveAdjointOneDensity S hS x +
      (∫ y, ‖truncatedKernel r k (x, y)‖ ∂ν.restrict Θ) ≤
        ‖S + (lebesgueLpExtend (𝕜 := ℝ) Θ hΘ).toContinuousLinearMap.comp
          (hk.truncatedOperator r)‖ := by
  have htrpos : ∀ z, 0 ≤ truncatedKernel r k z :=
    fun z => indicator_nonneg (fun w _ => hpos w) z
  have htr : 0 ≤ hk.truncatedOperator r :=
    (hk.truncatedOperator_represents r).positive_of_nonneg_ae (Eventually.of_forall htrpos)
  have hb := (norm_positive_add_extended_integral_le_iff Θ hΘ hS htr
    (hk.truncatedOperator_represents r) (norm_nonneg _)).mp le_rfl
  simpa only [Real.norm_of_nonneg (htrpos _)] using hb

end ThesisCommon

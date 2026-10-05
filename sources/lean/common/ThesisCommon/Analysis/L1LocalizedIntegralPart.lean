import ThesisCommon.Analysis.IntegralOperatorBand
import ThesisCommon.Analysis.L1AdjointOneRestriction
import ThesisCommon.Analysis.DecomposableL1Order

/-! The integral part on a finite or sigma-finite output localization,
with its positive remainder in the full ambient output space. Only the
localized output needs a sigma-finite measure. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}

theorem lebesgueL1Extend_mono (Θ : Set Y) (hΘ : MeasurableSet Θ) :
    Monotone (lebesgueLpExtend (𝕜 := ℝ) (E := ℝ) (p := 1) (μ := ν) Θ hΘ) := by
  intro f g hfg
  have h := lebesgueL1Extend_nonneg Θ hΘ (g-f) (sub_nonneg.mpr hfg)
  simpa only [map_sub, sub_nonneg] using h

theorem lebesgueL1Extend_restrict_le (Θ : Set Y) (hΘ : MeasurableSet Θ)
    (f : Lp ℝ 1 ν) (hf : 0 ≤ f) :
    lebesgueLpExtend (𝕜 := ℝ) Θ hΘ (lebesgueLpRestrict (𝕜 := ℝ) Θ f) ≤ f := by
  apply (Lp.coeFn_le _ _).mp
  filter_upwards [lebesgueLpExtend_coe (𝕜 := ℝ) Θ hΘ (lebesgueLpRestrict (𝕜 := ℝ) Θ f),
    (ae_restrict_iff' hΘ).mp (lebesgueLpRestrict_coe (𝕜 := ℝ) Θ f),
    (Lp.coeFn_nonneg f).mpr hf] with y he hr hp
  rw [he]
  by_cases hy : y ∈ Θ
  · simp [hy, hr hy]
  · simpa [hy] using hp

variable [SigmaFinite μ] (Θ : Set Y) [SigmaFinite (ν.restrict Θ)]

def localizedIntegralPart (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) :
    Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 (ν.restrict Θ) :=
  integralBandProjection ((lebesgueLpRestrict (𝕜 := ℝ) Θ).comp T)

def localizedIntegralRemainder (hΘ : MeasurableSet Θ)
    (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν :=
  T - (lebesgueLpExtend (𝕜 := ℝ) Θ hΘ).toContinuousLinearMap.comp (localizedIntegralPart Θ T)

theorem localizedIntegralPart_isIntegral (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) :
    IsIntegralOperator (localizedIntegralPart Θ T) := integralBandProjection_isIntegral _

theorem localizedIntegralPart_nonneg {T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν} (hT : 0 ≤ T) :
    0 ≤ localizedIntegralPart Θ T :=
  integralBandProjection_nonneg _ (fun f hf => lebesgueL1Restrict_nonneg Θ (T f) (hT f hf))

theorem localizedIntegralPart_le_restrict {T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν} (hT : 0 ≤ T) :
    localizedIntegralPart Θ T ≤ (lebesgueLpRestrict (𝕜 := ℝ) Θ).comp T :=
  integralBandProjection_le_id _ (fun f hf => lebesgueL1Restrict_nonneg Θ (T f) (hT f hf))

theorem localizedIntegralPart_extend_le (hΘ : MeasurableSet Θ)
    {T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν} (hT : 0 ≤ T) :
    (lebesgueLpExtend (𝕜 := ℝ) Θ hΘ).toContinuousLinearMap.comp (localizedIntegralPart Θ T) ≤ T := by
  intro f hf
  exact (lebesgueL1Extend_mono Θ hΘ (localizedIntegralPart_le_restrict Θ hT f hf)).trans
    (lebesgueL1Extend_restrict_le Θ hΘ (T f) (hT f hf))

theorem localizedIntegralRemainder_nonneg (hΘ : MeasurableSet Θ)
    {T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν} (hT : 0 ≤ T) :
    0 ≤ localizedIntegralRemainder Θ hΘ T :=
  sub_nonneg.mpr (localizedIntegralPart_extend_le Θ hΘ hT)

theorem norm_localizedIntegralPart_le (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) :
    ‖localizedIntegralPart Θ T‖ ≤ ‖T‖ := by
  calc
    _ ≤ ‖integralBandProjection (μ := μ) (ν := ν.restrict Θ)‖ *
        ‖(lebesgueLpRestrict (𝕜 := ℝ) Θ).comp T‖ := integralBandProjection.le_opNorm _
    _ ≤ 1 * ‖(lebesgueLpRestrict (𝕜 := ℝ) Θ).comp T‖ :=
      mul_le_mul_of_nonneg_right norm_integralBandProjection_le_one (norm_nonneg _)
    _ = ‖(lebesgueLpRestrict (𝕜 := ℝ) Θ).comp T‖ := one_mul _
    _ ≤ ‖lebesgueLpRestrict (𝕜 := ℝ) (E := ℝ) (p := 1) (μ := ν) Θ‖ * ‖T‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * ‖T‖ := mul_le_mul_of_nonneg_right (norm_lebesgueLpRestrict_le Θ) (norm_nonneg T)
    _ = ‖T‖ := one_mul _

theorem localizedIntegralRemainder_restrict (hΘ : MeasurableSet Θ)
    (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) :
    (lebesgueLpRestrict (𝕜 := ℝ) Θ).comp (localizedIntegralRemainder Θ hΘ T) =
      (lebesgueLpRestrict (𝕜 := ℝ) Θ).comp T - localizedIntegralPart Θ T := by
  apply ContinuousLinearMap.ext
  intro f
  change lebesgueLpRestrict (𝕜 := ℝ) Θ
    (T f - lebesgueLpExtend (𝕜 := ℝ) Θ hΘ (localizedIntegralPart Θ T f)) = _
  rw [map_sub, lebesgueLpRestrict_extend]
  rfl

theorem localizedIntegralRemainder_restrict_singular (hΘ : MeasurableSet Θ)
    (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) :
    IsSingularOperator ((lebesgueLpRestrict (𝕜 := ℝ) Θ).comp (localizedIntegralRemainder Θ hΘ T)) := by
  rw [localizedIntegralRemainder_restrict]
  exact integralBandProjection_residual_singular _

theorem localizedIntegralRemainder_add_part (hΘ : MeasurableSet Θ)
    (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) :
    localizedIntegralRemainder Θ hΘ T +
      (lebesgueLpExtend (𝕜 := ℝ) Θ hΘ).toContinuousLinearMap.comp (localizedIntegralPart Θ T) = T :=
  sub_add_cancel _ _

/-- A pointwise nonnegative kernel is obtained from the proved modulus
kernel theorem, rather than chosen from an a.e.-positivity assertion. -/
theorem localizedIntegralPart_exists_nonnegative_kernel
    {T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν} (hT : 0 ≤ T) :
    ∃ k : X × Y → ℝ, IsIntegralKernel k (localizedIntegralPart Θ T) ∧ ∀ z, 0 ≤ k z := by
  obtain ⟨k, hk⟩ := localizedIntegralPart_isIntegral Θ T
  refine ⟨fun z => |k z|, ?_, fun z => abs_nonneg (k z)⟩
  simpa only [← abs_lOneOperator_eq, abs_of_nonneg (localizedIntegralPart_nonneg Θ hT)] using hk.modulus

theorem localizedIntegralRemainder_le (hΘ : MeasurableSet Θ)
    {T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν} (hT : 0 ≤ T) :
    localizedIntegralRemainder Θ hΘ T ≤ T :=
  sub_le_self _ (lebesgueL1Extend_comp_nonneg Θ hΘ (localizedIntegralPart_nonneg Θ hT))

theorem norm_localizedIntegralRemainder_le (hΘ : MeasurableSet Θ)
    {T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν} (hT : 0 ≤ T) :
    ‖localizedIntegralRemainder Θ hΘ T‖ ≤ ‖T‖ := by
  apply norm_le_norm_of_abs_le_abs
  rw [abs_of_nonneg (localizedIntegralRemainder_nonneg Θ hΘ hT), abs_of_nonneg hT]
  exact localizedIntegralRemainder_le Θ hΘ hT

end ThesisCommon

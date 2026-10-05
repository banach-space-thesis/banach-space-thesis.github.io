import ThesisCommon.Analysis.SupportedWeakEssentialNorm
import ThesisCommon.Analysis.L1DensityEquivRCLike

/-! The supported distance is invariant under onto output isometries that
preserve the specified support. A positive change of density has exactly
this property, proved from its actual multiplication representative. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E Y : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [MeasurableSpace Y] {ν ν' : Measure Y}

theorem supportedWeakEssentialNorm_postcomp_isometry_le
    (e : Lp 𝕜 1 ν ≃ₗᵢ[𝕜] Lp 𝕜 1 ν') (Θ : Set Y)
    (hsupport : ∀ f : Lp 𝕜 1 ν, f =ᵐ[ν.restrict Θᶜ] 0 → e f =ᵐ[ν'.restrict Θᶜ] 0)
    (T : E →L[𝕜] Lp 𝕜 1 ν) :
    supportedWeakEssentialNorm Θ (e.toLinearIsometry.toContinuousLinearMap.comp T) ≤
      supportedWeakEssentialNorm Θ T := by
  apply le_csInf
  · exact ⟨‖T - 0‖, 0, weaklyCompact_zero, l1OperatorSupportedOn_zero Θ, rfl⟩
  · rintro r ⟨W, hW, hs, rfl⟩
    have h := supportedWeakEssentialNorm_le Θ
      (e.toLinearIsometry.toContinuousLinearMap.comp T)
      (hW.comp_left e.toLinearIsometry.toContinuousLinearMap)
      (show L1OperatorSupportedOn Θ (e.toLinearIsometry.toContinuousLinearMap.comp W) from
        fun f => hsupport (W f) (hs f))
    rwa [← ContinuousLinearMap.comp_sub, e.toLinearIsometry.norm_toContinuousLinearMap_comp] at h

theorem supportedWeakEssentialNorm_postcomp_isometry
    (e : Lp 𝕜 1 ν ≃ₗᵢ[𝕜] Lp 𝕜 1 ν') (Θ : Set Y)
    (hsupport : ∀ f : Lp 𝕜 1 ν, e f =ᵐ[ν'.restrict Θᶜ] 0 ↔ f =ᵐ[ν.restrict Θᶜ] 0)
    (T : E →L[𝕜] Lp 𝕜 1 ν) :
    supportedWeakEssentialNorm Θ (e.toLinearIsometry.toContinuousLinearMap.comp T) =
      supportedWeakEssentialNorm Θ T := by
  apply le_antisymm (supportedWeakEssentialNorm_postcomp_isometry_le e Θ
    (fun f hf => (hsupport f).mpr hf) T)
  have hs : ∀ f : Lp 𝕜 1 ν', f =ᵐ[ν'.restrict Θᶜ] 0 →
      e.symm f =ᵐ[ν.restrict Θᶜ] 0 := by
    intro f hf
    apply (hsupport (e.symm f)).mp
    simpa only [LinearIsometryEquiv.apply_symm_apply] using hf
  have h := supportedWeakEssentialNorm_postcomp_isometry_le e.symm Θ hs
    (e.toLinearIsometry.toContinuousLinearMap.comp T)
  have heq : e.symm.toLinearIsometry.toContinuousLinearMap.comp
      (e.toLinearIsometry.toContinuousLinearMap.comp T) = T := by
    apply ContinuousLinearMap.ext
    intro f
    exact e.symm_apply_apply (T f)
  rwa [heq] at h

theorem lOneWithDensityEquiv_supported_iff
    {g : Y → ℝ≥0} (hg : Measurable g) (hpos : ∀ᵐ y ∂ν, 0 < g y)
    (Θ : Set Y) (hΘ : MeasurableSet Θ)
    (f : Lp 𝕜 1 (ν.withDensity (fun y => (g y : ℝ≥0∞)))) :
    lOneWithDensityEquiv_rclike hg hpos f =ᵐ[ν.restrict Θᶜ] 0 ↔
      f =ᵐ[(ν.withDensity (fun y => (g y : ℝ≥0∞))).restrict Θᶜ] 0 := by
  change (∀ᵐ y ∂ν.restrict Θᶜ, lOneWithDensityEquiv_rclike hg hpos f y = 0) ↔
    ∀ᵐ y ∂(ν.withDensity (fun y => (g y : ℝ≥0∞))).restrict Θᶜ, f y = 0
  rw [ae_restrict_iff' hΘ.compl, ae_restrict_iff' hΘ.compl,
    ae_withDensity_coe_iff_of_pos hg hpos]
  constructor
  · intro h
    filter_upwards [h, withDensitySMulLI_coe_rclike hg f, hpos] with y hy hc hp
    intro hyΘ
    have hz := hy hyΘ
    change withDensitySMulLI ν hg f y = 0 at hz
    rw [hc] at hz
    exact (smul_eq_zero.mp hz).resolve_left (by exact_mod_cast hp.ne')
  · intro h
    filter_upwards [h, withDensitySMulLI_coe_rclike hg f] with y hy hc
    intro hyΘ
    change withDensitySMulLI ν hg f y = 0
    rw [hc, hy hyΘ, smul_zero]

theorem supportedWeakEssentialNorm_withDensity
    {g : Y → ℝ≥0} (hg : Measurable g) (hpos : ∀ᵐ y ∂ν, 0 < g y)
    (Θ : Set Y) (hΘ : MeasurableSet Θ)
    (T : E →L[𝕜] Lp 𝕜 1 (ν.withDensity (fun y => (g y : ℝ≥0∞)))) :
    supportedWeakEssentialNorm Θ
      ((lOneWithDensityEquiv_rclike hg hpos).toLinearIsometry.toContinuousLinearMap.comp T) =
      supportedWeakEssentialNorm Θ T :=
  supportedWeakEssentialNorm_postcomp_isometry _ Θ
    (lOneWithDensityEquiv_supported_iff hg hpos Θ hΘ) T

end ThesisCommon

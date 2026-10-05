import ThesisCommon.Analysis.SupportedWeakEssentialNormDensity

/-! Genuine supported best approximants transport through an onto output
isometry preserving the support, including positive changes of density. -/
noncomputable section
open MeasureTheory Set Filter
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E Y : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [MeasurableSpace Y] {ν ν' : Measure Y}

theorem exists_supported_bestApproximation_postcomp_isometry
    (e : Lp 𝕜 1 ν ≃ₗᵢ[𝕜] Lp 𝕜 1 ν') (Θ : Set Y)
    (hsupport : ∀ f : Lp 𝕜 1 ν, e f =ᵐ[ν'.restrict Θᶜ] 0 ↔ f =ᵐ[ν.restrict Θᶜ] 0)
    (T : E →L[𝕜] Lp 𝕜 1 ν)
    (hbest : ∃ W : E →L[𝕜] Lp 𝕜 1 ν, IsWeaklyCompactOperator W ∧
      L1OperatorSupportedOn Θ W ∧ ‖T - W‖ = supportedWeakEssentialNorm Θ T) :
    ∃ W : E →L[𝕜] Lp 𝕜 1 ν', IsWeaklyCompactOperator W ∧ L1OperatorSupportedOn Θ W ∧
      ‖e.toLinearIsometry.toContinuousLinearMap.comp T - W‖ =
        supportedWeakEssentialNorm Θ (e.toLinearIsometry.toContinuousLinearMap.comp T) := by
  obtain ⟨W, hW, hs, hnorm⟩ := hbest
  refine ⟨e.toLinearIsometry.toContinuousLinearMap.comp W,
    hW.comp_left _, fun f => (hsupport (W f)).mpr (hs f), ?_⟩
  rw [← ContinuousLinearMap.comp_sub, e.toLinearIsometry.norm_toContinuousLinearMap_comp,
    hnorm, supportedWeakEssentialNorm_postcomp_isometry e Θ hsupport]

end ThesisCommon

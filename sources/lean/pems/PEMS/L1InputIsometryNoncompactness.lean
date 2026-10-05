import PEMS.L1WeakNoncompactness
import ThesisCommon.Analysis.OperatorIsometryTransport

/-! Exact input-isometry transport of the localized small-set functional,
the actual weak essential norm, and actual weak compactness. All measures
and either real or complex scalars are allowed. -/
noncomputable section
open MeasureTheory Set
namespace PEMS
open ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X X' Y : Type*} [MeasurableSpace X] [MeasurableSpace X'] [MeasurableSpace Y]
variable {μ : Measure X} {μ' : Measure X'} {ν : Measure Y}
variable (a : LOne 𝕜 μ' ≃ₗᵢ[𝕜] LOne 𝕜 μ) (T : LOne 𝕜 μ →L[𝕜] LOne 𝕜 ν)

theorem cutOperatorNorm_precomp_isometry (A : Set Y) (hA : MeasurableSet A) :
    cutOperatorNorm (T.comp a.toLinearIsometry.toContinuousLinearMap) A = cutOperatorNorm T A := by
  rw [cutOperatorNorm_eq _ A hA, cutOperatorNorm_eq T A hA,
    ← ContinuousLinearMap.comp_assoc, ContinuousLinearMap.opNorm_comp_linearIsometryEquiv]

theorem smallSetSup_precomp_isometry (Θ : Set Y) (hΘ : MeasurableSet Θ) (δ : ℝ) :
    smallSetSup (T.comp a.toLinearIsometry.toContinuousLinearMap) Θ δ = smallSetSup T Θ δ := by
  unfold smallSetSup
  congr 1
  ext q
  constructor
  · rintro ⟨B, hB, hsub, hsmall, rfl⟩
    exact ⟨B, hB, hsub, hsmall, cutOperatorNorm_precomp_isometry a T _ (hΘ.compl.union hB)⟩
  · rintro ⟨B, hB, hsub, hsmall, rfl⟩
    exact ⟨B, hB, hsub, hsmall, (cutOperatorNorm_precomp_isometry a T _ (hΘ.compl.union hB)).symm⟩

theorem alphaTheta_precomp_isometry (Θ : Set Y) (hΘ : MeasurableSet Θ) :
    alphaTheta (T.comp a.toLinearIsometry.toContinuousLinearMap) Θ = alphaTheta T Θ := by
  simp only [alphaTheta, smallSetSup_precomp_isometry a T Θ hΘ]

theorem localizedWeakNoncompactness_precomp_isometry :
    localizedWeakNoncompactness (T.comp a.toLinearIsometry.toContinuousLinearMap) =
      localizedWeakNoncompactness T := by
  unfold localizedWeakNoncompactness
  congr 1
  ext r
  constructor
  · rintro ⟨Θ, hΘ, hfin, rfl⟩
    exact ⟨Θ, hΘ, hfin, alphaTheta_precomp_isometry a T Θ hΘ⟩
  · rintro ⟨Θ, hΘ, hfin, rfl⟩
    exact ⟨Θ, hΘ, hfin, (alphaTheta_precomp_isometry a T Θ hΘ).symm⟩

theorem weakEssentialNorm_precomp_isometry :
    weakEssentialNorm (T.comp a.toLinearIsometry.toContinuousLinearMap) = weakEssentialNorm T := by
  have heq : operatorTransport a.symm (LinearIsometryEquiv.refl 𝕜 (LOne 𝕜 ν)) T =
      T.comp a.toLinearIsometry.toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro f
    rfl
  rw [← heq]
  exact weakEssentialNorm_operatorTransport _ _ T

theorem weaklyCompact_precomp_isometry_iff :
    IsWeaklyCompactOperator (T.comp a.toLinearIsometry.toContinuousLinearMap) ↔
      IsWeaklyCompactOperator T := by
  have heq : operatorTransport a.symm (LinearIsometryEquiv.refl 𝕜 (LOne 𝕜 ν)) T =
      T.comp a.toLinearIsometry.toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro f
    rfl
  rw [← heq]
  exact weaklyCompact_operatorTransport_iff _ _ T

end PEMS

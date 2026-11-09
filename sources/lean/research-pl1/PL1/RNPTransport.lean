import PL1.RNPBridge

/-! # RNP transport with the exact inherited real norm and scalar action -/

noncomputable section
universe u v w
namespace PL1.RNPTransport

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem hasRadonNikodymProperty_restrictScalars_iff (e : E ≃L[𝕜] F) :
    @HasRadonNikodymProperty.{u, w} (UnderlyingReal 𝕜 E)
      (inferInstanceAs (NormedAddCommGroup E)) (NormedSpace.restrictScalars ℝ 𝕜 E) ↔
    @HasRadonNikodymProperty.{v, w} (UnderlyingReal 𝕜 F)
      (inferInstanceAs (NormedAddCommGroup F)) (NormedSpace.restrictScalars ℝ 𝕜 F) := by
  let := NormedSpace.restrictScalars ℝ 𝕜 E
  let := NormedSpace.restrictScalars ℝ 𝕜 F
  let := IsScalarTower.restrictScalars ℝ 𝕜 E
  let := IsScalarTower.restrictScalars ℝ 𝕜 F
  change @HasRadonNikodymProperty.{u, w} E _ (NormedSpace.restrictScalars ℝ 𝕜 E) ↔
    @HasRadonNikodymProperty.{v, w} F _ (NormedSpace.restrictScalars ℝ 𝕜 F)
  let eR : E ≃L[ℝ] F := ContinuousLinearEquiv.equivOfInverse
    (e.toContinuousLinearMap.restrictScalars ℝ)
    (e.symm.toContinuousLinearMap.restrictScalars ℝ)
    e.symm_apply_apply e.apply_symm_apply
  exact RNPBridge.hasRadonNikodymProperty_iff_equiv eR

end PL1.RNPTransport

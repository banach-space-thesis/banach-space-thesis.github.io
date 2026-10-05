import PEMS.ContinuousMapMainFactorization
import PEMS.InfinityNormEqualities
import PEMS.FactorizationSupTransport
import ThesisCommon.Analysis.ContinuousMapAdjointApproximation
import ThesisCommon.Analysis.AdjointOperatorIsometryTransport

/-! Equality of all four quantities on actual extremally disconnected C(K)
spaces, and transport to a space with a supplied onto linear isometry to
such a C(K). Concrete consumers must construct that isometry. -/
noncomputable section
set_option maxSynthPendingDepth 3
set_option synthInstance.maxSize 1024
open ThesisCommon
namespace PEMS
variable {K : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K]
  [ExtremallyDisconnected K]

private theorem four_quantities_of_model_factorization
    {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (e : E ≃ₗᵢ[𝕜] C(K, 𝕜)) (T : E →L[𝕜] E)
    (h : dualWeakEssentialNorm (operatorTransport e e T) =
      factorizationSup (EllInfinity 𝕜) (operatorTransport e e T)) :
    weakEssentialNorm T = dualWeakEssentialNorm T ∧
      dualWeakEssentialNorm T = residuumNorm T ∧ residuumNorm T = deBlasiOperator T := by
  have ha : dualWeakEssentialNorm (operatorTransport e e T) = dualWeakEssentialNorm T :=
    weakEssentialNorm_banachAdjoint_operatorTransport e e T
  have hb : dualWeakEssentialNorm (operatorTransport e e T) = weakEssentialNorm T := by
    change weakEssentialNorm (banachAdjoint (operatorTransport e e T)) = _
    rw [weakEssentialNorm_banachAdjoint_eq_continuousMap, weakEssentialNorm_operatorTransport]
  have hadj : dualWeakEssentialNorm T = weakEssentialNorm T := ha.symm.trans hb
  have hfactor : weakEssentialNorm T = factorizationSup (EllInfinity 𝕜) T := by
    rw [← hb, ← factorizationSup_operatorTransport e e T]
    exact h
  exact ⟨hadj.symm, hadj.trans (weakEssentialNorm_eq_residuumNorm_of_infinity_factorization T hfactor),
    residuumNorm_eq_deBlasiOperator_of_infinity_factorization T hfactor⟩

theorem four_quantities_of_real_extremallyDisconnected_model
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : E ≃ₗᵢ[ℝ] C(K, ℝ)) (T : E →L[ℝ] E) :
    weakEssentialNorm T = dualWeakEssentialNorm T ∧
      dualWeakEssentialNorm T = residuumNorm T ∧ residuumNorm T = deBlasiOperator T :=
  four_quantities_of_model_factorization e T
    ((theorem_1_5_real (operatorTransport e e T)).2.2 inferInstance)

theorem four_quantities_of_complex_extremallyDisconnected_model
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (e : E ≃ₗᵢ[ℂ] C(K, ℂ)) (T : E →L[ℂ] E) :
    weakEssentialNorm T = dualWeakEssentialNorm T ∧
      dualWeakEssentialNorm T = residuumNorm T ∧ residuumNorm T = deBlasiOperator T :=
  four_quantities_of_model_factorization e T
    ((theorem_1_5_complex (operatorTransport e e T)).2.2 inferInstance)

theorem continuousMap_four_quantities_real (T : C(K, ℝ) →L[ℝ] C(K, ℝ)) :
    weakEssentialNorm T = dualWeakEssentialNorm T ∧
      dualWeakEssentialNorm T = residuumNorm T ∧ residuumNorm T = deBlasiOperator T :=
  four_quantities_of_real_extremallyDisconnected_model (LinearIsometryEquiv.refl ℝ C(K, ℝ)) T

theorem continuousMap_four_quantities_complex (T : C(K, ℂ) →L[ℂ] C(K, ℂ)) :
    weakEssentialNorm T = dualWeakEssentialNorm T ∧
      dualWeakEssentialNorm T = residuumNorm T ∧ residuumNorm T = deBlasiOperator T :=
  four_quantities_of_complex_extremallyDisconnected_model (LinearIsometryEquiv.refl ℂ C(K, ℂ)) T

end PEMS

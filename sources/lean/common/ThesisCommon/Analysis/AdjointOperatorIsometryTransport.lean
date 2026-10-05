import ThesisCommon.Analysis.OperatorIsometryTransport
import ThesisCommon.Analysis.AdjointWeakEssentialNorm
import ThesisCommon.Analysis.WeakEssentialNormProperties

/-! The adjoint weak essential norm is invariant under actual onto linear
isometries of both operator spaces. The proof uses the ideal estimates and
the contractivity of the adjoints of the forward and inverse isometries. -/
noncomputable section
set_option maxSynthPendingDepth 3
set_option synthInstance.maxSize 1024
namespace ThesisCommon
variable {𝕜 E F E' F' : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup F'] [NormedSpace 𝕜 F']

theorem weakEssentialNorm_banachAdjoint_operatorTransport_le
    (a : E ≃ₗᵢ[𝕜] E') (b : F ≃ₗᵢ[𝕜] F') (T : E →L[𝕜] F) :
    weakEssentialNorm (banachAdjoint (operatorTransport a b T)) ≤
      weakEssentialNorm (banachAdjoint T) := by
  let A := banachAdjoint a.symm.toLinearIsometry.toContinuousLinearMap
  let B := banachAdjoint b.toLinearIsometry.toContinuousLinearMap
  have hA : ‖A‖ ≤ 1 := by
    dsimp only [A]
    rw [norm_banachAdjoint]
    exact a.symm.toLinearIsometry.norm_toContinuousLinearMap_le
  have hB : ‖B‖ ≤ 1 := by
    dsimp only [B]
    rw [norm_banachAdjoint]
    exact b.toLinearIsometry.norm_toContinuousLinearMap_le
  have heq : banachAdjoint (operatorTransport a b T) =
      A.comp ((banachAdjoint T).comp B) := by
    ext φ x
    rfl
  rw [heq]
  calc
    weakEssentialNorm (A.comp ((banachAdjoint T).comp B)) ≤
        ‖A‖ * weakEssentialNorm ((banachAdjoint T).comp B) :=
      weakEssentialNorm_comp_left_le _ _
    _ ≤ weakEssentialNorm ((banachAdjoint T).comp B) :=
      mul_le_of_le_one_left (weakEssentialNorm_nonneg _) hA
    _ ≤ weakEssentialNorm (banachAdjoint T) * ‖B‖ := weakEssentialNorm_comp_right_le _ _
    _ ≤ weakEssentialNorm (banachAdjoint T) :=
      mul_le_of_le_one_right (weakEssentialNorm_nonneg _) hB

theorem weakEssentialNorm_banachAdjoint_operatorTransport
    (a : E ≃ₗᵢ[𝕜] E') (b : F ≃ₗᵢ[𝕜] F') (T : E →L[𝕜] F) :
    weakEssentialNorm (banachAdjoint (operatorTransport a b T)) =
      weakEssentialNorm (banachAdjoint T) := by
  apply le_antisymm (weakEssentialNorm_banachAdjoint_operatorTransport_le a b T)
  have h := weakEssentialNorm_banachAdjoint_operatorTransport_le a.symm b.symm (operatorTransport a b T)
  simpa only [operatorTransport_symm] using h

end ThesisCommon

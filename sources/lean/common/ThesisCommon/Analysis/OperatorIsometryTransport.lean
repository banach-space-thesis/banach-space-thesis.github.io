import ThesisCommon.WeakCompact
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-! Operator norms and weak compactness under isometric changes of coordinates.
Used by the measure-space reductions in PEMS; no nontriviality is required. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E F E' F' : Type*}
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
variable (a : E ≃ₗᵢ[𝕜] E') (b : F ≃ₗᵢ[𝕜] F')

def operatorTransport (T : E →L[𝕜] F) : E' →L[𝕜] F' :=
  b.toLinearIsometry.toContinuousLinearMap.comp
    (T.comp a.symm.toLinearIsometry.toContinuousLinearMap)

theorem operatorTransport_apply (T : E →L[𝕜] F) (x : E') :
    operatorTransport a b T x = b (T (a.symm x)) := rfl

theorem norm_operatorTransport (T : E →L[𝕜] F) : ‖operatorTransport a b T‖ = ‖T‖ := by
  rw [operatorTransport, b.toLinearIsometry.norm_toContinuousLinearMap_comp,
    T.opNorm_comp_linearIsometryEquiv]

theorem operatorTransport_symm (T : E →L[𝕜] F) :
    operatorTransport a.symm b.symm (operatorTransport a b T) = T := by
  ext x
  simp [operatorTransport_apply]

theorem operatorTransport_sub (T W : E →L[𝕜] F) :
    operatorTransport a b (T - W) = operatorTransport a b T - operatorTransport a b W := by
  ext x
  simp [operatorTransport_apply]

theorem weaklyCompact_operatorTransport_iff (T : E →L[𝕜] F) :
    IsWeaklyCompactOperator (operatorTransport a b T) ↔ IsWeaklyCompactOperator T := by
  constructor
  · intro h
    have hi := (h.comp_right a.toLinearIsometry.toContinuousLinearMap).comp_left
      b.symm.toLinearIsometry.toContinuousLinearMap
    change IsWeaklyCompactOperator (operatorTransport a.symm b.symm (operatorTransport a b T)) at hi
    rwa [operatorTransport_symm] at hi
  · intro h
    exact (h.comp_right a.symm.toLinearIsometry.toContinuousLinearMap).comp_left
      b.toLinearIsometry.toContinuousLinearMap

theorem weakEssentialNorm_operatorTransport_le (T : E →L[𝕜] F) :
    weakEssentialNorm (operatorTransport a b T) ≤ weakEssentialNorm T := by
  apply le_csInf
  · exact ⟨‖T - 0‖, 0, weaklyCompact_zero, rfl⟩
  · rintro r ⟨W, hW, rfl⟩
    calc
      weakEssentialNorm (operatorTransport a b T) ≤
          ‖operatorTransport a b T - operatorTransport a b W‖ :=
        weakEssentialNorm_le _ ((weaklyCompact_operatorTransport_iff a b W).mpr hW)
      _ = ‖T - W‖ := by rw [← operatorTransport_sub, norm_operatorTransport]

/-- Distance to the genuine weakly compact operator ideal is invariant under
isometric changes of both domain and range. -/
theorem weakEssentialNorm_operatorTransport (T : E →L[𝕜] F) :
    weakEssentialNorm (operatorTransport a b T) = weakEssentialNorm T := by
  apply le_antisymm (weakEssentialNorm_operatorTransport_le a b T)
  have h := weakEssentialNorm_operatorTransport_le a.symm b.symm (operatorTransport a b T)
  rwa [operatorTransport_symm] at h

end ThesisCommon

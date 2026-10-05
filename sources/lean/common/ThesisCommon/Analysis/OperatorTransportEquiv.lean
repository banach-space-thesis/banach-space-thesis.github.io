import ThesisCommon.Analysis.OperatorIsometryTransport

/-! Bundle the actual conjugation map as a linear isometry equivalence
on operator spaces. This permits transport of submodules without adding
linearity or inverse identities as assumptions. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E F E' F' : Type*}
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
variable (a : E ≃ₗᵢ[𝕜] E') (b : F ≃ₗᵢ[𝕜] F')

def operatorTransportLinearEquiv : (E →L[𝕜] F) ≃ₗ[𝕜] (E' →L[𝕜] F') where
  toFun := operatorTransport a b
  invFun := operatorTransport a.symm b.symm
  left_inv := operatorTransport_symm a b
  right_inv := operatorTransport_symm a.symm b.symm
  map_add' := by
    intro S T
    ext x
    simp [operatorTransport_apply]
  map_smul' := by
    intro c T
    ext x
    simp [operatorTransport_apply]

def operatorTransportLinearIsometryEquiv :
    (E →L[𝕜] F) ≃ₗᵢ[𝕜] (E' →L[𝕜] F') where
  toLinearEquiv := operatorTransportLinearEquiv a b
  norm_map' := norm_operatorTransport a b

end ThesisCommon

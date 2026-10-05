import PosetsCommon.Algebra
import JFA.SeparableRange
import Mathlib.Topology.Algebra.Module.StrongTopology

/-! Isometric change of coordinates for bounded-operator algebras. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 : Type} [RCLike 𝕜] {E F : Type}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

def operatorConjugation (e : E ≃ₗᵢ[𝕜] F) : (E →L[𝕜] E) ≃L[𝕜] (F →L[𝕜] F) :=
  e.toContinuousLinearEquiv.arrowCongr e.toContinuousLinearEquiv

theorem operatorConjugation_apply (e : E ≃ₗᵢ[𝕜] F) (T : E →L[𝕜] E) (x : F) :
    operatorConjugation e T x = e (T (e.symm x)) := rfl

theorem operatorConjugation_norm_le (e : E ≃ₗᵢ[𝕜] F) (T : E →L[𝕜] E) :
    ‖operatorConjugation e T‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
  intro x
  rw [operatorConjugation_apply, e.norm_map]
  simpa using T.le_opNorm (e.symm x)

theorem operatorConjugation_symm (e : E ≃ₗᵢ[𝕜] F) :
    (operatorConjugation e).symm = operatorConjugation e.symm := rfl

theorem operatorConjugation_norm (e : E ≃ₗᵢ[𝕜] F) (T : E →L[𝕜] E) :
    ‖operatorConjugation e T‖ = ‖T‖ := by
  apply le_antisymm (operatorConjugation_norm_le e T)
  have h := operatorConjugation_norm_le e.symm (operatorConjugation e T)
  rw [← operatorConjugation_symm, ContinuousLinearEquiv.symm_apply_apply] at h
  exact h

def operatorConjugationIsometry (e : E ≃ₗᵢ[𝕜] F) :
    (E →L[𝕜] E) ≃ₗᵢ[𝕜] (F →L[𝕜] F) :=
  { (operatorConjugation e).toLinearEquiv with norm_map' := operatorConjugation_norm e }

theorem operatorConjugation_mul (e : E ≃ₗᵢ[𝕜] F) (S T : E →L[𝕜] E) :
    operatorConjugation e (S * T) = operatorConjugation e S * operatorConjugation e T := by
  ext x
  simp [operatorConjugation_apply, ContinuousLinearMap.mul_apply]

def operatorConjugationHom (e : E ≃ₗᵢ[𝕜] F) : BoundedHom 𝕜 (E →L[𝕜] E) (F →L[𝕜] F) where
  toContinuousLinearMap := (operatorConjugation e).toContinuousLinearMap
  map_mul' := operatorConjugation_mul e

def operatorConjugationAlgEquiv (e : E ≃ₗᵢ[𝕜] F) :
    (E →L[𝕜] E) ≃ₐ[𝕜] (F →L[𝕜] F) :=
  AlgEquiv.ofLinearEquiv (operatorConjugation e).toLinearEquiv
    (by ext x; simp [operatorConjugation_apply]) (operatorConjugation_mul e)

theorem operatorConjugation_separable_iff (e : E ≃ₗᵢ[𝕜] F) (T : E →L[𝕜] E) :
    JFA.HasSeparableRange 𝕜 F F (operatorConjugation e T) ↔ JFA.HasSeparableRange 𝕜 E E T := by
  have hpres {A B : Type} [NormedAddCommGroup A] [NormedSpace 𝕜 A]
      [NormedAddCommGroup B] [NormedSpace 𝕜 B] (u : A ≃ₗᵢ[𝕜] B) (S : A →L[𝕜] A)
      (hS : JFA.HasSeparableRange 𝕜 A A S) :
      JFA.HasSeparableRange 𝕜 B B (operatorConjugation u S) :=
    (hS.comp_right u.symm.toContinuousLinearEquiv.toContinuousLinearMap).comp_left
      u.toContinuousLinearEquiv.toContinuousLinearMap
  constructor
  · intro hT
    have h := hpres e.symm _ hT
    rwa [← operatorConjugation_symm, ContinuousLinearEquiv.symm_apply_apply] at h
  · exact hpres e T

end ThesisCommon

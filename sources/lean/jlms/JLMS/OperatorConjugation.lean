import JLMS.EssentialNormCoordinates
import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# Conjugating operator algebras along a Banach-space isomorphism

The operator homomorphism is continuous and has a continuous inverse.
Automatic continuity therefore transfers between isomorphic spaces. For
isometric coordinate changes the essential norm is preserved exactly.
-/

noncomputable section
namespace JLMS
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

def operatorConjugation (e : E ≃L[𝕜] F) : (E →L[𝕜] E) →ₙₐ[𝕜] (F →L[𝕜] F) where
  toFun T := e.toContinuousLinearMap.comp (T.comp e.symm.toContinuousLinearMap)
  map_zero' := by ext x; simp
  map_add' S T := by ext x; simp
  map_smul' c T := by ext x; simp
  map_mul' S T := by
    apply ContinuousLinearMap.ext
    intro x
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, e.symm_apply_apply]

@[simp] theorem operatorConjugation_apply (e : E ≃L[𝕜] F) (T : E →L[𝕜] E) (x : F) :
    operatorConjugation e T x = e (T (e.symm x)) := rfl

theorem continuous_operatorConjugation (e : E ≃L[𝕜] F) : Continuous (operatorConjugation e) :=
  (continuous_id.clm_comp_const e.symm.toContinuousLinearMap).const_clm_comp e.toContinuousLinearMap

theorem norm_operatorConjugation_le (e : E ≃ₗᵢ[𝕜] F) (T : E →L[𝕜] E) :
    ‖operatorConjugation e.toContinuousLinearEquiv T‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
  intro x
  change ‖e (T (e.symm x))‖ ≤ _
  rw [e.norm_map]
  simpa only [e.symm.norm_map] using T.le_opNorm (e.symm x)

@[simp] theorem operatorConjugation_inverse (e : E ≃L[𝕜] F) (T : E →L[𝕜] E) :
    operatorConjugation e.symm (operatorConjugation e T) = T := by
  apply ContinuousLinearMap.ext
  intro x
  simp

theorem norm_operatorConjugation (e : E ≃ₗᵢ[𝕜] F) (T : E →L[𝕜] E) :
    ‖operatorConjugation e.toContinuousLinearEquiv T‖ = ‖T‖ := by
  apply le_antisymm (norm_operatorConjugation_le e T)
  have h := norm_operatorConjugation_le e.symm (operatorConjugation e.toContinuousLinearEquiv T)
  simpa only [LinearIsometryEquiv.toContinuousLinearEquiv_symm, operatorConjugation_inverse] using h

theorem continuous_operator_hom_of_conjugation
    {A : Type*} [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
    (e : E ≃L[𝕜] F) (φ : (E →L[𝕜] E) →ₙₐ[𝕜] A)
    (hφ : Continuous (φ.comp (operatorConjugation e.symm))) : Continuous φ := by
  have h := hφ.comp (continuous_operatorConjugation e)
  have heq : (fun T => φ.comp (operatorConjugation e.symm) (operatorConjugation e T)) = φ := by
    funext T
    simp
  exact heq ▸ h

theorem essentialNorm_operatorConjugation (e : E ≃ₗᵢ[𝕜] F) (T : E →L[𝕜] E) :
    essentialNorm (operatorConjugation e.toContinuousLinearEquiv T) = essentialNorm T := by
  change essentialNorm (e.toLinearIsometry.toContinuousLinearMap.comp
    (T.comp e.symm.toLinearIsometry.toContinuousLinearMap)) = _
  rw [essentialNorm_isometryEquiv_comp, essentialNorm_comp_isometryEquiv]

end JLMS

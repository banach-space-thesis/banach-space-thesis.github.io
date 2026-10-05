import Sigma.ComplexSelectedInjection
import Sigma.ComplexCrossedCoefficients
import ThesisCommon.Analysis.SigmaComplexProductDualCoefficients

/-! The full product coefficient representation is onto, and extension from
the crossed summand preserves functional norms exactly. -/
noncomputable section
namespace SigmaNonprimarity
open ThesisCommon
attribute [local instance] complexJLGroup complexJLSpace complexJLDualGroup complexJLDualSpace
attribute [local instance] complexPairedJLGroup complexPairedJLSpace complexPairedJLDualGroup
attribute [local instance] complexFinalCandidateGroup complexFinalCandidateSpace

def ComplexEnumeratedConstruction.fullCoefficientEquiv (D : ComplexEnumeratedConstruction) :
    (ComplexFinalJLProduct D →L[ℂ] ℂ) ≃ₗᵢ[ℂ] lp (fun _ : FullAtom => ℂ) 1 :=
  complexDualProdLpEquiv
    (complexIndexedJLDualEquiv (D.family_almostDisjoint false) (D.family_infinite false) (D.familyEquiv false))
    (complexIndexedJLDualEquiv (D.family_almostDisjoint true) (D.family_infinite true) (D.familyEquiv true))

@[simp] theorem ComplexEnumeratedConstruction.fullCoefficientEquiv_apply (D : ComplexEnumeratedConstruction)
    (φ : ComplexFinalJLProduct D →L[ℂ] ℂ) : D.fullCoefficientEquiv φ = D.coefficients φ := rfl

theorem ComplexEnumeratedConstruction.coefficients_add (D : ComplexEnumeratedConstruction)
    (φ ψ : ComplexFinalJLProduct D →L[ℂ] ℂ) : D.coefficients (φ+ψ) = D.coefficients φ + D.coefficients ψ :=
  D.fullCoefficientEquiv.map_add φ ψ

theorem ComplexEnumeratedConstruction.coefficients_smul (D : ComplexEnumeratedConstruction) (r : ℂ)
    (φ : ComplexFinalJLProduct D →L[ℂ] ℂ) : D.coefficients (r • φ) = r • D.coefficients φ :=
  D.fullCoefficientEquiv.map_smul r φ

theorem ComplexEnumeratedConstruction.crossedInjection_norm (D : ComplexEnumeratedConstruction) (side : Bool)
    (f : ComplexFinalCandidate D side) : ‖D.crossedInjection side f‖ = ‖f‖ := by
  cases side
  · change max ‖(0 : ComplexJL (D.family false)) + D.antisymmetricInclusion false f.2‖
      ‖D.cylinderInclusion true f.1 + 0‖ = max ‖f.1‖ ‖f.2‖
    rw [zero_add,add_zero]
    exact max_comm _ _
  · change max ‖D.cylinderInclusion false f.1 + 0‖
      ‖(0 : ComplexJL (D.family true)) + D.antisymmetricInclusion true f.2‖ = max ‖f.1‖ ‖f.2‖
    rw [add_zero,zero_add]
    rfl

theorem ComplexEnumeratedConstruction.extendCrossedFunctional_norm (D : ComplexEnumeratedConstruction) (side : Bool)
    (φ : ComplexFinalCandidate D side →L[ℂ] ℂ) : ‖D.extendCrossedFunctional side φ‖ = ‖φ‖ := by
  apply le_antisymm (D.extendCrossedFunctional_norm_le side φ)
  apply φ.opNorm_le_bound (norm_nonneg _)
  intro f
  have h := (D.extendCrossedFunctional side φ).le_opNorm (D.crossedInjection side f)
  change ‖φ (D.crossedProjection side (D.crossedInjection side f))‖ ≤ _ at h
  rwa [D.crossedProjection_rightInverse,D.crossedInjection_norm] at h

theorem ComplexEnumeratedConstruction.cylinderProjection_flip (D : ComplexEnumeratedConstruction) (side : Bool)
    (f : ComplexJL (D.family side)) : D.cylinderProjection side (D.flipJL side f) = D.cylinderProjection side f := by
  apply Subtype.ext
  change complexAverage (complexFlip f.val) = complexAverage f.val
  ext p
  simp only [complexAverage_apply,complexFlip_apply,Bool.not_not]
  ring

theorem ComplexEnumeratedConstruction.extendCrossedFunctional_symmetric (D : ComplexEnumeratedConstruction)
    (side : Bool) (φ : ComplexFinalCandidate D side →L[ℂ] ℂ) :
    ((D.extendCrossedFunctional side φ).comp (D.sideInjection (!side))).comp (D.flipJL (!side)) =
      (D.extendCrossedFunctional side φ).comp (D.sideInjection (!side)) := by
  apply ContinuousLinearMap.ext
  intro f
  change φ (D.crossedProjection side (D.sideInjection (!side) (D.flipJL (!side) f))) =
    φ (D.crossedProjection side (D.sideInjection (!side) f))
  rw [D.crossedProjection_injection_other,D.crossedProjection_injection_other,D.cylinderProjection_flip]

end SigmaNonprimarity



import Sigma.CrossedInjection
import ThesisCommon.Analysis.ProductDualCoefficients

/-! The full product coefficient representation is onto, and extension from
the crossed summand preserves functional norms exactly. -/
noncomputable section
namespace SigmaNonprimarity
open ThesisCommon
attribute [local instance] bridgeRealSpace bridgeJLGroup bridgeJLSpace jlDualGroup jlDualSpace
attribute [local instance] pairedJLGroup pairedJLSpace pairedJLDualGroup
attribute [local instance] finalCandidateGroup finalCandidateSpace

def EnumeratedConstruction.fullCoefficientEquiv (D : EnumeratedConstruction) :
    (FinalJLProduct D →L[ℝ] ℝ) ≃ₗᵢ[ℝ] lp (fun _ : FullAtom => ℝ) 1 :=
  dualProdLpEquiv
    (indexedJLDualEquiv (D.family_almostDisjoint false) (D.family_infinite false) (D.familyEquiv false))
    (indexedJLDualEquiv (D.family_almostDisjoint true) (D.family_infinite true) (D.familyEquiv true))

@[simp] theorem EnumeratedConstruction.fullCoefficientEquiv_apply (D : EnumeratedConstruction)
    (φ : FinalJLProduct D →L[ℝ] ℝ) : D.fullCoefficientEquiv φ = D.coefficients φ := rfl

theorem EnumeratedConstruction.coefficients_add (D : EnumeratedConstruction)
    (φ ψ : FinalJLProduct D →L[ℝ] ℝ) : D.coefficients (φ+ψ) = D.coefficients φ + D.coefficients ψ :=
  D.fullCoefficientEquiv.map_add φ ψ

theorem EnumeratedConstruction.coefficients_smul (D : EnumeratedConstruction) (r : ℝ)
    (φ : FinalJLProduct D →L[ℝ] ℝ) : D.coefficients (r • φ) = r • D.coefficients φ :=
  D.fullCoefficientEquiv.map_smul r φ

theorem EnumeratedConstruction.crossedInjection_norm (D : EnumeratedConstruction) (side : Bool)
    (f : FinalCandidate D side) : ‖D.crossedInjection side f‖ = ‖f‖ := by
  cases side
  · change max ‖(0 : JL (D.family false)) + D.antisymmetricInclusion false f.2‖
      ‖D.cylinderInclusion true f.1 + 0‖ = max ‖f.1‖ ‖f.2‖
    rw [zero_add,add_zero]
    exact max_comm _ _
  · change max ‖D.cylinderInclusion false f.1 + 0‖
      ‖(0 : JL (D.family true)) + D.antisymmetricInclusion true f.2‖ = max ‖f.1‖ ‖f.2‖
    rw [add_zero,zero_add]
    rfl

theorem EnumeratedConstruction.extendCrossedFunctional_norm (D : EnumeratedConstruction) (side : Bool)
    (φ : FinalCandidate D side →L[ℝ] ℝ) : ‖D.extendCrossedFunctional side φ‖ = ‖φ‖ := by
  apply le_antisymm (D.extendCrossedFunctional_norm_le side φ)
  apply φ.opNorm_le_bound (norm_nonneg _)
  intro f
  have h := (D.extendCrossedFunctional side φ).le_opNorm (D.crossedInjection side f)
  change ‖φ (D.crossedProjection side (D.crossedInjection side f))‖ ≤ _ at h
  rwa [D.crossedProjection_rightInverse,D.crossedInjection_norm] at h

theorem EnumeratedConstruction.cylinderProjection_flip (D : EnumeratedConstruction) (side : Bool)
    (f : JL (D.family side)) : D.cylinderProjection side (D.flipJL side f) = D.cylinderProjection side f := by
  apply Subtype.ext
  change average (flip f.val) = average f.val
  ext p
  simp only [average_apply,flip_apply,Bool.not_not]
  ring

theorem EnumeratedConstruction.extendCrossedFunctional_symmetric (D : EnumeratedConstruction)
    (side : Bool) (φ : FinalCandidate D side →L[ℝ] ℝ) :
    ((D.extendCrossedFunctional side φ).comp (D.sideInjection (!side))).comp (D.flipJL (!side)) =
      (D.extendCrossedFunctional side φ).comp (D.sideInjection (!side)) := by
  apply ContinuousLinearMap.ext
  intro f
  change φ (D.crossedProjection side (D.sideInjection (!side) (D.flipJL (!side) f))) =
    φ (D.crossedProjection side (D.sideInjection (!side) f))
  rw [D.crossedProjection_injection_other,D.crossedProjection_injection_other,D.cylinderProjection_flip]

end SigmaNonprimarity

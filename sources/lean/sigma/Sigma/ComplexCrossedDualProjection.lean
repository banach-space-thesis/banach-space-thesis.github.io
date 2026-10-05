import Sigma.ComplexCrossedDualNorm

/-! Coefficients of the two coordinate projections: averaging on the
cylinder copy and antisymmetrizing on the other copy. -/
noncomputable section
namespace SigmaNonprimarity
open ThesisCommon
attribute [local instance] complexJLGroup complexJLSpace complexJLDualGroup complexJLDualSpace
attribute [local instance] complexPairedJLGroup complexPairedJLSpace complexPairedJLDualGroup
attribute [local instance] complexFinalCandidateGroup complexFinalCandidateSpace

theorem ComplexEnumeratedConstruction.cylinderInclusion_projection (D : ComplexEnumeratedConstruction)
    (side : Bool) (f : ComplexJL (D.family side)) :
    D.cylinderInclusion side (D.cylinderProjection side f) = (1/2 : ℂ) • (f + D.flipJL side f) := by
  apply Subtype.ext
  ext p
  change complexAverage f.val p = (1/2 : ℂ) * (f.val p + complexFlip f.val p)
  simp only [complexAverage_apply,complexFlip_apply]
  ring

theorem ComplexEnumeratedConstruction.antisymmetricInclusion_projection (D : ComplexEnumeratedConstruction)
    (side : Bool) (f : ComplexJL (D.family side)) :
    D.antisymmetricInclusion side (D.antisymmetricProjection side f) =
      (1/2 : ℂ) • (f - D.flipJL side f) := by
  apply Subtype.ext
  ext p
  change complexAntiAverage f.val p = (1/2 : ℂ) * (f.val p - complexFlip f.val p)
  simp only [complexAntiAverage_apply,complexFlip_apply]
  ring

theorem ComplexEnumeratedConstruction.restrictedExtension_selected (D : ComplexEnumeratedConstruction) (side : Bool)
    (φ : ComplexFinalJLProduct D →L[ℂ] ℂ) :
    (D.extendCrossedFunctional side (φ.comp (D.crossedInjection side))).comp (D.sideInjection side) =
      (1/2 : ℂ) • ((φ.comp (D.sideInjection side)) -
        (φ.comp (D.sideInjection side)).comp (D.flipJL side)) := by
  apply ContinuousLinearMap.ext
  intro f
  change φ (D.crossedInjection side (D.crossedProjection side (D.sideInjection side f))) =
    (1/2 : ℂ) * (φ (D.sideInjection side f) - φ (D.sideInjection side (D.flipJL side f)))
  rw [D.crossedProjection_injection]
  change φ (D.sideInjection (!side) (D.cylinderInclusion (!side) 0) +
    D.sideInjection side (D.antisymmetricInclusion side (D.antisymmetricProjection side f))) = _
  rw [map_zero,map_zero,zero_add,D.antisymmetricInclusion_projection]
  simp only [map_smul,map_sub,smul_eq_mul]

theorem ComplexEnumeratedConstruction.restrictedExtension_other (D : ComplexEnumeratedConstruction) (side : Bool)
    (φ : ComplexFinalJLProduct D →L[ℂ] ℂ) :
    (D.extendCrossedFunctional side (φ.comp (D.crossedInjection side))).comp (D.sideInjection (!side)) =
      (1/2 : ℂ) • ((φ.comp (D.sideInjection (!side))) +
        (φ.comp (D.sideInjection (!side))).comp (D.flipJL (!side))) := by
  apply ContinuousLinearMap.ext
  intro f
  change φ (D.crossedInjection side (D.crossedProjection side (D.sideInjection (!side) f))) =
    (1/2 : ℂ) * (φ (D.sideInjection (!side) f) + φ (D.sideInjection (!side) (D.flipJL (!side) f)))
  rw [D.crossedProjection_injection_other]
  change φ (D.sideInjection (!side) (D.cylinderInclusion (!side) (D.cylinderProjection (!side) f)) +
    D.sideInjection side (D.antisymmetricInclusion side 0)) = _
  rw [map_zero,map_zero,add_zero,D.cylinderInclusion_projection]
  simp only [map_smul,map_add,smul_eq_mul]

theorem ComplexEnumeratedConstruction.restrictedCoefficients_selected (D : ComplexEnumeratedConstruction) (side : Bool)
    (φ : ComplexFinalJLProduct D →L[ℂ] ℂ) (p : IndexedAtom (ConstructionIndex × Bool)) :
    D.coefficients (D.extendCrossedFunctional side (φ.comp (D.crossedInjection side))) (side,p) =
      (1/2 : ℂ) * (D.coefficients φ (side,p) - D.coefficients φ (side,indexedAtomFlip p)) := by
  rw [D.coefficients_side,D.restrictedExtension_selected,map_smul,map_sub,D.indexedDual_flip]
  rw [D.coefficients_side,D.coefficients_side]
  rfl

theorem ComplexEnumeratedConstruction.restrictedCoefficients_other (D : ComplexEnumeratedConstruction) (side : Bool)
    (φ : ComplexFinalJLProduct D →L[ℂ] ℂ) (p : IndexedAtom (ConstructionIndex × Bool)) :
    D.coefficients (D.extendCrossedFunctional side (φ.comp (D.crossedInjection side))) (!side,p) =
      (1/2 : ℂ) * (D.coefficients φ (!side,p) + D.coefficients φ (!side,indexedAtomFlip p)) := by
  rw [D.coefficients_side,D.restrictedExtension_other,map_smul,map_add,D.indexedDual_flip]
  rw [D.coefficients_side,D.coefficients_side]
  rfl

theorem ComplexEnumeratedConstruction.extendedCoefficients_other_flip (D : ComplexEnumeratedConstruction) (side : Bool)
    (φ : ComplexFinalCandidate D side →L[ℂ] ℂ) (p : IndexedAtom (ConstructionIndex × Bool)) :
    D.coefficients (D.extendCrossedFunctional side φ) (!side,indexedAtomFlip p) =
      D.coefficients (D.extendCrossedFunctional side φ) (!side,p) := by
  rw [D.coefficients_side,D.coefficients_side]
  have h := D.indexedDual_flip (!side) ((D.extendCrossedFunctional side φ).comp (D.sideInjection (!side)))
  rw [D.extendCrossedFunctional_symmetric] at h
  exact (congrArg (fun c : lp (fun _ : IndexedAtom (ConstructionIndex × Bool) => ℂ) 1 => c p) h).symm

end SigmaNonprimarity



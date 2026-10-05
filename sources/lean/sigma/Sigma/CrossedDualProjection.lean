import Sigma.CrossedDualNorm

/-! Coefficients of the two coordinate projections: averaging on the
cylinder copy and antisymmetrizing on the other copy. -/
noncomputable section
namespace SigmaNonprimarity
open ThesisCommon
attribute [local instance] bridgeRealSpace bridgeJLGroup bridgeJLSpace jlDualGroup jlDualSpace
attribute [local instance] pairedJLGroup pairedJLSpace pairedJLDualGroup
attribute [local instance] finalCandidateGroup finalCandidateSpace

theorem EnumeratedConstruction.cylinderInclusion_projection (D : EnumeratedConstruction)
    (side : Bool) (f : JL (D.family side)) :
    D.cylinderInclusion side (D.cylinderProjection side f) = (1/2 : ℝ) • (f + D.flipJL side f) := by
  apply Subtype.ext
  ext p
  change average f.val p = (1/2 : ℝ) * (f.val p + flip f.val p)
  simp only [average_apply,flip_apply]
  ring

theorem EnumeratedConstruction.antisymmetricInclusion_projection (D : EnumeratedConstruction)
    (side : Bool) (f : JL (D.family side)) :
    D.antisymmetricInclusion side (D.antisymmetricProjection side f) =
      (1/2 : ℝ) • (f - D.flipJL side f) := by
  apply Subtype.ext
  ext p
  change antiAverage f.val p = (1/2 : ℝ) * (f.val p - flip f.val p)
  simp only [antiAverage_apply,flip_apply]
  ring

theorem EnumeratedConstruction.restrictedExtension_selected (D : EnumeratedConstruction) (side : Bool)
    (φ : FinalJLProduct D →L[ℝ] ℝ) :
    (D.extendCrossedFunctional side (φ.comp (D.crossedInjection side))).comp (D.sideInjection side) =
      (1/2 : ℝ) • ((φ.comp (D.sideInjection side)) -
        (φ.comp (D.sideInjection side)).comp (D.flipJL side)) := by
  apply ContinuousLinearMap.ext
  intro f
  change φ (D.crossedInjection side (D.crossedProjection side (D.sideInjection side f))) =
    (1/2 : ℝ) * (φ (D.sideInjection side f) - φ (D.sideInjection side (D.flipJL side f)))
  rw [D.crossedProjection_injection]
  change φ (D.sideInjection (!side) (D.cylinderInclusion (!side) 0) +
    D.sideInjection side (D.antisymmetricInclusion side (D.antisymmetricProjection side f))) = _
  rw [map_zero,map_zero,zero_add,D.antisymmetricInclusion_projection]
  simp only [map_smul,map_sub,smul_eq_mul]

theorem EnumeratedConstruction.restrictedExtension_other (D : EnumeratedConstruction) (side : Bool)
    (φ : FinalJLProduct D →L[ℝ] ℝ) :
    (D.extendCrossedFunctional side (φ.comp (D.crossedInjection side))).comp (D.sideInjection (!side)) =
      (1/2 : ℝ) • ((φ.comp (D.sideInjection (!side))) +
        (φ.comp (D.sideInjection (!side))).comp (D.flipJL (!side))) := by
  apply ContinuousLinearMap.ext
  intro f
  change φ (D.crossedInjection side (D.crossedProjection side (D.sideInjection (!side) f))) =
    (1/2 : ℝ) * (φ (D.sideInjection (!side) f) + φ (D.sideInjection (!side) (D.flipJL (!side) f)))
  rw [D.crossedProjection_injection_other]
  change φ (D.sideInjection (!side) (D.cylinderInclusion (!side) (D.cylinderProjection (!side) f)) +
    D.sideInjection side (D.antisymmetricInclusion side 0)) = _
  rw [map_zero,map_zero,add_zero,D.cylinderInclusion_projection]
  simp only [map_smul,map_add,smul_eq_mul]

theorem EnumeratedConstruction.restrictedCoefficients_selected (D : EnumeratedConstruction) (side : Bool)
    (φ : FinalJLProduct D →L[ℝ] ℝ) (p : IndexedAtom (ConstructionIndex × Bool)) :
    D.coefficients (D.extendCrossedFunctional side (φ.comp (D.crossedInjection side))) (side,p) =
      (1/2 : ℝ) * (D.coefficients φ (side,p) - D.coefficients φ (side,indexedAtomFlip p)) := by
  rw [D.coefficients_side,D.restrictedExtension_selected,map_smul,map_sub,D.indexedDual_flip]
  rw [D.coefficients_side,D.coefficients_side]
  rfl

theorem EnumeratedConstruction.restrictedCoefficients_other (D : EnumeratedConstruction) (side : Bool)
    (φ : FinalJLProduct D →L[ℝ] ℝ) (p : IndexedAtom (ConstructionIndex × Bool)) :
    D.coefficients (D.extendCrossedFunctional side (φ.comp (D.crossedInjection side))) (!side,p) =
      (1/2 : ℝ) * (D.coefficients φ (!side,p) + D.coefficients φ (!side,indexedAtomFlip p)) := by
  rw [D.coefficients_side,D.restrictedExtension_other,map_smul,map_add,D.indexedDual_flip]
  rw [D.coefficients_side,D.coefficients_side]
  rfl

theorem EnumeratedConstruction.extendedCoefficients_other_flip (D : EnumeratedConstruction) (side : Bool)
    (φ : FinalCandidate D side →L[ℝ] ℝ) (p : IndexedAtom (ConstructionIndex × Bool)) :
    D.coefficients (D.extendCrossedFunctional side φ) (!side,indexedAtomFlip p) =
      D.coefficients (D.extendCrossedFunctional side φ) (!side,p) := by
  rw [D.coefficients_side,D.coefficients_side]
  have h := D.indexedDual_flip (!side) ((D.extendCrossedFunctional side φ).comp (D.sideInjection (!side)))
  rw [D.extendCrossedFunctional_symmetric] at h
  exact (congrArg (fun c : lp (fun _ : IndexedAtom (ConstructionIndex × Bool) => ℝ) 1 => c p) h).symm

end SigmaNonprimarity

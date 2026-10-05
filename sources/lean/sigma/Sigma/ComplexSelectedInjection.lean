import Sigma.ComplexCrossedProjection

/-! An explicit right inverse to the projection onto each crossed summand. -/
noncomputable section
namespace SigmaNonprimarity
attribute [local instance] complexJLGroup complexJLSpace complexJLDualGroup complexJLDualSpace
attribute [local instance] complexPairedJLGroup complexPairedJLSpace complexPairedJLDualGroup
attribute [local instance] complexFinalCandidateGroup complexFinalCandidateSpace

def ComplexEnumeratedConstruction.cylinderInclusion (D : ComplexEnumeratedConstruction) (side : Bool) :
    ComplexCylinderJL (cylinderFamily (D.baseSets side)) →L[ℂ] ComplexJL (D.family side) :=
  (ComplexCylinderJL (cylinderFamily (D.baseSets side))).subtypeL.codRestrict _
    (fun f => complexCylinderJL_le_complexSplitJL _ _ (D.splits side) f.property)

def ComplexEnumeratedConstruction.antisymmetricInclusion (D : ComplexEnumeratedConstruction) (side : Bool) :
    complexAntisymmetricJL (D.family side) →L[ℂ] ComplexJL (D.family side) :=
  (complexAntisymmetricJL (D.family side)).subtypeL.codRestrict _ (fun f => f.property.1)

def ComplexEnumeratedConstruction.crossedInjection (D : ComplexEnumeratedConstruction) (side : Bool) :
    ComplexFinalCandidate D side →L[ℂ] ComplexFinalJLProduct D :=
  ((D.sideInjection (!side)).comp (D.cylinderInclusion (!side))).comp (ContinuousLinearMap.fst ℂ _ _) +
    ((D.sideInjection side).comp (D.antisymmetricInclusion side)).comp (ContinuousLinearMap.snd ℂ _ _)

theorem ComplexEnumeratedConstruction.crossedProjection_injection_other (D : ComplexEnumeratedConstruction)
    (side : Bool) (f : ComplexJL (D.family (!side))) :
    D.crossedProjection side (D.sideInjection (!side) f) = (D.cylinderProjection (!side) f,0) := by
  change (D.cylinderProjection (!side) (D.sideProjection (!side) (D.sideInjection (!side) f)),
    D.antisymmetricProjection side (D.sideProjection side (D.sideInjection (!side) f))) = _
  rw [D.sideProjection_injection]
  have h : D.sideProjection side (D.sideInjection (!side) f) = 0 := by cases side <;> rfl
  rw [h,map_zero]

theorem ComplexEnumeratedConstruction.crossedProjection_rightInverse (D : ComplexEnumeratedConstruction) (side : Bool)
    (f : ComplexFinalCandidate D side) : D.crossedProjection side (D.crossedInjection side f) = f := by
  change D.crossedProjection side
    (D.sideInjection (!side) (D.cylinderInclusion (!side) f.1) +
      D.sideInjection side (D.antisymmetricInclusion side f.2)) = _
  rw [map_add,D.crossedProjection_injection,D.crossedProjection_injection_other]
  apply Prod.ext <;> apply Subtype.ext
  · change complexAverage f.1.val + 0 = f.1.val
    rw [complexAverage_eq_self_of_mem_complexCylinderJL (D.baseSets (!side)) f.1.property,add_zero]
  · change 0 + (f.2.val - complexAverage f.2.val) = f.2.val
    rw [show complexAverage f.2.val = 0 from f.2.property.2,sub_zero,zero_add]

theorem ComplexEnumeratedConstruction.crossedProjection_surjective (D : ComplexEnumeratedConstruction) (side : Bool) :
    Function.Surjective (D.crossedProjection side) :=
  fun f => ⟨D.crossedInjection side f,D.crossedProjection_rightInverse side f⟩

end SigmaNonprimarity



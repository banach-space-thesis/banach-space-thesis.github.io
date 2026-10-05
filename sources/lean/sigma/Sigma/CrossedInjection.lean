import Sigma.CrossedCoefficients

/-! An explicit right inverse to the projection onto each crossed summand. -/
noncomputable section
namespace SigmaNonprimarity
attribute [local instance] bridgeRealSpace bridgeJLGroup bridgeJLSpace jlDualGroup jlDualSpace
attribute [local instance] pairedJLGroup pairedJLSpace pairedJLDualGroup
attribute [local instance] finalCandidateGroup finalCandidateSpace

def EnumeratedConstruction.cylinderInclusion (D : EnumeratedConstruction) (side : Bool) :
    CylinderJL (cylinderFamily (D.baseSets side)) →L[ℝ] JL (D.family side) :=
  (CylinderJL (cylinderFamily (D.baseSets side))).subtypeL.codRestrict _
    (fun f => cylinderJL_le_splitJL _ _ (D.splits side) f.property)

def EnumeratedConstruction.antisymmetricInclusion (D : EnumeratedConstruction) (side : Bool) :
    antisymmetricJL (D.family side) →L[ℝ] JL (D.family side) :=
  (antisymmetricJL (D.family side)).subtypeL.codRestrict _ (fun f => f.property.1)

def EnumeratedConstruction.crossedInjection (D : EnumeratedConstruction) (side : Bool) :
    FinalCandidate D side →L[ℝ] FinalJLProduct D :=
  ((D.sideInjection (!side)).comp (D.cylinderInclusion (!side))).comp (ContinuousLinearMap.fst ℝ _ _) +
    ((D.sideInjection side).comp (D.antisymmetricInclusion side)).comp (ContinuousLinearMap.snd ℝ _ _)

theorem EnumeratedConstruction.crossedProjection_injection_other (D : EnumeratedConstruction)
    (side : Bool) (f : JL (D.family (!side))) :
    D.crossedProjection side (D.sideInjection (!side) f) = (D.cylinderProjection (!side) f,0) := by
  change (D.cylinderProjection (!side) (D.sideProjection (!side) (D.sideInjection (!side) f)),
    D.antisymmetricProjection side (D.sideProjection side (D.sideInjection (!side) f))) = _
  rw [D.sideProjection_injection]
  have h : D.sideProjection side (D.sideInjection (!side) f) = 0 := by cases side <;> rfl
  rw [h,map_zero]

theorem EnumeratedConstruction.crossedProjection_rightInverse (D : EnumeratedConstruction) (side : Bool)
    (f : FinalCandidate D side) : D.crossedProjection side (D.crossedInjection side f) = f := by
  change D.crossedProjection side
    (D.sideInjection (!side) (D.cylinderInclusion (!side) f.1) +
      D.sideInjection side (D.antisymmetricInclusion side f.2)) = _
  rw [map_add,D.crossedProjection_injection,D.crossedProjection_injection_other]
  apply Prod.ext <;> apply Subtype.ext
  · change average f.1.val + 0 = f.1.val
    rw [average_eq_self_of_mem_cylinderJL (D.baseSets (!side)) f.1.property,add_zero]
  · change 0 + (f.2.val - average f.2.val) = f.2.val
    rw [show average f.2.val = 0 from f.2.property.2,sub_zero,zero_add]

theorem EnumeratedConstruction.crossedProjection_surjective (D : EnumeratedConstruction) (side : Bool) :
    Function.Surjective (D.crossedProjection side) :=
  fun f => ⟨D.crossedInjection side f,D.crossedProjection_rightInverse side f⟩

end SigmaNonprimarity

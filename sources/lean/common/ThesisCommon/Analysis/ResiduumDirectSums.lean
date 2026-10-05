import ThesisCommon.Analysis.QuasiReflexiveDefinitions
import ThesisCommon.Analysis.ResiduumProperties

/-! The actual bidual quotient functor preserves Banach-space isomorphisms
and finite complemented direct sums. -/
noncomputable section
set_option synthInstance.maxSize 1024
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000
namespace ThesisCommon
variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

omit [CompleteSpace E] [CompleteSpace F] in
theorem residuumOperator_comp_apply (S : E →L[𝕜] F)
    {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    (T : G →L[𝕜] E) (x : ResiduumSpace 𝕜 G) :
    residuumOperator (S.comp T) x = residuumOperator S (residuumOperator T x) := by
  rw [residuumOperator_comp]
  rfl

/-- An isomorphism acts on the genuine bidual quotients, with its inverse
induced by the inverse isomorphism. -/
def residuumEquiv (e : E ≃L[𝕜] F) :
    ResiduumSpace 𝕜 E ≃L[𝕜] ResiduumSpace 𝕜 F := by
  refine ContinuousLinearEquiv.equivOfInverse (residuumOperator e.toContinuousLinearMap)
    (residuumOperator e.symm.toContinuousLinearMap) ?_ ?_
  · intro x
    rw [← residuumOperator_comp_apply]
    have h : e.symm.toContinuousLinearMap.comp e.toContinuousLinearMap =
        ContinuousLinearMap.id 𝕜 E := by ext x; exact e.symm_apply_apply x
    rw [h, residuumOperator_id]
    rfl
  · intro x
    rw [← residuumOperator_comp_apply]
    have h : e.toContinuousLinearMap.comp e.symm.toContinuousLinearMap =
        ContinuousLinearMap.id 𝕜 F := by ext x; exact e.apply_symm_apply x
    rw [h, residuumOperator_id]
    rfl

set_option maxHeartbeats 2000000 in
/-- The quotient of the bidual of a product by its canonical image is the
product of the two actual bidual quotients. -/
def residuumProductEquiv :
    ResiduumSpace 𝕜 (E × F) ≃L[𝕜] (ResiduumSpace 𝕜 E × ResiduumSpace 𝕜 F) := by
  let a := ContinuousLinearMap.fst 𝕜 E F
  let b := ContinuousLinearMap.snd 𝕜 E F
  let c := ContinuousLinearMap.inl 𝕜 E F
  let d := ContinuousLinearMap.inr 𝕜 E F
  have hac : a.comp c = ContinuousLinearMap.id 𝕜 E := by ext x; rfl
  have had : a.comp d = 0 := by ext x; rfl
  have hbc : b.comp c = 0 := by ext x; rfl
  have hbd : b.comp d = ContinuousLinearMap.id 𝕜 F := by ext x; rfl
  have hsum : c.comp a + d.comp b = ContinuousLinearMap.id 𝕜 (E × F) := by
    ext x <;> simp [a, b, c, d]
  refine ContinuousLinearEquiv.equivOfInverse
    ((residuumOperator a).prod (residuumOperator b))
    ((residuumOperator c).coprod (residuumOperator d)) ?_ ?_
  · intro x
    change residuumOperator c (residuumOperator a x) +
      residuumOperator d (residuumOperator b x) = x
    rw [← residuumOperator_comp_apply, ← residuumOperator_comp_apply,
      ← ContinuousLinearMap.add_apply, ← residuumOperator_add, hsum, residuumOperator_id]
    rfl
  · intro x
    apply Prod.ext
    · change residuumOperator a (residuumOperator c x.1 + residuumOperator d x.2) = x.1
      rw [map_add, ← residuumOperator_comp_apply, ← residuumOperator_comp_apply,
        hac, had, residuumOperator_id, residuumOperator_zero]
      simp
    · change residuumOperator b (residuumOperator c x.1 + residuumOperator d x.2) = x.2
      rw [map_add, ← residuumOperator_comp_apply, ← residuumOperator_comp_apply,
        hbc, hbd, residuumOperator_id, residuumOperator_zero]
      simp

/-- Closed complementary subspaces induce an actual continuous linear
equivalence between the corresponding bidual quotients. -/
def residuumComplementedEquiv (Y Z : Submodule 𝕜 E)
    (hY : IsClosed (Y : Set E)) (hZ : IsClosed (Z : Set E)) (h : IsCompl Y Z) :
    letI : CompleteSpace Y := hY.completeSpace_coe
    letI : CompleteSpace Z := hZ.completeSpace_coe
    ResiduumSpace 𝕜 E ≃L[𝕜] (ResiduumSpace 𝕜 Y × ResiduumSpace 𝕜 Z) := by
  letI : CompleteSpace Y := hY.completeSpace_coe
  letI : CompleteSpace Z := hZ.completeSpace_coe
  exact (residuumEquiv (Y.prodEquivOfClosedCompl Z h hY hZ).symm).trans
    (residuumProductEquiv (𝕜 := 𝕜) (E := Y) (F := Z))

end ThesisCommon

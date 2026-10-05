import ThesisCommon.Residuum

/-! Concrete dual isomorphisms by precomposition and restriction to product
coordinates. These work over both real and complex scalars. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

def banachDualEquiv (e : E ≃L[𝕜] F) : StrongDual 𝕜 E ≃L[𝕜] StrongDual 𝕜 F := by
  refine ContinuousLinearEquiv.equivOfInverse
    (banachAdjoint e.symm.toContinuousLinearMap)
    (banachAdjoint e.toContinuousLinearMap) ?_ ?_
  · intro f
    apply ContinuousLinearMap.ext
    intro x
    change f (e.symm (e x)) = f x
    rw [e.symm_apply_apply]
  · intro f
    apply ContinuousLinearMap.ext
    intro x
    change f (e (e.symm x)) = f x
    rw [e.apply_symm_apply]

@[simp] theorem banachDualEquiv_apply (e : E ≃L[𝕜] F) (f : StrongDual 𝕜 E) (y : F) :
    banachDualEquiv e f y = f (e.symm y) := rfl

def banachDualProductEquiv :
    StrongDual 𝕜 (E × F) ≃L[𝕜] (StrongDual 𝕜 E × StrongDual 𝕜 F) := by
  refine ContinuousLinearEquiv.equivOfInverse
    ((banachAdjoint (ContinuousLinearMap.inl 𝕜 E F)).prod
      (banachAdjoint (ContinuousLinearMap.inr 𝕜 E F)))
    ((banachAdjoint (ContinuousLinearMap.fst 𝕜 E F)).coprod
      (banachAdjoint (ContinuousLinearMap.snd 𝕜 E F))) ?_ ?_
  · intro f
    apply ContinuousLinearMap.ext
    intro x
    change f (x.1, 0) + f (0, x.2) = f x
    rw [← map_add]
    congr 1
    exact Prod.ext (add_zero _) (zero_add _)
  · intro f
    apply Prod.ext <;> ext x
    · change f.1 x + f.2 0 = f.1 x
      rw [map_zero, add_zero]
    · change f.1 0 + f.2 x = f.2 x
      rw [map_zero, zero_add]

end ThesisCommon

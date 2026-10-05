import ThesisCommon.Analysis.HyperplaneIsomorphisms

/-! Appendix B.1: scalar absorption passes from an actual complemented
subspace to the whole space, then gives isomorphism with every hyperplane.
-/
noncomputable section
namespace ThesisCommon
variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- Reassociate an actual complemented decomposition and absorb its scalar
coordinate inside the complemented summand. -/
theorem scalarExtension_of_complemented_subspace (E : Submodule 𝕜 X)
    (hE : E.ClosedComplemented) (he : IsIsomorphicToScalarExtension 𝕜 E) :
    IsIsomorphicToScalarExtension 𝕜 X := by
  obtain ⟨F, e, _⟩ := hE.exists_submodule_equiv_prod
  obtain ⟨a⟩ := he
  let r : ((E × 𝕜) × F) ≃L[𝕜] ((E × F) × 𝕜) :=
    (ContinuousLinearEquiv.prodAssoc 𝕜 E 𝕜 F).trans
      (((ContinuousLinearEquiv.refl 𝕜 E).prodCongr
        (ContinuousLinearEquiv.prodComm 𝕜 𝕜 F)).trans
          (ContinuousLinearEquiv.prodAssoc 𝕜 E F 𝕜).symm)
  exact ⟨e.trans ((a.prodCongr (ContinuousLinearEquiv.refl 𝕜 F)).trans
    (r.trans (e.symm.prodCongr (ContinuousLinearEquiv.refl 𝕜 𝕜))))⟩

/-- The functional detecting the added scalar coordinate of X ≃ X × 𝕜. -/
def scalarExtensionFunctional (e : X ≃L[𝕜] (X × 𝕜)) : X →L[𝕜] 𝕜 :=
  (ContinuousLinearMap.snd 𝕜 X 𝕜).comp e.toContinuousLinearMap

theorem scalarExtensionFunctional_ne_zero (e : X ≃L[𝕜] (X × 𝕜)) :
    scalarExtensionFunctional e ≠ 0 := by
  intro hf
  have hh := congrArg (fun f : X →L[𝕜] 𝕜 => f (e.symm (0, 1))) hf
  have he : scalarExtensionFunctional e (e.symm (0, 1)) = 1 := by
    change (e (e.symm (0, 1))).2 = 1
    rw [e.apply_symm_apply]
  change scalarExtensionFunctional e (e.symm (0, 1)) = 0 at hh
  rw [he] at hh
  simp at hh

/-- X identifies with the kernel of its added scalar coordinate. -/
def scalarExtensionKernelEquiv (e : X ≃L[𝕜] (X × 𝕜)) :
    X ≃L[𝕜] LinearMap.ker (scalarExtensionFunctional e).toLinearMap := by
  let J : X →L[𝕜] X := e.symm.toContinuousLinearMap.comp (ContinuousLinearMap.inl 𝕜 X 𝕜)
  let A : X →L[𝕜] X := (ContinuousLinearMap.fst 𝕜 X 𝕜).comp e.toContinuousLinearMap
  let V : X →L[𝕜] LinearMap.ker (scalarExtensionFunctional e).toLinearMap :=
    J.codRestrict _ (by
      intro x
      change (e (e.symm (x, 0))).2 = 0
      rw [e.apply_symm_apply])
  let U := A.comp (LinearMap.ker (scalarExtensionFunctional e).toLinearMap).subtypeL
  refine ContinuousLinearEquiv.equivOfInverse V U ?_ ?_
  · intro x
    change (e (e.symm (x, 0))).1 = x
    rw [e.apply_symm_apply]
  · intro y
    apply Subtype.ext
    apply e.injective
    change e (e.symm ((e y).1, 0)) = e y
    rw [e.apply_symm_apply]
    apply Prod.ext
    · rfl
    · exact y.property.symm

/-- Absorbing one scalar dimension gives isomorphism with every closed
hyperplane via the explicit common-transverse-vector construction. -/
theorem IsIsomorphicToScalarExtension.everyHyperplane
    (h : IsIsomorphicToScalarExtension 𝕜 X) : IsIsomorphicToEveryHyperplane 𝕜 X := by
  obtain ⟨e⟩ := h
  intro H hH
  obtain ⟨f, hf, hker⟩ := hH.exists_functional
  obtain ⟨a⟩ := nonempty_scalarKernelEquiv (scalarExtensionFunctional e) f
    (scalarExtensionFunctional_ne_zero e) hf
  rw [← hker]
  exact ⟨(scalarExtensionKernelEquiv e).trans a⟩

end ThesisCommon

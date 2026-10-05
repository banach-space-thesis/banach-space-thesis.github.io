import JLMS.ComplementedCopyIdeal

/-!
# Ogden Lemma 6.15 for bounded operators

If Q is a bounded projection whose range is isomorphic to the whole Banach
space, then I - Q is in the continuity ideal of every algebra homomorphism.
The argument only needs boundedness of Q, so no norm-one assumption is needed.
-/

noncomputable section
namespace JLMS
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
variable {A : Type*} [NonUnitalNormedRing A] [NormedSpace 𝕜 A]

theorem ogden_projectionComplement_mem_continuityIdeal
    (θ : (E →L[𝕜] E) →ₙₐ[𝕜] A) (Q : E →L[𝕜] E)
    (hQ : Q.comp Q = Q) (e : E ≃L[𝕜] LinearMap.range Q) :
    1 - Q ∈ continuityIdeal θ := by
  let u : E →L[𝕜] E := (LinearMap.range Q).subtypeL.comp e.toContinuousLinearMap
  let v : E →L[𝕜] E := e.symm.toContinuousLinearMap.comp Q.rangeRestrict
  have hfix (z : LinearMap.range Q) : Q z.val = z.val := by
    obtain ⟨y, hy⟩ := z.property
    rw [← hy]
    exact congrArg (fun R : E →L[𝕜] E => R y) hQ
  have hvu : v * u = 1 := by
    ext x
    change e.symm (Q.rangeRestrict (e x).val) = x
    have hh : Q.rangeRestrict (e x).val = e x := Subtype.ext (hfix (e x))
    rw [hh, e.symm_apply_apply]
  have huv : u * v = Q := by
    ext x
    change (e (e.symm (Q.rangeRestrict x))).val = Q x
    simp
  simpa only [huv] using complement_mem_continuityIdeal_of_retraction θ u v hvu

end JLMS

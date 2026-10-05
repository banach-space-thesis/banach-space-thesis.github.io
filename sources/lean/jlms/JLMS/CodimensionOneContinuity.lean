import JLMS.Definitions

/-!
# Extending continuity from the kernel of one bounded functional

The final step of Ogden Theorem 6.18 splits an operator into an element of
the closed codimension-one ideal and a scalar multiple of the identity.
This reusable linear lemma proves that step using the actual kernel and
an explicit bounded projection, with no finite-codimension continuity input.
-/

noncomputable section
namespace JLMS
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem continuous_of_continuous_on_codimensionOne_kernel
    (f : E →ₗ[𝕜] F) (χ : E →L[𝕜] 𝕜) (e : E) (he : χ e = 1)
    (hf : Continuous (f.comp (LinearMap.ker χ).subtype)) : Continuous f := by
  let R : E →L[𝕜] LinearMap.ker χ :=
    (ContinuousLinearMap.id 𝕜 E - χ.smulRight e).codRestrict (LinearMap.ker χ)
      (fun x => by simp [LinearMap.mem_ker, he])
  have h₁ := hf.comp R.continuous
  have h₂ : Continuous (fun x : E => χ x • f e) := χ.continuous.smul continuous_const
  convert h₁.add h₂ using 1
  funext x
  change f x = f (x - χ x • e) + χ x • f e
  simp

end JLMS

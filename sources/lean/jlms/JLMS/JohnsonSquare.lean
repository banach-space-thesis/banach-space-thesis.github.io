import JLMS.OrthogonalAutomaticContinuity
import Mathlib.Topology.Algebra.Module.LinearMapPiProd

/-!
# Johnson's theorem for a Banach space isomorphic to its square

The two coordinate embeddings and projections of a square decomposition
satisfy the two-copy relations. The preceding diagonal argument then proves
continuity of every algebra homomorphism into any normed algebra.
-/

noncomputable section
namespace JLMS
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
variable {A : Type*} [NonUnitalNormedRing A] [NormedSpace 𝕜 A]

theorem johnson_automaticContinuity_of_square (e : E ≃L[𝕜] E × E)
    (φ : (E →L[𝕜] E) →ₙₐ[𝕜] A) : Continuous φ := by
  let u₀ := e.symm.toContinuousLinearMap.comp (ContinuousLinearMap.inl 𝕜 E E)
  let u₁ := e.symm.toContinuousLinearMap.comp (ContinuousLinearMap.inr 𝕜 E E)
  let v₀ := (ContinuousLinearMap.fst 𝕜 E E).comp e.toContinuousLinearMap
  let v₁ := (ContinuousLinearMap.snd 𝕜 E E).comp e.toContinuousLinearMap
  apply continuous_hom_of_twoCopies φ u₀ u₁ v₀ v₁
  all_goals
    ext x
    simp [u₀, u₁, v₀, v₁, ContinuousLinearMap.mul_apply]

end JLMS

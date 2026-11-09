import NonCalkinAlgebra.DiagonalCorner
import NonCalkinAlgebra.Statements

noncomputable section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
namespace NonCalkinAlgebra
universe u

theorem density_lower_bound_of_surjective
    {E F : Type u} [TopologicalSpace E] [TopologicalSpace F]
    {κ : Cardinal.{u}} (hF : HasDensityCharacter F κ)
    (f : E → F) (hf : Continuous f) (hsurj : Function.Surjective f)
    (S : Set E) (hS : Dense S) : κ ≤ Cardinal.mk S := by
  have hdense : Dense (f '' S) := hsurj.denseRange.dense_image hf hS
  exact (hF.2 (f '' S) hdense).trans Cardinal.mk_image_le

variable (D : Type u) [NormedRing D] [NormedAlgebra ℂ D] [NormOneClass D]

def coefficientProjection : matrixAlgebra D →L[ℂ] D :=
  (matrixEntry D 0 0).comp (matrixAlgebra D).toSubmodule.subtypeL

theorem coefficientProjection_surjective : Function.Surjective (coefficientProjection D) := by
  intro d
  refine ⟨matrixTheta D 0 0 d, ?_⟩
  change matrixEntry D 0 0 (theta D 0 0 d) = d
  simp only [matrixEntry_theta, and_self, if_true]

/-- The lower density bound in the proof of Theorem 1.1; no loss from the
operator realisation or passage to the diagonal corner. -/
theorem matrixAlgebra_density_lower_bound {κ : Cardinal.{u}}
    (hD : HasDensityCharacter D κ) (S : Set (matrixAlgebra D)) (hS : Dense S) :
    κ ≤ Cardinal.mk S :=
  density_lower_bound_of_surjective hD (coefficientProjection D)
    (coefficientProjection D).continuous (coefficientProjection_surjective D) S hS

end NonCalkinAlgebra

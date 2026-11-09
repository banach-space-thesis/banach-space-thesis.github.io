import NonCalkinAlgebra.ConstructedBanachAlgebra
import NonCalkinAlgebra.DiagonalCorner

noncomputable section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
namespace NonCalkinAlgebra
universe u v

/-- An explicit bounded algebra isomorphism with the actual corner pAp.
The corner has the inherited norm and identity p. The two continuous linear
maps are mutual inverses on the corner, so no alternative topology is used.
-/
structure CornerModel (D : Type u) (A : Type v)
    [NormedRing D] [NormedAlgebra ℂ D] [NormedRing A] [NormedAlgebra ℂ A] (p : A) where
  inclusion : D →L[ℂ] A
  projection : A →L[ℂ] D
  inclusion_mul : ∀ d e : D, inclusion (d * e) = inclusion d * inclusion e
  inclusion_one : inclusion 1 = p
  projection_inclusion : ∀ d : D, projection (inclusion d) = d
  inclusion_projection : ∀ a : A, inclusion (projection a) = p * a * p

namespace CornerModel
variable {D : Type u} {A : Type v}
  [NormedRing D] [NormedAlgebra ℂ D] [NormedRing A] [NormedAlgebra ℂ A]
  {p : A} (M : CornerModel D A p)

theorem inclusion_injective : Function.Injective M.inclusion :=
  Function.LeftInverse.injective M.projection_inclusion

theorem inclusion_fixed (d : D) : p * M.inclusion d * p = M.inclusion d := by
  have hleft : p * M.inclusion d = M.inclusion d := by
    simpa only [M.inclusion_one, one_mul] using (M.inclusion_mul 1 d).symm
  have hright : M.inclusion d * p = M.inclusion d := by
    simpa only [M.inclusion_one, mul_one] using (M.inclusion_mul d 1).symm
  exact (congrArg (fun a : A => a * p) hleft).trans hright

include M in
theorem idempotent : p * p = p := by
  simpa only [M.inclusion_one, one_mul] using (M.inclusion_mul 1 1).symm

/-- The model's range is precisely the literal corner, not a larger subspace. -/
theorem range_iff (a : A) : (∃ d : D, M.inclusion d = a) ↔ p * a * p = a := by
  constructor
  · rintro ⟨d, rfl⟩
    exact M.inclusion_fixed d
  · intro ha
    exact ⟨M.projection a, (M.inclusion_projection a).trans ha⟩

end CornerModel

variable (D : Type u) [NormedRing D] [NormedAlgebra ℂ D] [NormOneClass D]

/-- The explicit corner isomorphism in Proposition 5.1, with its inverse
given by taking the (i,i) coefficient. -/
def matrixCornerModel (i : ℕ) :
    CornerModel D (matrixAlgebra D) (canonicalMatrixUnit D i i) where
  inclusion := matrixThetaMap D i i
  projection := (matrixEntry D i i).comp (matrixAlgebra D).toSubmodule.subtypeL
  inclusion_mul d e := by
    simp only [matrixThetaMap_apply, matrixTheta_mul, if_true]
  inclusion_one := rfl
  projection_inclusion d := by
    change matrixEntry D i i (theta D i i d) = d
    simp [matrixEntry_theta]
  inclusion_projection a := by
    apply Subtype.ext
    exact (diagonal_matrixAlgebra_corner_formula D a.property i).symm

theorem matrixCornerModel_isometric (i : ℕ) (d : D) :
    ‖(matrixCornerModel D i).inclusion d‖ = ‖d‖ := norm_theta D i i d

end NonCalkinAlgebra

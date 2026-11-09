import NonCalkinAlgebra.CornerModel
import Mathlib.Topology.Algebra.Algebra.Equiv

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace NonCalkinAlgebra
universe u v w z

def continuousAlgEquivToLinear {A : Type u} {B : Type v}
    [NormedRing A] [NormedAlgebra ℂ A] [NormedRing B] [NormedAlgebra ℂ B]
    (e : A ≃A[ℂ] B) : A ≃L[ℂ] B :=
  { e.toAlgEquiv.toLinearEquiv with
    continuous_toFun := e.continuous
    continuous_invFun := e.symm.continuous }

namespace CornerModel
variable {D : Type u} {A : Type v}
  [NormedRing D] [NormedAlgebra ℂ D] [NormedRing A] [NormedAlgebra ℂ A]
  {p : A} (M : CornerModel D A p)

include M

theorem projection_compression (a : A) : M.projection (p * a * p) = M.projection a := by
  simpa only [M.inclusion_projection] using M.projection_inclusion (M.projection a)

theorem left_fixed_of_fixed {a : A} (ha : p * a * p = a) : p * a = a := by
  calc
    p * a = p * (p * a * p) := congrArg (fun x : A => p * x) ha.symm
    _ = p * a * p := by simp only [← mul_assoc, M.idempotent]
    _ = a := ha

theorem right_fixed_of_fixed {a : A} (ha : p * a * p = a) : a * p = a := by
  calc
    a * p = (p * a * p) * p := congrArg (fun x : A => x * p) ha.symm
    _ = p * a * p := by simp only [mul_assoc, M.idempotent]
    _ = a := ha

theorem projection_mul_of_fixed {a b : A}
    (ha : p * a * p = a) (hb : p * b * p = b) :
    M.projection (a * b) = M.projection a * M.projection b := by
  apply M.inclusion_injective
  calc
    M.inclusion (M.projection (a * b)) = p * (a * b) * p := M.inclusion_projection _
    _ = (p * a) * (b * p) := by simp only [mul_assoc]
    _ = a * b := by rw [M.left_fixed_of_fixed ha, M.right_fixed_of_fixed hb]
    _ = M.inclusion (M.projection a) * M.inclusion (M.projection b) := by
      rw [M.inclusion_projection, M.inclusion_projection, ha, hb]
    _ = M.inclusion (M.projection a * M.projection b) := (M.inclusion_mul _ _).symm

variable {E : Type w} {B : Type z}
  [NormedRing E] [NormedAlgebra ℂ E] [NormedRing B] [NormedAlgebra ℂ B]
  {q : B} (N : CornerModel E B q)

include N

def transferForward (e : A ≃A[ℂ] B) : D →L[ℂ] E :=
  N.projection.comp ((continuousAlgEquivToLinear e).toContinuousLinearMap.comp M.inclusion)

def transferBackward (e : A ≃A[ℂ] B) : E →L[ℂ] D :=
  M.projection.comp ((continuousAlgEquivToLinear e.symm).toContinuousLinearMap.comp N.inclusion)

theorem transferForward_fixed (e : A ≃A[ℂ] B) (hep : e p = q) (d : D) :
    q * e (M.inclusion d) * q = e (M.inclusion d) := by
  calc
    q * e (M.inclusion d) * q = e (p * M.inclusion d * p) := by
      rw [map_mul e, map_mul e, hep]
    _ = e (M.inclusion d) := congrArg e (M.inclusion_fixed d)

theorem transfer_left_inverse (e : A ≃A[ℂ] B) (hep : e p = q) (d : D) :
    M.transferBackward N e (M.transferForward N e d) = d := by
  have heq : e.symm q = p := by simpa only [hep] using e.symm_apply_apply p
  change M.projection (e.symm (N.inclusion (N.projection (e (M.inclusion d))))) = d
  rw [N.inclusion_projection, map_mul e.symm, map_mul e.symm, heq,
    e.symm_apply_apply, M.inclusion_fixed, M.projection_inclusion]

theorem transfer_right_inverse (e : A ≃A[ℂ] B) (hep : e p = q) (d : E) :
    M.transferForward N e (M.transferBackward N e d) = d := by
  change N.projection (e (M.inclusion (M.projection (e.symm (N.inclusion d))))) = d
  rw [M.inclusion_projection, map_mul e, map_mul e, hep,
    e.apply_symm_apply, N.inclusion_fixed, N.projection_inclusion]

def transferLinearEquiv (e : A ≃A[ℂ] B) (hep : e p = q) : D ≃L[ℂ] E where
  toFun := M.transferForward N e
  invFun := M.transferBackward N e
  map_add' := (M.transferForward N e).map_add
  map_smul' := (M.transferForward N e).map_smul
  left_inv := M.transfer_left_inverse N e hep
  right_inv := M.transfer_right_inverse N e hep
  continuous_toFun := (M.transferForward N e).continuous
  continuous_invFun := (M.transferBackward N e).continuous

/-- Bounded algebra isomorphisms carry corners to corners, with bounded
inverse and the actual inherited norms. -/
def transfer (e : A ≃A[ℂ] B) (hep : e p = q) : D ≃A[ℂ] E where
  toAlgEquiv := AlgEquiv.ofLinearEquiv (M.transferLinearEquiv N e hep).toLinearEquiv
    (by
      change N.projection (e (M.inclusion 1)) = 1
      rw [M.inclusion_one, hep]
      simpa only [N.inclusion_one] using N.projection_inclusion 1)
    (by
      intro a b
      change N.projection (e (M.inclusion (a * b))) =
        N.projection (e (M.inclusion a)) * N.projection (e (M.inclusion b))
      rw [M.inclusion_mul, map_mul e]
      exact N.projection_mul_of_fixed (M.transferForward_fixed N e hep a)
        (M.transferForward_fixed N e hep b))
  continuous_toFun := (M.transferForward N e).continuous
  continuous_invFun := (M.transferBackward N e).continuous

end CornerModel
end NonCalkinAlgebra

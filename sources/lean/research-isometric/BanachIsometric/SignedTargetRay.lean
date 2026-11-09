import BanachIsometric.SignedRayBlockDerivative

/-! The target chart sends radius-and-tail coordinates to a positive multiple
of `(1, y)`. Its Jacobian determinant is positive for a positive radius. -/

noncomputable section
namespace BanachIsometric.SingularPrism

open Matrix

def signedTargetRay (n : ℕ) (u : Fin (n + 1) → ℝ) : Fin (n + 1) → ℝ :=
  u 0 • Fin.cons (α := fun _ => ℝ) 1 (signedTailLinear n u)

def signedTargetRayDerivative (n : ℕ) (u : Fin (n + 1) → ℝ) :
    (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) :=
  u 0 • signedRayJoin n 0 (signedTailLinear n).toContinuousLinearMap +
    (signedRayHead n).smulRight (Fin.cons (1 : ℝ) (signedTailLinear n u))

theorem signedTargetRay_hasFDerivAt (n : ℕ) (u : Fin (n + 1) → ℝ) :
    HasFDerivAt (signedTargetRay n) (signedTargetRayDerivative n u) u := by
  have hcoord : HasFDerivAt (fun z => Fin.cons (1 : ℝ) (signedTailLinear n z))
      (signedRayJoin n 0 (signedTailLinear n).toContinuousLinearMap) u :=
    HasFDerivAt.signedRayJoin (hasFDerivAt_const _ _)
      (signedTailLinear n).toContinuousLinearMap.hasFDerivAt
  exact (signedRayHead n).hasFDerivAt.smul hcoord

theorem signedTargetRayDerivative_det (n : ℕ) (u : Fin (n + 1) → ℝ) :
    (signedTargetRayDerivative n u).det = (u 0) ^ n := by
  let A := signedTargetRayDerivative n u
  let M := LinearMap.toMatrix' A.toLinearMap
  change A.toLinearMap.det = _
  rw [← LinearMap.det_toMatrix' A.toLinearMap]
  change M.det = _
  have hhead : M 0 0 = 1 := by
    change A (Pi.single (0 : Fin (n + 1)) 1) 0 = 1
    simp [A, signedTargetRayDerivative, signedRayHead]
  have hzero (j : Fin n) : M 0 j.succ = 0 := by
    change A (Pi.single j.succ 1) 0 = 0
    simp [A, signedTargetRayDerivative, signedRayHead]
  have hminor : M.submatrix Fin.succ Fin.succ = Matrix.diagonal (fun _ : Fin n => u 0) := by
    ext i j
    change A (Pi.single j.succ 1) i.succ = Matrix.diagonal (fun _ : Fin n => u 0) i j
    simp [A, signedTargetRayDerivative, signedRayHead, signedTailLinear_single_succ,
      Matrix.diagonal_apply, Pi.single_apply, eq_comm]
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  simp [hhead, hzero, hminor]

end BanachIsometric.SingularPrism

import BanachIsometric.SignedSimplexFaceGeometry
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Algebra.Module.Determinant

/-! The actual local ray chart has the oriented facet determinant multiplied
by the positive radial factor to the power of the face dimension. -/

noncomputable section
namespace BanachIsometric.SingularPrism

open Matrix

def signedRayHead (n : ℕ) : (Fin (n + 1) → ℝ) →L[ℝ] ℝ :=
  (LinearMap.proj (R := ℝ) (0 : Fin (n + 1))).toContinuousLinearMap

def signedFacetRay (n : ℕ) (i : Fin (n + 2)) (u : Fin (n + 1) → ℝ) : Fin (n + 1) → ℝ :=
  u 0 • signedFacetVector n i (signedTailLinear n u)

def signedFacetRayDerivative (n : ℕ) (i : Fin (n + 2)) (u : Fin (n + 1) → ℝ) :
    (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) :=
  u 0 • ((signedFacetSlope n i).comp (signedTailLinear n).toContinuousLinearMap) +
    (signedRayHead n).smulRight (signedFacetVector n i (signedTailLinear n u))

theorem signedFacetRay_hasFDerivAt (n : ℕ) (i : Fin (n + 2)) (u : Fin (n + 1) → ℝ) :
    HasFDerivAt (signedFacetRay n i) (signedFacetRayDerivative n i u) u := by
  exact (signedRayHead n).hasFDerivAt.smul
    ((signedFacetVector_hasFDerivAt n i (signedTailLinear n u)).comp u
      ((signedTailLinear n).toContinuousLinearMap.hasFDerivAt))

theorem signedFacetRay_contDiff (n : ℕ) (i : Fin (n + 2)) : ContDiff ℝ 1 (signedFacetRay n i) := by
  have heq : signedFacetVector n i = fun x => signedFacetVector n i 0 + signedFacetSlope n i x :=
    funext (signedFacetVector_affine n i)
  have hv : ContDiff ℝ 1 (signedFacetVector n i) := by
    rw [heq]
    exact contDiff_const.add (signedFacetSlope n i).contDiff
  exact (signedRayHead n).contDiff.smul (hv.comp (signedTailLinear n).toContinuousLinearMap.contDiff)

theorem signedFacetRay_hasStrictFDerivAt (n : ℕ) (i : Fin (n + 2)) (u : Fin (n + 1) → ℝ) :
    HasStrictFDerivAt (signedFacetRay n i) (signedFacetRayDerivative n i u) u := by
  rw [← (signedFacetRay_hasFDerivAt n i u).fderiv]
  exact (signedFacetRay_contDiff n i).contDiffAt.hasStrictFDerivAt (by norm_num)

theorem signedTailLinear_single_zero (n : ℕ) :
    signedTailLinear n (Pi.single (0 : Fin (n + 1)) (1 : ℝ)) = 0 := by
  funext k
  change (Pi.single (M := fun _ => ℝ) (0 : Fin (n + 1)) 1) k.succ = 0
  simp

theorem signedTailLinear_single_succ (n : ℕ) (j : Fin n) :
    signedTailLinear n (Pi.single j.succ (1 : ℝ)) = Pi.single j 1 := by
  funext k
  change (Pi.single (M := fun _ => ℝ) j.succ 1) k.succ = (Pi.single (M := fun _ => ℝ) j 1) k
  simp [Pi.single_apply]

theorem signedFacetRayDerivative_matrix (n : ℕ) (i : Fin (n + 2)) (u : Fin (n + 1) → ℝ) :
    LinearMap.toMatrix' (signedFacetRayDerivative n i u).toLinearMap =
      signedFacetChartMatrix n i (signedTailLinear n u) *
        Matrix.diagonal (Fin.cons (1 : ℝ) fun _ : Fin n => u 0) := by
  ext a b
  rw [Matrix.mul_diagonal]
  change (u 0 • signedFacetSlope n i (signedTailLinear n (Pi.single b 1)) +
      (Pi.single (M := fun _ => ℝ) b 1 0) • signedFacetVector n i (signedTailLinear n u)) a =
    signedFacetChartMatrix n i (signedTailLinear n u) a b *
      (Fin.cons (α := fun _ => ℝ) 1 fun _ : Fin n => u 0) b
  refine Fin.cases ?_ (fun j => ?_) b
  · simp [signedTailLinear_single_zero, signedFacetVector]
  · simp [signedTailLinear_single_succ, signedFacetChartMatrix_succ, mul_comm]

theorem signedFacetRayDerivative_det (n : ℕ) (i : Fin (n + 2)) (u : Fin (n + 1) → ℝ) :
    (signedFacetRayDerivative n i u).det =
      (Int.negOnePow (i.val : ℤ) • signedFacetCenter n) * (u 0) ^ n := by
  change (signedFacetRayDerivative n i u).toLinearMap.det = _
  rw [← LinearMap.det_toMatrix', signedFacetRayDerivative_matrix, Matrix.det_mul,
    signedFacetChartMatrix_det, Matrix.det_diagonal, Fin.prod_univ_succ]
  simp

end BanachIsometric.SingularPrism

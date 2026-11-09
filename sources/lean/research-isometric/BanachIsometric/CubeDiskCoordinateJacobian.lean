import BanachIsometric.RadialSupAxisOrientation
import BanachIsometric.SignedCoordinateTransport
import BanachIsometric.PiolaIdentity

/-! # Actual cube-to-disk coordinate Jacobian at regular first-axis points -/

namespace BanachIsometric

open scoped Topology

noncomputable section

def cubeCoordinateAxis (n : ℕ) (a : ℝ) : PiolaSpace (n + 1) :=
  Fin.cons a (fun _ : Fin n => 1 / 2)

def centeredCubeAmbient (n : ℕ) (u : PiolaSpace n) : PiolaSpace n := fun i => 2 * u i - 1

def cubeRadialCoordinates (n : ℕ) : PiolaSpace n → PiolaSpace n :=
  coordinateMapConjugate (euclideanCoordinates n) (radialGaugeMapInv (coordinateSupGauge n))

def cubeDiskCoordinateAmbient (n : ℕ) (u : PiolaSpace n) : PiolaSpace n :=
  cubeRadialCoordinates n (centeredCubeAmbient n u)

theorem euclideanCoordinates_single_first (n : ℕ) (r : ℝ) :
    euclideanCoordinates (n + 1) (EuclideanSpace.single 0 r) = Fin.cons r (0 : PiolaSpace n) := by
  funext i
  induction i using Fin.cases with
  | zero => simp [EuclideanSpace.single_apply]
  | succ j => simp [EuclideanSpace.single_apply]

theorem centeredCubeAmbient_axis (n : ℕ) (a : ℝ) :
    centeredCubeAmbient (n + 1) (cubeCoordinateAxis n a) = Fin.cons (2 * a - 1) 0 := by
  funext i
  induction i using Fin.cases with
  | zero => rfl
  | succ j => simp [centeredCubeAmbient, cubeCoordinateAxis]

theorem cubeDiskCoordinateAmbient_axis (n : ℕ) (a : ℝ) (ha : a ≠ 1 / 2) :
    cubeDiskCoordinateAmbient (n + 1) (cubeCoordinateAxis n a) = Fin.cons (2 * a - 1) 0 := by
  have hr : 2 * a - 1 ≠ 0 := by intro h; apply ha; linarith
  have hinv : (euclideanCoordinates (n + 1)).symm
      (centeredCubeAmbient (n + 1) (cubeCoordinateAxis n a)) = EuclideanSpace.single 0 (2 * a - 1) := by
    apply (euclideanCoordinates (n + 1)).injective
    rw [ContinuousLinearEquiv.apply_symm_apply, centeredCubeAmbient_axis, euclideanCoordinates_single_first]
  rw [cubeDiskCoordinateAmbient, cubeRadialCoordinates, coordinateMapConjugate, hinv,
    radialGaugeMapInv_sup_axis n _ hr, euclideanCoordinates_single_first]

theorem contDiff_centeredCubeAmbient (n : ℕ) (k : WithTop ℕ∞) :
    ContDiff ℝ k (centeredCubeAmbient n) := by
  apply contDiff_pi.mpr
  intro i
  exact (contDiff_const.mul (ContinuousLinearMap.proj i : PiolaSpace n →L[ℝ] ℝ).contDiff).sub contDiff_const

theorem hasFDerivAt_centeredCubeAmbient (n : ℕ) (u : PiolaSpace n) :
    HasFDerivAt (centeredCubeAmbient n) ((2 : ℝ) • ContinuousLinearMap.id ℝ (PiolaSpace n)) u := by
  have hid : HasFDerivAt (fun z : PiolaSpace n => z) (ContinuousLinearMap.id ℝ (PiolaSpace n)) u :=
    hasFDerivAt_id u
  simpa only [centeredCubeAmbient, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using
    (hid.const_smul (2 : ℝ)).sub_const (fun _ : Fin n => (1 : ℝ))

theorem contDiffAt_cubeRadialCoordinates_axis (n : ℕ) (r : ℝ) (hr : r ≠ 0) (k : WithTop ℕ∞) :
    ContDiffAt ℝ k (cubeRadialCoordinates (n + 1)) (Fin.cons r 0) := by
  let e := euclideanCoordinates (n + 1)
  let x : EuclideanSpace ℝ (Fin (n + 1)) := EuclideanSpace.single 0 r
  have hf : ContDiffAt ℝ k (radialGaugeMapInv (coordinateSupGauge (n + 1))) (e.symm (e x)) := by
    rw [e.symm_apply_apply]
    exact contDiffAt_radialGaugeMapInv_sup_axis n r hr k
  have hh := e.contDiff.contDiffAt.comp (e x) (hf.comp (e x) e.symm.contDiff.contDiffAt)
  simpa only [e, x, euclideanCoordinates_single_first, cubeRadialCoordinates, coordinateMapConjugate] using hh

theorem contDiffAt_cubeDiskCoordinateAmbient_axis (n : ℕ) (a : ℝ) (ha : a ≠ 1 / 2) (k : WithTop ℕ∞) :
    ContDiffAt ℝ k (cubeDiskCoordinateAmbient (n + 1)) (cubeCoordinateAxis n a) := by
  have hr : 2 * a - 1 ≠ 0 := by intro h; apply ha; linarith
  have hh : ContDiffAt ℝ k (cubeRadialCoordinates (n + 1))
      (centeredCubeAmbient (n + 1) (cubeCoordinateAxis n a)) := by
    rw [centeredCubeAmbient_axis]
    exact contDiffAt_cubeRadialCoordinates_axis n _ hr k
  exact hh.comp _ (contDiff_centeredCubeAmbient (n + 1) k).contDiffAt

theorem det_fderiv_cubeRadialCoordinates_axis_pos (n : ℕ) (r : ℝ) (hr : r ≠ 0) :
    0 < (fderiv ℝ (cubeRadialCoordinates (n + 1)) (Fin.cons r 0)).det := by
  have hd := det_fderiv_coordinateConjugate (euclideanCoordinates (n + 1))
    (radialGaugeMapInv (coordinateSupGauge (n + 1))) (EuclideanSpace.single 0 r)
  rw [euclideanCoordinates_single_first] at hd
  change (fderiv ℝ (cubeRadialCoordinates (n + 1)) (Fin.cons r 0)).det = _ at hd
  rw [hd]
  exact det_fderiv_radialGaugeMapInv_sup_axis_pos n r hr

theorem det_fderiv_cubeDiskCoordinateAmbient_axis_pos (n : ℕ) (a : ℝ) (ha : a ≠ 1 / 2) :
    0 < (fderiv ℝ (cubeDiskCoordinateAmbient (n + 1)) (cubeCoordinateAxis n a)).det := by
  have hr : 2 * a - 1 ≠ 0 := by intro h; apply ha; linarith
  have hR : DifferentiableAt ℝ (cubeRadialCoordinates (n + 1))
      (centeredCubeAmbient (n + 1) (cubeCoordinateAxis n a)) := by
    rw [centeredCubeAmbient_axis]
    exact (contDiffAt_cubeRadialCoordinates_axis n _ hr 1).differentiableAt (by norm_num)
  have hQ : HasFDerivAt (cubeDiskCoordinateAmbient (n + 1))
      ((fderiv ℝ (cubeRadialCoordinates (n + 1))
        (centeredCubeAmbient (n + 1) (cubeCoordinateAxis n a))).comp
          ((2 : ℝ) • ContinuousLinearMap.id ℝ (PiolaSpace (n + 1)))) (cubeCoordinateAxis n a) :=
    hR.hasFDerivAt.comp _ (hasFDerivAt_centeredCubeAmbient _ _)
  rw [hQ.fderiv]
  change 0 < LinearMap.det
    ((fderiv ℝ (cubeRadialCoordinates (n + 1))
      (centeredCubeAmbient (n + 1) (cubeCoordinateAxis n a))).toLinearMap.comp
        ((2 : ℝ) • (LinearMap.id : PiolaSpace (n + 1) →ₗ[ℝ] PiolaSpace (n + 1))))
  rw [LinearMap.det_comp, LinearMap.det_smul, LinearMap.det_id, mul_one, centeredCubeAmbient_axis]
  exact mul_pos (det_fderiv_cubeRadialCoordinates_axis_pos n _ hr) (pow_pos (by norm_num) _)

end
end BanachIsometric

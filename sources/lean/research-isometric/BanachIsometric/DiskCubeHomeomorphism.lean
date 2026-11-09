import BanachIsometric.CubeDiskCoordinates

/-! The actual disk–cube homeomorphism and exact boundary correspondence,
constructed using the already proved radial gauge homeomorphism. -/

noncomputable section

namespace BanachIsometric

open Set Metric
open scoped Topology unitInterval

def euclideanDiskToCube (n : ℕ) : closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 → (Fin n → unitInterval) := by
  intro x
  let e := radialGaugeHomeomorph (coordinateSupGauge_homogeneous n) (continuous_coordinateSupGauge n)
  let w := euclideanCoordinates n (e x.val)
  have hw : ‖w‖ ≤ 1 := by
    change coordinateSupGauge n (radialGaugeMap (coordinateSupGauge n) x.val) ≤ 1
    rw [gauge_radialGaugeMap (coordinateSupGauge_homogeneous n)]
    simpa only [Metric.mem_closedBall, dist_zero_right] using x.property
  intro i
  refine ⟨(w i + 1) / 2, ?_⟩
  have hi := (norm_le_pi_norm w i).trans hw
  rw [Real.norm_eq_abs, abs_le] at hi
  exact ⟨by linarith [hi.1], by linarith [hi.2]⟩

theorem continuous_euclideanDiskToCube (n : ℕ) : Continuous (euclideanDiskToCube n) := by
  apply continuous_pi
  intro i
  apply Continuous.subtype_mk
  exact (((continuous_apply i).comp ((euclideanCoordinates n).continuous.comp
    ((radialGaugeHomeomorph (coordinateSupGauge_homogeneous n)
      (continuous_coordinateSupGauge n)).continuous.comp continuous_subtype_val))).add continuous_const).div_const 2

def cubeDiskHomeomorph (n : ℕ) : (Fin n → unitInterval) ≃ₜ closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 where
  toFun := cubeToEuclideanDisk n
  invFun := euclideanDiskToCube n
  left_inv y := by
    let e := radialGaugeHomeomorph (coordinateSupGauge_homogeneous n) (continuous_coordinateSupGauge n)
    funext i
    apply Subtype.ext
    change (euclideanCoordinates n (e (e.symm ((euclideanCoordinates n).symm (centeredCube n y)))) i + 1) / 2 =
      (y i : ℝ)
    rw [e.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply]
    dsimp [centeredCube]
    ring
  right_inv x := by
    let e := radialGaugeHomeomorph (coordinateSupGauge_homogeneous n) (continuous_coordinateSupGauge n)
    have hc : centeredCube n (euclideanDiskToCube n x) = euclideanCoordinates n (e x.val) := by
      funext i
      change 2 * ((euclideanCoordinates n (e x.val) i + 1) / 2) - 1 = euclideanCoordinates n (e x.val) i
      ring
    apply Subtype.ext
    change e.symm ((euclideanCoordinates n).symm (centeredCube n (euclideanDiskToCube n x))) = x.val
    rw [hc, ContinuousLinearEquiv.symm_apply_apply, e.symm_apply_apply]
  continuous_toFun := continuous_cubeToEuclideanDisk n
  continuous_invFun := continuous_euclideanDiskToCube n

theorem cubeDiskHomeomorph_boundary (n : ℕ) (y : I^ (Fin n)) :
    ‖(cubeDiskHomeomorph n y).val‖ = 1 ↔ y ∈ Cube.boundary (Fin n) := by
  change ‖(cubeToEuclideanDisk n y).val‖ = 1 ↔ _
  rw [norm_cubeToEuclideanDisk, centeredCube_norm_eq_one_iff_boundary]

end BanachIsometric

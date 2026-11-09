import BanachIsometric.CubeDiskCoordinateJacobian
import BanachIsometric.PrefixCoordinateCalculus
import BanachIsometric.DiskSphereConeOrientation
import BanachIsometric.DiskSphereChartRegularity
import BanachIsometric.CubicalSphereGenerator

/-!
# Actual smooth cone chart of the cubical sphere quotient at first-axis points

The literal cube-to-disk map has positive Jacobian, and the literal disk cone
chart has negative Jacobian in the specified coordinate order. Their actual
composition is therefore a negatively oriented smooth local chart.
-/

namespace BanachIsometric.SphereGenerator

open scoped Topology unitInterval

noncomputable section

def cubeSphereConeChart (n : ℕ) : PiolaSpace (n + 2) → PiolaSpace (n + 2) :=
  fun z => diskSphereConeChart n (prefixMap (cubeDiskCoordinateAmbient (n + 1)) z)

def cubeSphereConeAxis (n : ℕ) (ρ a : ℝ) : PiolaSpace (n + 2) := Fin.cons ρ (cubeCoordinateAxis n a)

theorem cubeDiskPrefix_axis (n : ℕ) (ρ a : ℝ) (ha : a ≠ 1 / 2) :
    prefixMap (cubeDiskCoordinateAmbient (n + 1)) (cubeSphereConeAxis n ρ a) =
      diskSphereConeAxis n ρ (2 * a - 1) := by
  change (Fin.cons ρ (cubeDiskCoordinateAmbient (n + 1) (cubeCoordinateAxis n a)) : PiolaSpace (n + 2)) = _
  rw [cubeDiskCoordinateAmbient_axis n a ha]
  rfl

theorem contDiffAt_diskSphereConeChart_axis (n : ℕ) (ρ r : ℝ) (hr : r ^ 2 < 1)
    (k : WithTop ℕ∞) :
    ContDiffAt ℝ k (diskSphereConeChart n) (diskSphereConeAxis n ρ r) := by
  have hnorm : ‖diskSphereConeTail n (diskSphereConeAxis n ρ r)‖ < 1 := by
    have hn := norm_sq_diskSphereConeTail_axis n ρ r
    nlinarith [norm_nonneg (diskSphereConeTail n (diskSphereConeAxis n ρ r))]
  have hfun : diskSphereConeChart n = fun z => euclideanCoordinates (n + 2)
      (z 0 • diskSphereAmbient (n + 1) (diskSphereConeTail n z)) := by
    funext z
    exact diskSphereConeChart_eq_raw n z
  rw [hfun]
  exact (euclideanCoordinates (n + 2)).contDiff.contDiffAt.comp _
    ((ContinuousLinearMap.proj (0 : Fin (n + 2)) : PiolaSpace (n + 2) →L[ℝ] ℝ).contDiff.contDiffAt.smul
      ((contDiffAt_diskSphereAmbient (n + 1) k _ hnorm).comp _
        (diskSphereConeTail n).contDiff.contDiffAt))

theorem contDiffAt_cubeSphereConeChart_axis (n : ℕ) (ρ a : ℝ) (ha : a ≠ 1 / 2)
    (haxis : (2 * a - 1) ^ 2 < 1) (k : WithTop ℕ∞) :
    ContDiffAt ℝ k (cubeSphereConeChart n) (cubeSphereConeAxis n ρ a) := by
  have hP := contDiffAt_prefixMap (contDiffAt_cubeDiskCoordinateAmbient_axis n a ha k) ρ
  have hD : ContDiffAt ℝ k (diskSphereConeChart n)
      (prefixMap (cubeDiskCoordinateAmbient (n + 1)) (cubeSphereConeAxis n ρ a)) := by
    rw [cubeDiskPrefix_axis n ρ a ha]
    exact contDiffAt_diskSphereConeChart_axis n ρ _ haxis k
  exact hD.comp _ hP

theorem det_fderiv_cubeSphereConeChart_axis_neg (n : ℕ) (ρ a : ℝ) (hρ : 0 < ρ)
    (ha : a ≠ 1 / 2) (haxis : (2 * a - 1) ^ 2 < 1) :
    (fderiv ℝ (cubeSphereConeChart n) (cubeSphereConeAxis n ρ a)).det < 0 := by
  let Q := cubeDiskCoordinateAmbient (n + 1)
  let D := fderiv ℝ Q (cubeCoordinateAxis n a)
  have hQ : HasFDerivAt Q D (cubeCoordinateAxis n a) :=
    ((contDiffAt_cubeDiskCoordinateAmbient_axis n a ha 1).differentiableAt (by norm_num)).hasFDerivAt
  have hP := hasFDerivAt_prefixMap hQ ρ
  have hD : HasFDerivAt (diskSphereConeChart n) (diskSphereConeChartDerivative n ρ (2 * a - 1))
      (prefixMap Q (cubeSphereConeAxis n ρ a)) := by
    rw [cubeDiskPrefix_axis n ρ a ha]
    exact hasFDerivAt_diskSphereConeChart_axis n ρ _ haxis
  have hS : HasFDerivAt (cubeSphereConeChart n)
      ((diskSphereConeChartDerivative n ρ (2 * a - 1)).comp (prefixBlockCLM D))
        (cubeSphereConeAxis n ρ a) := hD.comp _ hP
  rw [hS.fderiv]
  change LinearMap.det ((diskSphereConeChartDerivative n ρ (2 * a - 1)).toLinearMap.comp
    (prefixBlockCLM D).toLinearMap) < 0
  rw [LinearMap.det_comp]
  change (diskSphereConeChartDerivative n ρ (2 * a - 1)).det * (prefixBlockCLM D).det < 0
  rw [det_prefixBlockCLM]
  have hneg : (diskSphereConeChartDerivative n ρ (2 * a - 1)).det < 0 := by
    rw [← (hasFDerivAt_diskSphereConeChart_axis n ρ _ haxis).fderiv]
    exact det_fderiv_diskSphereConeChart_neg n ρ _ hρ haxis
  exact mul_neg_of_neg_of_pos hneg (det_fderiv_cubeDiskCoordinateAmbient_axis_pos n a ha)

theorem hasStrictFDerivAt_cubeSphereConeChart_axis (n : ℕ) (ρ a : ℝ) (ha : a ≠ 1 / 2)
    (haxis : (2 * a - 1) ^ 2 < 1) :
    HasStrictFDerivAt (cubeSphereConeChart n)
      (fderiv ℝ (cubeSphereConeChart n) (cubeSphereConeAxis n ρ a)) (cubeSphereConeAxis n ρ a) :=
  (contDiffAt_cubeSphereConeChart_axis n ρ a ha haxis 1).hasStrictFDerivAt (by norm_num)

theorem cubeSphereConeChart_eq_raw (n : ℕ) (ρ : ℝ) (u : Fin (n + 1) → unitInterval) :
    cubeSphereConeChart n (Fin.cons ρ (fun i => (u i : ℝ))) =
      euclideanCoordinates (n + 2) (ρ • (cubeToSphere (n + 1) u).val) := by
  have htail : diskSphereConeTail n
      (prefixMap (cubeDiskCoordinateAmbient (n + 1)) (Fin.cons ρ (fun i => (u i : ℝ)))) =
      (cubeDiskHomeomorph (n + 1) u).val := by
    ext i
    rfl
  rw [cubeSphereConeChart, diskSphereConeChart_eq_raw]
  change euclideanCoordinates (n + 2)
    (ρ • consLp (2 * ‖diskSphereConeTail n
      (prefixMap (cubeDiskCoordinateAmbient (n + 1)) (Fin.cons ρ (fun i => (u i : ℝ))))‖ ^ 2 - 1)
      ((2 * Real.sqrt (1 - ‖diskSphereConeTail n
        (prefixMap (cubeDiskCoordinateAmbient (n + 1)) (Fin.cons ρ (fun i => (u i : ℝ))))‖ ^ 2)) •
          diskSphereConeTail n (prefixMap (cubeDiskCoordinateAmbient (n + 1))
            (Fin.cons ρ (fun i => (u i : ℝ)))))) = _
  rw [htail]
  rfl

end
end BanachIsometric.SphereGenerator

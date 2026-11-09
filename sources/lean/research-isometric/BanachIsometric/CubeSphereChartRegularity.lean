import BanachIsometric.CubeDiskLipschitz
import BanachIsometric.DiskSphereChartRegularity
import BanachIsometric.CubicalSphereGenerator

/-! Actual local Lipschitz chart formulas for the cubical sphere quotient.
The ambient inverse formula recovers every actual interior cube point
exactly, and is locally Lipschitz wherever the first sphere coordinate is
less than one. No orientation or degree law is assumed. -/

noncomputable section
namespace BanachIsometric.SphereGenerator
open Set Metric
open scoped Topology NNReal unitInterval

def uncenterCubeCoordinates (n : ℕ) (w : Fin n → ℝ) : Fin n → ℝ := fun i => (w i + 1) / 2

theorem lipschitz_uncenterCubeCoordinates (n : ℕ) : LipschitzWith 1 (uncenterCubeCoordinates n) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [NNReal.coe_one, one_mul]
  apply (dist_pi_le_iff dist_nonneg).mpr
  intro i
  change |(x i + 1) / 2 - (y i + 1) / 2| ≤ dist x y
  rw [show (x i + 1) / 2 - (y i + 1) / 2 = (x i - y i) / 2 by ring,
    abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hi : |x i - y i| ≤ dist x y := by
    simpa only [NNReal.coe_one, one_mul, Real.dist_eq] using (LipschitzWith.eval i).dist_le_mul x y
  linarith [abs_nonneg (x i - y i)]

def cubeSphereInverseAmbient (n : ℕ) (z : EuclideanSpace ℝ (Fin (n + 1))) : Fin n → ℝ :=
  uncenterCubeCoordinates n (euclideanCoordinates n
    (radialGaugeMap (coordinateSupGauge n) (sphereDiskInverseAmbient n z)))

theorem norm_cubeDisk_lt_one_of_not_boundary (n : ℕ) (u : Fin n → unitInterval)
    (hu : u ∉ Cube.boundary (Fin n)) : ‖(cubeDiskHomeomorph n u).val‖ < 1 := by
  have hle : ‖(cubeDiskHomeomorph n u).val‖ ≤ 1 := by
    simpa only [mem_closedBall, dist_zero_right] using (cubeDiskHomeomorph n u).property
  exact lt_of_le_of_ne hle (fun he => hu ((cubeDiskHomeomorph_boundary n u).mp he))

theorem cubeToSphere_first_lt_one_of_not_boundary (n : ℕ) (u : Fin n → unitInterval)
    (hu : u ∉ Cube.boundary (Fin n)) : (cubeToSphere n u).val 0 < 1 := by
  have hnorm := norm_cubeDisk_lt_one_of_not_boundary n u hu
  change 2 * ‖(cubeDiskHomeomorph n u).val‖ ^ 2 - 1 < 1
  nlinarith [norm_nonneg (cubeDiskHomeomorph n u).val]

theorem cubeSphereInverse_cubeToSphere (n : ℕ) (u : Fin n → unitInterval)
    (hu : u ∉ Cube.boundary (Fin n)) :
    cubeSphereInverseAmbient n (cubeToSphere n u).val = fun i => (u i : ℝ) := by
  have hnorm := norm_cubeDisk_lt_one_of_not_boundary n u hu
  change uncenterCubeCoordinates n (euclideanCoordinates n
    (radialGaugeMap (coordinateSupGauge n)
      (sphereDiskInverseAmbient n (diskSphereAmbient n (cubeDiskHomeomorph n u).val)))) = _
  rw [sphereDiskInverse_diskSphereAmbient n _ hnorm]
  change uncenterCubeCoordinates n (euclideanCoordinates n
    (radialGaugeMap (coordinateSupGauge n) (radialGaugeMapInv (coordinateSupGauge n)
      ((euclideanCoordinates n).symm (centeredCube n u))))) = _
  rw [radialGaugeMap_mapInv (coordinateSupGauge_homogeneous n), ContinuousLinearEquiv.apply_symm_apply]
  funext i
  change (2 * (u i : ℝ) - 1 + 1) / 2 = (u i : ℝ)
  ring

theorem exists_lipschitzOn_cubeSphereInverseAmbient_nhds (n : ℕ)
    (z : EuclideanSpace ℝ (Fin (n + 1))) (hz : z 0 < 1) :
    ∃ L : ℝ≥0, ∃ U ∈ 𝓝 z, LipschitzOnWith L (cubeSphereInverseAmbient n) U := by
  obtain ⟨R, hR⟩ := exists_lipschitz_radialGaugeMap (coordinateSupGauge_homogeneous n)
    (lipschitz_coordinateSupGauge n).lipschitzOnWith
  obtain ⟨L, U, hU, hLip⟩ := exists_lipschitzOn_sphereDiskInverseAmbient_nhds n z hz
  have houter := (lipschitz_uncenterCubeCoordinates n).comp ((euclideanCoordinates n).lipschitz.comp hR)
  exact ⟨(1 * (‖(euclideanCoordinates n).toContinuousLinearMap‖₊ * R)) * L,
    U, hU, houter.comp_lipschitzOnWith hLip⟩

theorem exists_lipschitzOn_cubeToSphere_nhds (n : ℕ) (u : Fin n → unitInterval)
    (hu : u ∉ Cube.boundary (Fin n)) :
    ∃ L : ℝ≥0, ∃ U ∈ 𝓝 u, LipschitzOnWith L (cubeToSphere n) U := by
  have hnorm := norm_cubeDisk_lt_one_of_not_boundary n u hu
  obtain ⟨D, hD⟩ := exists_lipschitz_cubeDiskHomeomorph n
  have hval := (LipschitzWith.subtype_val _).comp hD
  obtain ⟨L, U, hU, hLip⟩ := exists_lipschitzOn_diskSphereAmbient_nhds n
    (cubeDiskHomeomorph n u).val hnorm
  let W := (fun v : Fin n → unitInterval => (cubeDiskHomeomorph n v).val) ⁻¹' U
  have hW : W ∈ 𝓝 u := hval.continuous.continuousAt.preimage_mem_nhds hU
  refine ⟨L * (1 * D), W, hW, ?_⟩
  have hcomp := hLip.comp hval.lipschitzOnWith (fun _ hv => hv)
  exact hcomp

end BanachIsometric.SphereGenerator

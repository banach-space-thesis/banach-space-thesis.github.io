import BanachIsometric.CubeSphereChartRegularity
import BanachIsometric.SphereRepetitionFiberCoordinates

/-! A total explicit clamped inverse to the cubical sphere quotient, which
is the exact inverse off the pole and is locally Lipschitz there. Clamping
extends the formula to all ambient vectors; it is not used to change its
values on the actual interior chart. -/

noncomputable section
namespace BanachIsometric.SphereGenerator
open Set Metric
open scoped Topology NNReal unitInterval

def clampCube (n : ℕ) (w : Fin n → ℝ) : Fin n → unitInterval :=
  fun i => Set.projIcc 0 1 zero_le_one (w i)

theorem lipschitz_clampCube (n : ℕ) : LipschitzWith 1 (clampCube n) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [NNReal.coe_one, one_mul]
  apply (dist_pi_le_iff dist_nonneg).mpr
  intro i
  have hclamp := (LipschitzWith.projIcc (zero_le_one : (0 : ℝ) ≤ 1)).dist_le_mul (x i) (y i)
  have hcoord := (LipschitzWith.eval i).dist_le_mul x y
  have hc : dist (clampCube n x i) (clampCube n y i) ≤ dist (x i) (y i) := by
    simpa only [NNReal.coe_one, one_mul] using hclamp
  have hi : dist (x i) (y i) ≤ dist x y := by
    simpa only [NNReal.coe_one, one_mul] using hcoord
  exact hc.trans hi

def sphereCubeInverse (n : ℕ) (z : Sph n) : Fin n → unitInterval :=
  clampCube n (cubeSphereInverseAmbient n z.val)

theorem sphereCubeInverse_cubeToSphere (n : ℕ) (u : Fin n → unitInterval)
    (hu : u ∉ Cube.boundary (Fin n)) : sphereCubeInverse n (cubeToSphere n u) = u := by
  unfold sphereCubeInverse
  rw [cubeSphereInverse_cubeToSphere n u hu]
  funext i
  exact Set.projIcc_val zero_le_one (u i)

theorem cubeToSphere_sphereCubeInverse (n : ℕ) (z : Sph (n + 1))
    (hz : z ≠ sphereBasepoint (n + 1)) :
    cubeToSphere (n + 1) (sphereCubeInverse (n + 1) z) = z := by
  obtain ⟨u, rfl⟩ := cubeToSphere_surjective n z
  have hu : u ∉ Cube.boundary (Fin (n + 1)) := fun hu => hz (cubeToSphere_boundary _ _ hu)
  rw [sphereCubeInverse_cubeToSphere _ _ hu]

theorem sphere_first_lt_one_of_ne_basepoint (n : ℕ) (z : Sph (n + 1))
    (hz : z ≠ sphereBasepoint (n + 1)) : z.val 0 < 1 := by
  obtain ⟨u, rfl⟩ := cubeToSphere_surjective n z
  exact cubeToSphere_first_lt_one_of_not_boundary _ _
    (fun hu => hz (cubeToSphere_boundary _ _ hu))

theorem exists_lipschitzOn_sphereCubeInverse_nhds (n : ℕ) (z : Sph (n + 1))
    (hz : z ≠ sphereBasepoint (n + 1)) :
    ∃ L : ℝ≥0, ∃ U ∈ 𝓝 z, LipschitzOnWith L (sphereCubeInverse (n + 1)) U := by
  obtain ⟨L, U, hU, hLip⟩ := exists_lipschitzOn_cubeSphereInverseAmbient_nhds
    (n + 1) z.val (sphere_first_lt_one_of_ne_basepoint n z hz)
  let W : Set (Sph (n + 1)) := Subtype.val ⁻¹' U
  have hW : W ∈ 𝓝 z := continuous_subtype_val.continuousAt.preimage_mem_nhds hU
  have hcomp : LipschitzOnWith (L * 1) (fun w : Sph (n + 1) =>
      cubeSphereInverseAmbient (n + 1) w.val) W :=
    hLip.comp (LipschitzWith.subtype_val _).lipschitzOnWith (fun _ hw => hw)
  exact ⟨1 * (L * 1), W, hW, (lipschitz_clampCube _).comp_lipschitzOnWith hcomp⟩

end BanachIsometric.SphereGenerator

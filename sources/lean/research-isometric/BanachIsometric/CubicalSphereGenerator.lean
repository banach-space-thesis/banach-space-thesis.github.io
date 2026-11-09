import BanachIsometric.SphereGenerator
import BanachIsometric.DiskCubeHomeomorphism

/-! The actual cube quotient model of the ordinary metric sphere. The cube–disk
homeomorphism uses the Euclidean norm; only its explicit auxiliary gauge is a
coordinate sup norm. Boundary collapse and all fibres are proved exactly. -/

noncomputable section
namespace BanachIsometric.SphereGenerator

open scoped Topology Topology.Homotopy unitInterval
open Topology

def cubeToSphere (n : ℕ) : C((Fin n → unitInterval), Sph n) :=
  (closedDiskToSphere n).comp ⟨cubeDiskHomeomorph n, (cubeDiskHomeomorph n).continuous⟩

theorem cubeToSphere_boundary (n : ℕ) (u : Fin n → unitInterval)
    (hu : u ∈ Cube.boundary (Fin n)) :
    cubeToSphere n u = sphereBasepoint n :=
  closedDiskToSphere_boundary n _ ((cubeDiskHomeomorph_boundary n u).mpr hu)

theorem cubeToSphere_surjective (n : ℕ) : Function.Surjective (cubeToSphere (n + 1)) := by
  intro z
  obtain ⟨x, hx⟩ := closedDiskToSphere_surjective n z
  obtain ⟨u, hu⟩ := (cubeDiskHomeomorph (n + 1)).surjective x
  refine ⟨u, ?_⟩
  change closedDiskToSphere (n + 1) (cubeDiskHomeomorph (n + 1) u) = z
  rw [hu, hx]

theorem cubeToSphere_eq_iff (n : ℕ) (u v : Fin n → unitInterval) :
    cubeToSphere n u = cubeToSphere n v ↔
      u = v ∨ (u ∈ Cube.boundary (Fin n) ∧ v ∈ Cube.boundary (Fin n)) := by
  change closedDiskToSphere n _ = closedDiskToSphere n _ ↔ _
  rw [closedDiskToSphere_eq_iff]
  change cubeDiskHomeomorph n u = cubeDiskHomeomorph n v ∨
    (‖(cubeDiskHomeomorph n u).val‖ = 1 ∧ ‖(cubeDiskHomeomorph n v).val‖ = 1) ↔ _
  rw [cubeDiskHomeomorph_boundary, cubeDiskHomeomorph_boundary]
  exact or_congr (cubeDiskHomeomorph n).injective.eq_iff Iff.rfl

theorem isQuotientMap_cubeToSphere (n : ℕ) : IsQuotientMap (cubeToSphere (n + 1)) :=
  (cubeToSphere (n + 1)).continuous.isClosedMap.isQuotientMap
    (cubeToSphere (n + 1)).continuous (cubeToSphere_surjective n)

def sphereGenerator (n : ℕ) : GenLoop (Fin n) (Sph n) (sphereBasepoint n) :=
  ⟨cubeToSphere n, cubeToSphere_boundary n⟩

end BanachIsometric.SphereGenerator

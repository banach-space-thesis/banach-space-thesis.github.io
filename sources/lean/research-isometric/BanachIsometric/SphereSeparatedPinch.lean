import BanachIsometric.CubeBoxPinch

/-! The two cube pinches descend to actual sphere self-maps homotopic to the
identity. Each is constant at the basepoint off its own compact support. -/

noncomputable section
namespace BanachIsometric.SphereGenerator
open Set
open scoped Topology Topology.Homotopy unitInterval

def boxPinchGenLoop (n : ℕ) (right : Bool) :
    GenLoop (Fin (n + 1)) (Sph (n + 1)) (sphereBasepoint (n + 1)) :=
  ⟨(cubeToSphere (n + 1)).comp (cubeBoxPinch n right), fun u hu =>
    cubeToSphere_boundary (n + 1) _ (cubeBoxPinch_boundary n right u hu)⟩

def boxPinchGenLoopHomotopyRel (n : ℕ) (right : Bool) :
    ContinuousMap.HomotopyRel (sphereGenerator (n + 1)).val (boxPinchGenLoop n right).val
      (Cube.boundary (Fin (n + 1))) where
  toHomotopy := {
    toContinuousMap := (cubeToSphere (n + 1)).comp (cubePinchInterpolation n right)
    map_zero_left := by
      intro u
      change cubeToSphere (n + 1) (cubePinchInterpolation n right (0, u)) = cubeToSphere (n + 1) u
      rw [cubePinchInterpolation_zero]
    map_one_left := by
      intro u
      change cubeToSphere (n + 1) (cubePinchInterpolation n right (1, u)) =
        cubeToSphere (n + 1) (cubeBoxPinch n right u)
      rw [cubePinchInterpolation_one] }
  prop' := by
    intro t u hu
    change cubeToSphere (n + 1) (cubePinchInterpolation n right (t, u)) = cubeToSphere (n + 1) u
    rw [cubeToSphere_boundary _ _ (cubePinchInterpolation_boundary n right t u hu),
      cubeToSphere_boundary _ _ hu]

def sphereBoxPinch (n : ℕ) (right : Bool) : C(Sph (n + 1), Sph (n + 1)) :=
  targetGenLoopSphereMap n (boxPinchGenLoop n right)

theorem sphereBoxPinch_apply_cube (n : ℕ) (right : Bool) (u : SpherePinchCube n) :
    sphereBoxPinch n right (cubeToSphere (n + 1) u) = cubeToSphere (n + 1) (cubeBoxPinch n right u) := by
  have h := congrArg (fun f : C(SpherePinchCube n, Sph (n + 1)) => f u)
    (targetGenLoopSphereMap_comp_cubeToSphere n (boxPinchGenLoop n right))
  exact h

def sphereBoxPinchHomotopy (n : ℕ) (right : Bool) :
    (ContinuousMap.id (Sph (n + 1))).Homotopy (sphereBoxPinch n right) := by
  have hid : targetGenLoopSphereMap n (sphereGenerator (n + 1)) = ContinuousMap.id _ := by
    apply ContinuousMap.ext
    intro z
    obtain ⟨u, rfl⟩ := cubeToSphere_surjective n z
    have h := congrArg (fun f : C(SpherePinchCube n, Sph (n + 1)) => f u)
      (targetGenLoopSphereMap_comp_cubeToSphere n (sphereGenerator (n + 1)))
    exact h
  exact (targetGenLoopSphereMapHomotopy n (boxPinchGenLoopHomotopyRel n right)).cast hid rfl

def spherePinchSupport (n : ℕ) (right : Bool) : Set (Sph (n + 1)) :=
  cubeToSphere (n + 1) '' cubePinchSupport n right

theorem isClosed_spherePinchSupport (n : ℕ) (right : Bool) : IsClosed (spherePinchSupport n right) :=
  ((isClosed_cubePinchSupport n right).isCompact.image (cubeToSphere (n + 1)).continuous).isClosed

theorem disjoint_spherePinchSupport (n : ℕ) :
    Disjoint (spherePinchSupport n false) (spherePinchSupport n true) := by
  apply Set.disjoint_left.mpr
  rintro x ⟨u, hu, rfl⟩ ⟨v, hv, he⟩
  rcases (cubeToSphere_eq_iff (n + 1) u v).mp he.symm with rfl | ⟨hu', _⟩
  · exact (Set.disjoint_left.mp (disjoint_cubePinchSupport n)) hu hv
  · exact (not_boundary_of_mem_cubePinchSupport n false u hu) hu'

theorem sphereBoxPinch_eq_basepoint_of_notMem (n : ℕ) (right : Bool) (x : Sph (n + 1))
    (hx : x ∉ spherePinchSupport n right) : sphereBoxPinch n right x = sphereBasepoint (n + 1) := by
  obtain ⟨u, rfl⟩ := cubeToSphere_surjective n x
  have hu : u ∉ cubePinchSupport n right := fun h => hx ⟨u, h, rfl⟩
  rw [sphereBoxPinch_apply_cube]
  exact cubeToSphere_boundary _ _ (cubeBoxPinch_boundary_of_not_mem_support n right u hu)

def spherePinchOpenCover (n : ℕ) (right : Bool) : Set (Sph (n + 1)) := (spherePinchSupport n right)ᶜ

theorem isOpen_spherePinchOpenCover (n : ℕ) (right : Bool) : IsOpen (spherePinchOpenCover n right) :=
  (isClosed_spherePinchSupport n right).isOpen_compl

theorem mem_spherePinchOpenCover (n : ℕ) (x : Sph (n + 1)) :
    ∃ right, x ∈ spherePinchOpenCover n right := by
  by_cases hx : x ∈ spherePinchSupport n false
  · exact ⟨true, fun hy => (Set.disjoint_left.mp (disjoint_spherePinchSupport n)) hx hy⟩
  · exact ⟨false, hx⟩

end BanachIsometric.SphereGenerator

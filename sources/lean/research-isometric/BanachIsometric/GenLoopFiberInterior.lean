import BanachIsometric.SphereRepetitionFiberCoordinates

/-! Every actual non-basepoint cubical fiber lies strictly inside the cube.
The explicit generator's chosen target has precisely its specified cube point
as preimage. Both statements concern literal maps and boundary conditions. -/

noncomputable section
namespace BanachIsometric
open scoped Topology Topology.Homotopy unitInterval

theorem genLoop_fiber_not_mem_boundary
    {N X : Type*} [TopologicalSpace X] {base z : X}
    (p : GenLoop N X base) (hz : z ≠ base) (u : N → unitInterval) (hu : p u = z) :
    u ∉ Cube.boundary N := fun hb => hz (hu.symm.trans (p.property u hb))

theorem genLoop_fiber_coordinate_lt_one
    {N X : Type*} [TopologicalSpace X] {base z : X}
    (p : GenLoop N X base) (hz : z ≠ base) (u : N → unitInterval) (hu : p u = z) (i : N) :
    (u i : ℝ) < 1 := by
  have hne : (u i : ℝ) ≠ 1 := by
    intro he
    exact genLoop_fiber_not_mem_boundary p hz u hu ⟨i, Or.inr (Subtype.ext he)⟩
  exact lt_of_le_of_ne (u i).property.2 hne

theorem genLoop_fiber_coordinate_mem_Ioo
    {N X : Type*} [TopologicalSpace X] {base z : X}
    (p : GenLoop N X base) (hz : z ≠ base) (u : N → unitInterval) (hu : p u = z) (i : N) :
    0 < (u i : ℝ) ∧ (u i : ℝ) < 1 :=
  ⟨genLoop_fiber_coordinate_pos p hz ⟨u, hu⟩ i, genLoop_fiber_coordinate_lt_one p hz u hu i⟩

namespace SphereGenerator

theorem cubeToSphere_axisTarget_fiber_eq (n : ℕ) (u : Fin (n + 1) → unitInterval)
    (hu : cubeToSphere (n + 1) u = axisSphereTarget n) : u = axisCubeTarget n := by
  letI := subsingleton_cubeToSphere_fiber n (axisSphereTarget n) (axisSphereTarget_ne_basepoint n)
  exact congrArg Subtype.val (Subsingleton.elim
    (⟨u, hu⟩ : {u : Fin (n + 1) → unitInterval // cubeToSphere (n + 1) u = axisSphereTarget n})
    ⟨axisCubeTarget n, rfl⟩)

end SphereGenerator
end BanachIsometric

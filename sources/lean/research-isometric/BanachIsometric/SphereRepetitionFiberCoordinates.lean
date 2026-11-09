import BanachIsometric.SphereRepetitionFibers

/-! Actual coordinate invariants of non-pole repetition fibers. Affine
half-cube embeddings preserve every other coordinate, and the outer
concatenation sends its dividing hyperplane to the basepoint. -/

noncomputable section
namespace BanachIsometric
open scoped Topology Topology.Homotopy unitInterval

variable {N X : Type*} [DecidableEq N] [TopologicalSpace X] {x z : X}

theorem genLoop_transAt_at_half (i : N) (f g : GenLoop N X x)
    (u : N → unitInterval) (hu : (u i : ℝ) = 1 / 2) : GenLoop.transAt i f g u = x := by
  have hbound : leftExpandCube i u ∈ Cube.boundary N := by
    refine ⟨i, Or.inr ?_⟩
    apply Subtype.ext
    simp only [leftExpandCube, Function.update_self]
    rw [hu]
    norm_num [Set.projIcc]
  simp only [GenLoop.transAt, GenLoop.coe_copy, if_pos hu.le]
  exact f.property _ hbound

theorem repeatGenLoop_fiber_coordinate_ne_half (i : N) (p : GenLoop N X x)
    (hz : z ≠ x) (d : ℕ) (u : {u : N → unitInterval // repeatGenLoop i p d u = z}) :
    (u.val i : ℝ) ≠ 1 / 2 := by
  cases d with
  | zero => exact (hz u.property.symm).elim
  | succ d =>
    intro hu
    exact hz (u.property.symm.trans (genLoop_transAt_at_half i _ _ u.val hu))

theorem repeatGenLoop_fiber_coordinate_of_ne (i j : N) (hji : j ≠ i)
    (p : GenLoop N X x) (hz : z ≠ x) (t : unitInterval)
    (hp : ∀ u : {u : N → unitInterval // p u = z}, u.val j = t)
    (d : ℕ) (u : {u : N → unitInterval // repeatGenLoop i p d u = z}) : u.val j = t := by
  induction d with
  | zero => exact (hz u.property.symm).elim
  | succ d ih =>
    obtain ⟨w, hw⟩ := transAtFiberMap_surjective i (repeatGenLoop i p d) p hz u
    rcases w with v | v
    · have he : leftHalfCube i v.val = u.val := congrArg Subtype.val hw
      rw [← he]
      change Function.update v.val i _ j = t
      rw [Function.update_of_ne hji]
      exact ih v
    · have he : rightHalfCube i v.val = u.val := congrArg Subtype.val hw
      rw [← he]
      change Function.update v.val i _ j = t
      rw [Function.update_of_ne hji]
      exact hp v

namespace SphereGenerator

theorem cubeToSphere_eq_basepoint_iff_boundary (n : ℕ) (u : Fin (n + 1) → unitInterval) :
    cubeToSphere (n + 1) u = sphereBasepoint (n + 1) ↔ u ∈ Cube.boundary (Fin (n + 1)) := by
  let v : Fin (n + 1) → unitInterval := fun _ => 0
  have hv : v ∈ Cube.boundary (Fin (n + 1)) := ⟨0, Or.inl rfl⟩
  constructor
  · intro hu
    have he : cubeToSphere (n + 1) u = cubeToSphere (n + 1) v :=
      hu.trans (cubeToSphere_boundary _ _ hv).symm
    rcases (cubeToSphere_eq_iff _ _ _).mp he with rfl | he
    · exact hv
    · exact he.1
  · exact cubeToSphere_boundary _ _

def axisCubeTarget (n : ℕ) : Fin (n + 1) → unitInterval :=
  fun i => if i = 0 then ⟨1 / 3, by norm_num⟩ else ⟨1 / 2, by norm_num⟩

def axisSphereTarget (n : ℕ) : Sph (n + 1) := cubeToSphere (n + 1) (axisCubeTarget n)

theorem axisSphereTarget_ne_basepoint (n : ℕ) :
    axisSphereTarget n ≠ sphereBasepoint (n + 1) := by
  intro he
  have h := (cubeToSphere_eq_basepoint_iff_boundary n _).mp he
  obtain ⟨i, hi | hi⟩ := h
  all_goals
    have hv := congrArg (fun t : unitInterval => (t : ℝ)) hi
    by_cases hi0 : i = 0 <;> norm_num [axisCubeTarget, hi0] at hv

theorem axis_repetition_fiber_other_coordinate (n d : ℕ)
    (u : {u : Fin (n + 1) → unitInterval //
      repeatGenLoop (0 : Fin (n + 1)) (sphereGenerator (n + 1)) d u = axisSphereTarget n})
    (j : Fin (n + 1)) (hj : j ≠ 0) : (u.val j : ℝ) = 1 / 2 := by
  have hp : ∀ v : {v : Fin (n + 1) → unitInterval //
      sphereGenerator (n + 1) v = axisSphereTarget n}, v.val j = axisCubeTarget n j := by
    intro v
    letI : Subsingleton {v : Fin (n + 1) → unitInterval //
      sphereGenerator (n + 1) v = axisSphereTarget n} :=
      subsingleton_cubeToSphere_fiber n _ (axisSphereTarget_ne_basepoint n)
    exact congrArg (fun w => w.val j) (Subsingleton.elim v ⟨axisCubeTarget n, rfl⟩)
  have he := repeatGenLoop_fiber_coordinate_of_ne 0 j hj (sphereGenerator (n + 1))
    (axisSphereTarget_ne_basepoint n) (axisCubeTarget n j) hp d u
  have hv := congrArg (fun t : unitInterval => (t : ℝ)) he
  simpa only [axisCubeTarget, if_neg hj] using hv

theorem axis_repetition_fiber_first_ne_half (n d : ℕ)
    (u : {u : Fin (n + 1) → unitInterval //
      repeatGenLoop (0 : Fin (n + 1)) (sphereGenerator (n + 1)) d u = axisSphereTarget n}) :
    (u.val 0 : ℝ) ≠ 1 / 2 :=
  repeatGenLoop_fiber_coordinate_ne_half 0 _ (axisSphereTarget_ne_basepoint n) d u

end SphereGenerator
end BanachIsometric

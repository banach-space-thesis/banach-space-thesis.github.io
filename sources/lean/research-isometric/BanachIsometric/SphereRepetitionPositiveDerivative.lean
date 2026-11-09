import BanachIsometric.SphereRepetitionDerivativeSteps
import BanachIsometric.GenLoopFiberInterior

/-! Every branch over the specified non-pole anchor has positive actual
Jacobian. This induction uses literal strip identities and genuine local
charts, without assuming a degree or orientation law for concatenation. -/

namespace BanachIsometric.SphereGenerator

open scoped Topology Topology.Homotopy unitInterval

noncomputable section

theorem repetition_fiber_cube_axis (n d : ℕ)
    (u : {u : Fin (n + 1) → unitInterval //
      repeatGenLoop (0 : Fin (n + 1)) (sphereGenerator (n + 1)) d u = axisSphereTarget n}) :
    (fun i => (u.val i : ℝ)) = cubeCoordinateAxis n (u.val 0 : ℝ) := by
  ext i
  induction i using Fin.cases with
  | zero => rfl
  | succ i =>
    exact axis_repetition_fiber_other_coordinate n d u i.succ (Fin.succ_ne_zero i)

theorem stripChart_left_cons (n : ℕ) (ρ : ℝ) (u : Fin (n + 1) → unitInterval)
    (hu : (u 0 : ℝ) ≤ 1 / 2) :
    stripChart n 0 (Fin.cons ρ (fun i => (u i : ℝ))) =
      Fin.cons ρ (fun i => (leftExpandCube 0 u i : ℝ)) := by
  have hm := stripChart_left_cubeTailOfMem (Fin.cons ρ (fun i => (u i : ℝ)))
    (fun i => (u i).property) hu
  exact hm

theorem stripChart_right_cons (n : ℕ) (ρ : ℝ) (u : Fin (n + 1) → unitInterval)
    (hu : 1 / 2 ≤ (u 0 : ℝ)) :
    stripChart n 1 (Fin.cons ρ (fun i => (u i : ℝ))) =
      Fin.cons ρ (fun i => (rightExpandCube 0 u i : ℝ)) := by
  have hm := stripChart_right_cubeTailOfMem (Fin.cons ρ (fun i => (u i : ℝ)))
    (fun i => (u i).property) hu
  exact hm

theorem sphereRepetitionCone_positive_at_axis_fiber (n d : ℕ) (ρ : ℝ) (hρ : 0 < ρ)
    (u : {u : Fin (n + 1) → unitInterval //
      repeatGenLoop (0 : Fin (n + 1)) (sphereGenerator (n + 1)) d u = axisSphereTarget n}) :
    DifferentiableAt ℝ (sphereRepetitionCone n d)
        (cubeSphereConeChart n (Fin.cons ρ (fun i => (u.val i : ℝ)))) ∧
      0 < (fderiv ℝ (sphereRepetitionCone n d)
        (cubeSphereConeChart n (Fin.cons ρ (fun i => (u.val i : ℝ))))).det := by
  induction d with
  | zero => exact (axisSphereTarget_ne_basepoint n u.property.symm).elim
  | succ d ih =>
    let a : ℝ := u.val 0
    have huaxis : (Fin.cons ρ (fun i => (u.val i : ℝ)) : PiolaSpace (n + 2)) =
        cubeSphereConeAxis n ρ a := by rw [repetition_fiber_cube_axis]; rfl
    have ha := genLoop_fiber_coordinate_mem_Ioo
      (repeatGenLoop (0 : Fin (n + 1)) (sphereGenerator (n + 1)) (d + 1))
      (axisSphereTarget_ne_basepoint n) u.val u.property 0
    have hne : a ≠ 1 / 2 := axis_repetition_fiber_first_ne_half n (d + 1) u
    rw [huaxis]
    by_cases hleft : a < 1 / 2
    · have hv : repeatGenLoop (0 : Fin (n + 1)) (sphereGenerator (n + 1)) d
          (leftExpandCube 0 u.val) = axisSphereTarget n := by
        have he := u.property
        have huleft : (u.val 0 : ℝ) ≤ 1 / 2 := hleft.le
        simpa only [repeatGenLoop_succ, GenLoop.transAt, GenLoop.coe_copy, if_pos huleft] using he
      let v : {v : Fin (n + 1) → unitInterval //
          repeatGenLoop (0 : Fin (n + 1)) (sphereGenerator (n + 1)) d v = axisSphereTarget n} :=
        ⟨leftExpandCube 0 u.val, hv⟩
      have hstrip := stripChart_left_cons n ρ u.val hleft.le
      rw [huaxis, stripChart_axis, sub_zero] at hstrip
      have hb : 2 * a ≠ 1 / 2 := by
        have he := congrArg (fun z : PiolaSpace (n + 2) => z (0 : Fin (n + 1)).succ) hstrip
        change 2 * a = (v.val 0 : ℝ) at he
        rw [he]
        exact axis_repetition_fiber_first_ne_half n d v
      have hih := ih v
      change DifferentiableAt ℝ (sphereRepetitionCone n d)
          (cubeSphereConeChart n (Fin.cons ρ (fun i => (v.val i : ℝ)))) ∧ _ at hih
      rw [← hstrip] at hih
      exact sphereRepetitionCone_positive_left_step n d ρ a hρ ha.1 hleft hb hih.1 hih.2
    · have hright : 1 / 2 < a := lt_of_le_of_ne (le_of_not_gt hleft) (Ne.symm hne)
      have hv : cubeToSphere (n + 1) (rightExpandCube 0 u.val) = axisSphereTarget n := by
        have he := u.property
        have huright : ¬ (u.val 0 : ℝ) ≤ 1 / 2 := not_le.mpr hright
        simpa only [repeatGenLoop_succ, GenLoop.transAt, GenLoop.coe_copy,
          if_neg huright] using he
      have hv' := cubeToSphere_axisTarget_fiber_eq n _ hv
      have hstrip := stripChart_right_cons n ρ u.val hright.le
      rw [huaxis, stripChart_axis, hv'] at hstrip
      have hbvalue : 2 * a - 1 = (1 / 3 : ℝ) := by
        have he := congrArg (fun z : PiolaSpace (n + 2) => z (0 : Fin (n + 1)).succ) hstrip
        simpa [cubeSphereConeAxis, cubeCoordinateAxis, axisCubeTarget] using he
      apply sphereRepetitionCone_positive_right_step n d ρ a hρ hright ha.2
      rw [hbvalue]
      norm_num

end
end BanachIsometric.SphereGenerator

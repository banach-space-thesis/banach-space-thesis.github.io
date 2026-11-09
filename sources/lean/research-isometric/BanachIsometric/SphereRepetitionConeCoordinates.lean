import BanachIsometric.CubeSphereConeChart
import BanachIsometric.SphereConeCount
import BanachIsometric.ConeGeometry
import BanachIsometric.SphereRepetitionFiberCoordinates
import BanachIsometric.TwoCoordinateBlockDeterminant

/-! # Literal cone identities and actual affine strip maps for sphere repetition -/

namespace BanachIsometric.SphereGenerator

open NormedSpace
open scoped Topology Topology.Homotopy unitInterval

noncomputable section

def sphereRepetitionCone (n d : ℕ) : PiolaSpace (n + 2) → PiolaSpace (n + 2) :=
  coordinateMapConjugate (euclideanCoordinates (n + 2)) (unitSphereCone (sphereRepetition n d))

theorem sphereRepetitionCone_cubeChart (n d : ℕ) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (u : Fin (n + 1) → unitInterval) :
    sphereRepetitionCone n d (cubeSphereConeChart n (Fin.cons ρ (fun i => (u i : ℝ)))) =
      euclideanCoordinates (n + 2)
        (ρ • ((repeatGenLoop (0 : Fin (n + 1)) (sphereGenerator (n + 1)) d) u).val) := by
  have hφ : sphereRepetition n d (cubeToSphere (n + 1) u) =
      (repeatGenLoop (0 : Fin (n + 1)) (sphereGenerator (n + 1)) d) u := by
    exact congrArg (fun f : C((Fin (n + 1) → unitInterval), Sph (n + 1)) => f u)
      (sphereRepetition_comp_cubeToSphere n d)
  rw [cubeSphereConeChart_eq_raw, sphereRepetitionCone, coordinateMapConjugate,
    ContinuousLinearEquiv.symm_apply_apply]
  rw [unitSphereCone, coneExtension_smul_nonneg _ hρ, coneExtension_unit, hφ]

theorem sphereRepetitionCone_cubeChart_left (n d : ℕ) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (u : Fin (n + 1) → unitInterval) (hu : (u 0 : ℝ) ≤ 1 / 2) :
    sphereRepetitionCone n (d + 1) (cubeSphereConeChart n (Fin.cons ρ (fun i => (u i : ℝ)))) =
      sphereRepetitionCone n d
        (cubeSphereConeChart n (Fin.cons ρ (fun i => (leftExpandCube 0 u i : ℝ)))) := by
  rw [sphereRepetitionCone_cubeChart n (d + 1) hρ, sphereRepetitionCone_cubeChart n d hρ]
  apply congrArg (fun z : Sph (n + 1) => euclideanCoordinates (n + 2) (ρ • z.val))
  simp only [repeatGenLoop_succ, GenLoop.transAt, GenLoop.coe_copy, if_pos hu]
  rfl

theorem sphereRepetitionCone_cubeChart_right (n d : ℕ) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (u : Fin (n + 1) → unitInterval) (hu : 1 / 2 < (u 0 : ℝ)) :
    sphereRepetitionCone n (d + 1) (cubeSphereConeChart n (Fin.cons ρ (fun i => (u i : ℝ)))) =
      cubeSphereConeChart n (Fin.cons ρ (fun i => (rightExpandCube 0 u i : ℝ))) := by
  rw [sphereRepetitionCone_cubeChart n (d + 1) hρ, cubeSphereConeChart_eq_raw]
  apply congrArg (fun z : Sph (n + 1) => euclideanCoordinates (n + 2) (ρ • z.val))
  simp only [repeatGenLoop_succ, GenLoop.transAt, GenLoop.coe_copy, if_neg (not_le.mpr hu)]
  rfl

def stripChartLinear (n : ℕ) : PiolaSpace (n + 2) →L[ℝ] PiolaSpace (n + 2) :=
  (prefixTwoBlockLinear n 1 0 0 2 1).toContinuousLinearMap

def stripChart (n : ℕ) (ε : ℝ) (z : PiolaSpace (n + 2)) : PiolaSpace (n + 2) :=
  stripChartLinear n z - ε • piolaBasisVector (0 : Fin (n + 1)).succ

@[simp] theorem stripChart_zero (n : ℕ) (ε : ℝ) (z : PiolaSpace (n + 2)) :
    stripChart n ε z 0 = z 0 := by
  simp [stripChart, stripChartLinear, prefixTwoBlockLinear, piolaBasisVector]

@[simp] theorem stripChart_one (n : ℕ) (ε : ℝ) (z : PiolaSpace (n + 2)) :
    stripChart n ε z (0 : Fin (n + 1)).succ = 2 * z (0 : Fin (n + 1)).succ - ε := by
  simp [stripChart, stripChartLinear, prefixTwoBlockLinear, piolaBasisVector]

@[simp] theorem stripChart_succ_succ (n : ℕ) (ε : ℝ) (z : PiolaSpace (n + 2)) (j : Fin n) :
    stripChart n ε z j.succ.succ = z j.succ.succ := by
  have hj : j.succ.succ ≠ (1 : Fin (n + 2)) := by
    intro h
    have hv := congrArg Fin.val h
    simp at hv
  simp [stripChart, stripChartLinear, prefixTwoBlockLinear, piolaBasisVector, hj]

theorem stripChart_axis (n : ℕ) (ε ρ a : ℝ) :
    stripChart n ε (cubeSphereConeAxis n ρ a) = cubeSphereConeAxis n ρ (2 * a - ε) := by
  funext i
  induction i using Fin.cases with
  | zero => simp [cubeSphereConeAxis]
  | succ j =>
    induction j using Fin.cases with
    | zero =>
      rw [stripChart_one]
      rfl
    | succ j => simp [cubeSphereConeAxis, cubeCoordinateAxis]

theorem hasFDerivAt_stripChart (n : ℕ) (ε : ℝ) (z : PiolaSpace (n + 2)) :
    HasFDerivAt (stripChart n ε) (stripChartLinear n) z :=
  (stripChartLinear n).hasFDerivAt.sub_const (ε • piolaBasisVector (0 : Fin (n + 1)).succ)

theorem det_stripChartLinear (n : ℕ) : (stripChartLinear n).det = 2 := by
  change (prefixTwoBlockLinear n 1 0 0 2 1).det = 2
  rw [det_prefixTwoBlockLinear]
  norm_num

end
end BanachIsometric.SphereGenerator

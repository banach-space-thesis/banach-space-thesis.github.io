import BanachIsometric.DiskSphereConeJacobian
import BanachIsometric.TwoCoordinateBlockDeterminant

/-!
# Negative actual Jacobian of the disk-sphere cone chart on its regular axis

An actual linear coordinate splitting conjugates the derivative to its first
two-coordinate block and its scalar tail. Determinant conjugacy cancels the
coordinate splitting itself, so no orientation premise is introduced.
-/

namespace BanachIsometric.SphereGenerator

open scoped Matrix

noncomputable section

def diskSphereConeBlock (ρ r : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  let s := Real.sqrt (1 - r ^ 2)
  !![2 * r ^ 2 - 1, 4 * ρ * r;
    2 * s * r, 2 * ρ * s - 2 * ρ * r ^ 2 / s]

theorem diskSphereConeChartDerivative_eq_prefixTwoBlock (n : ℕ) (ρ r : ℝ) :
    (diskSphereConeChartDerivative n ρ r).toLinearMap =
      prefixTwoBlockLinear n (2 * r ^ 2 - 1) (4 * ρ * r)
        (2 * Real.sqrt (1 - r ^ 2) * r)
        (2 * ρ * Real.sqrt (1 - r ^ 2) - 2 * ρ * r ^ 2 / Real.sqrt (1 - r ^ 2))
        (2 * ρ * Real.sqrt (1 - r ^ 2)) := by
  ext z i
  induction i using Fin.cases with
  | zero => simp [diskSphereConeChartDerivative, prefixTwoBlockLinear]
  | succ i =>
    induction i using Fin.cases with
    | zero => simp [diskSphereConeChartDerivative, prefixTwoBlockLinear]
    | succ j => simp [diskSphereConeChartDerivative, prefixTwoBlockLinear]

theorem det_diskSphereConeChartDerivative (n : ℕ) (ρ r : ℝ) :
    (diskSphereConeChartDerivative n ρ r).det =
      (diskSphereConeBlock ρ r).det * (2 * ρ * Real.sqrt (1 - r ^ 2)) ^ n := by
  change (diskSphereConeChartDerivative n ρ r).toLinearMap.det = _
  rw [diskSphereConeChartDerivative_eq_prefixTwoBlock, det_prefixTwoBlockLinear]
  rw [diskSphereConeBlock, Matrix.det_fin_two]
  rfl

theorem det_diskSphereConeBlock (ρ r : ℝ) (hr : r ^ 2 < 1) :
    (diskSphereConeBlock ρ r).det = -2 * ρ / Real.sqrt (1 - r ^ 2) := by
  have hs : Real.sqrt (1 - r ^ 2) ≠ 0 := (Real.sqrt_pos.mpr (sub_pos.mpr hr)).ne'
  have hs2 := Real.sq_sqrt (sub_pos.mpr hr).le
  rw [Matrix.det_fin_two]
  change (2 * r ^ 2 - 1) *
    (2 * ρ * Real.sqrt (1 - r ^ 2) - 2 * ρ * r ^ 2 / Real.sqrt (1 - r ^ 2)) -
    (4 * ρ * r) * (2 * Real.sqrt (1 - r ^ 2) * r) = -2 * ρ / Real.sqrt (1 - r ^ 2)
  field_simp [hs]
  linear_combination -ρ * (2 * r ^ 2 + 1) * hs2

theorem det_fderiv_diskSphereConeChart_neg (n : ℕ) (ρ r : ℝ) (hρ : 0 < ρ) (hr : r ^ 2 < 1) :
    (fderiv ℝ (diskSphereConeChart n) (diskSphereConeAxis n ρ r)).det < 0 := by
  rw [(hasFDerivAt_diskSphereConeChart_axis n ρ r hr).fderiv,
    det_diskSphereConeChartDerivative, det_diskSphereConeBlock ρ r hr]
  have hs : 0 < Real.sqrt (1 - r ^ 2) := Real.sqrt_pos.mpr (sub_pos.mpr hr)
  apply mul_neg_of_neg_of_pos
  · exact div_neg_of_neg_of_pos (by nlinarith) hs
  · exact pow_pos (by positivity) n

end

end BanachIsometric.SphereGenerator

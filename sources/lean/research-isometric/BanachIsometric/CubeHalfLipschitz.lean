import BanachIsometric.CubeHalfCoordinates
import Mathlib.Topology.MetricSpace.Lipschitz

/-! The actual clamped affine expansion maps used in cubical concatenation
are globally Lipschitz for the existing finite cube metric. -/

noncomputable section
namespace BanachIsometric
open Set Metric
open scoped NNReal unitInterval

variable {N : Type*} [DecidableEq N] [Fintype N]

def expandAffineCube (i : N) (b : ℝ) (u : N → unitInterval) : N → unitInterval :=
  Function.update u i (Set.projIcc 0 1 zero_le_one (2 * (u i : ℝ) + b))

theorem lipschitz_expandAffineCube (i : N) (b : ℝ) : LipschitzWith 2 (expandAffineCube i b) := by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  apply (dist_pi_le_iff (by positivity)).mpr
  intro j
  have hcoord : dist (u j) (v j) ≤ dist u v := by
    simpa only [NNReal.coe_one, one_mul] using (LipschitzWith.eval j).dist_le_mul u v
  by_cases hj : j = i
  · subst j
    simp only [expandAffineCube, Function.update_self]
    have hclamp := (LipschitzWith.projIcc (zero_le_one : (0 : ℝ) ≤ 1)).dist_le_mul
      (2 * (u i : ℝ) + b) (2 * (v i : ℝ) + b)
    rw [NNReal.coe_one, one_mul] at hclamp
    calc
      _ ≤ dist (2 * (u i : ℝ) + b) (2 * (v i : ℝ) + b) := hclamp
      _ = 2 * dist (u i) (v i) := by
        rw [Real.dist_eq, Subtype.dist_eq, Real.dist_eq,
          show 2 * (u i : ℝ) + b - (2 * (v i : ℝ) + b) =
            2 * ((u i : ℝ) - (v i : ℝ)) by ring,
          abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      _ ≤ (2 : ℝ≥0) * dist u v := by exact mul_le_mul_of_nonneg_left hcoord (by norm_num)
  · simp only [expandAffineCube, Function.update_of_ne hj]
    exact hcoord.trans (by norm_num; linarith [dist_nonneg (x := u) (y := v)])

theorem lipschitz_leftExpandCube (i : N) : LipschitzWith 2 (leftExpandCube i) := by
  have he : expandAffineCube i 0 = leftExpandCube i := by
    funext u
    simp only [expandAffineCube, leftExpandCube, add_zero]
  rw [← he]
  exact lipschitz_expandAffineCube i 0

theorem lipschitz_rightExpandCube (i : N) : LipschitzWith 2 (rightExpandCube i) := by
  have he : expandAffineCube i (-1) = rightExpandCube i := by
    funext u
    simp only [expandAffineCube, rightExpandCube, sub_eq_add_neg]
  rw [← he]
  exact lipschitz_expandAffineCube i (-1)

end BanachIsometric

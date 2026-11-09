import PL1.Definitions
import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Operators defined by uniformly bounded columns on an actual ell1 sum

This is a general analytic construction used for K and the matrix projection.
The columns are supplied as continuous linear maps; their uniform bound is
an explicit hypothesis, to be discharged by the dyadic resolvent estimates.
-/

noncomputable section
open Filter
open scoped Topology ENNReal

namespace PL1

abbrev L1Sum (Y : Type*) [NormedAddCommGroup Y] := lp (fun _ : ℕ => Y) 1

namespace L1Sum

variable {𝕜 Y Z : Type*} [RCLike 𝕜]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  [NormedAddCommGroup Z] [NormedSpace 𝕜 Z] [CompleteSpace Z]

theorem summable_norm (x : L1Sum Y) : Summable (fun n => ‖x n‖) := by
  simpa using (lp.memℓp x).summable (by simp : (0 : ℝ) < (1 : ℝ≥0∞).toReal)

theorem norm_eq_tsum (x : L1Sum Y) : ‖x‖ = ∑' n, ‖x n‖ := by
  simpa using lp.norm_eq_tsum_rpow (by simp : (0 : ℝ) < (1 : ℝ≥0∞).toReal) x

variable (T : ℕ → Y →L[𝕜] Z) (C : ℝ) (hT : ∀ n, ‖T n‖ ≤ C)

include hT

omit [CompleteSpace Z] in
theorem column_norm_le (x : L1Sum Y) (n : ℕ) :
    ‖T n (x n)‖ ≤ C * ‖x n‖ :=
  (T n).le_opNorm (x n) |>.trans
    (mul_le_mul_of_nonneg_right (hT n) (norm_nonneg _))

theorem summable_norm_columns (x : L1Sum Y) :
    Summable (fun n => ‖T n (x n)‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (column_norm_le T C hT x)
    ((summable_norm x).mul_left C)

theorem summable_columns (x : L1Sum Y) :
    Summable (fun n => T n (x n)) :=
  (summable_norm_columns T C hT x).of_norm

theorem norm_tsum_columns_le (x : L1Sum Y) :
    ‖∑' n, T n (x n)‖ ≤ C * ‖x‖ := by
  calc
    ‖∑' n, T n (x n)‖ ≤ ∑' n, ‖T n (x n)‖ :=
      norm_tsum_le_tsum_norm (summable_norm_columns T C hT x)
    _ ≤ ∑' n, C * ‖x n‖ :=
      Summable.tsum_le_tsum (column_norm_le T C hT x)
        (summable_norm_columns T C hT x) ((summable_norm x).mul_left C)
    _ = C * ‖x‖ := by rw [tsum_mul_left, norm_eq_tsum]

/-- Synthesis of an ell1 input by uniformly bounded operator columns. -/
def synthesis : L1Sum Y →L[𝕜] Z :=
  LinearMap.mkContinuous
    { toFun := fun x => ∑' n, T n (x n)
      map_add' := by
        intro x y
        simp only [lp.coeFn_add, Pi.add_apply, map_add]
        exact (summable_columns T C hT x).tsum_add (summable_columns T C hT y)
      map_smul' := by
        intro c x
        simp only [lp.coeFn_smul, Pi.smul_apply, map_smul, RingHom.id_apply]
        exact (summable_columns T C hT x).tsum_const_smul c }
    C (norm_tsum_columns_le T C hT)

@[simp]
theorem synthesis_apply (x : L1Sum Y) :
    synthesis T C hT x = ∑' n, T n (x n) := rfl

theorem norm_synthesis_le (hC : 0 ≤ C) : ‖synthesis T C hT‖ ≤ C :=
  ContinuousLinearMap.opNorm_le_bound _ hC (norm_tsum_columns_le T C hT)

@[simp]
theorem synthesis_single (j : ℕ) (y : Y) :
    synthesis T C hT (lp.single 1 j y) = T j y := by
  rw [synthesis_apply, tsum_eq_single j]
  · simp
  · intro n hn
    simp [Pi.single_eq_of_ne hn]

end L1Sum
end PL1

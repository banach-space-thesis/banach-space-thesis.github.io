import BanachIsometric.AffineSingularSimplex
import Mathlib.Analysis.Normed.Module.Basic

/-! Affine simplices are Lipschitz in the actual barycentric coordinates. -/

noncomputable section
namespace BanachIsometric.SingularPrism

open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_lipschitz_affineSingularSimplex {n : ℕ} (v : Fin (n + 1) → E) :
    ∃ L : ℝ≥0, LipschitzWith L (affineSingularSimplex v) := by
  refine ⟨∑ i, ‖v i‖₊, LipschitzWith.of_dist_le_mul ?_⟩
  intro w z
  change dist (∑ i, w.val i • v i) (∑ i, z.val i • v i) ≤ _
  rw [dist_eq_norm, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, ‖w.val i • v i - z.val i • v i‖ := norm_sum_le _ _
    _ = ∑ i, dist (w.val i) (z.val i) * ‖v i‖ := by
      simp_rw [← sub_smul, norm_smul, dist_eq_norm]
    _ ≤ ∑ i, dist w z * ‖v i‖ := Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_right (dist_le_pi_dist w.val z.val i) (norm_nonneg _)
    _ = _ := by simp [Finset.sum_mul, mul_comm (dist w z)]

end BanachIsometric.SingularPrism

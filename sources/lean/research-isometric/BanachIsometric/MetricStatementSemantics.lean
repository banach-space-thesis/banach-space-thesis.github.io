import BanachIsometric.MetricGaugeIsometries
import Mathlib.LinearAlgebra.Dimension.Free

/-! Direct semantic checks for the metric theorem: finite dimensions in the
internal convenient finrank formulation mean exactly the paper's rank-n
subspaces, and the gauge is literally its displayed infimum. -/

namespace BanachIsometric.MetricGeometry

open Set
open scoped Pointwise

noncomputable section

variable {R X : Type*} [DivisionRing R] [AddCommGroup X] [Module R X] [MetricSpace X]

theorem linearMetricSubspaceHomogeneity_iff_rank {n : ℕ} (hn : 0 < n) :
    LinearMetricSubspaceHomogeneity (R := R) (X := X) n ↔
      ∀ E F : Submodule R X, Module.rank R E = (n : Cardinal) → Module.rank R F = (n : Cardinal) →
        ∃ T : E ≃ₗ[R] F, Isometry T := by
  constructor
  · intro h E F hE hF
    exact h E F (Module.finrank_eq_of_rank_eq hE) (Module.finrank_eq_of_rank_eq hF)
  · intro h E F hE hF
    letI : Module.Finite R E := Module.finite_of_finrank_pos (by rw [hE]; exact hn)
    letI : Module.Finite R F := Module.finite_of_finrank_pos (by rw [hF]; exact hn)
    apply h E F
    · rw [← Module.finrank_eq_rank, hE]
    · rw [← Module.finrank_eq_rank, hF]

omit [Module R X] in
theorem translationInvariant_iff_dist_sub_zero : TranslationInvariant (X := X) ↔
    ∀ x y : X, dist x y = dist (x - y) 0 := by
  constructor
  · exact dist_eq_dist_sub_zero
  · intro h x y z
    rw [h (x + z) (y + z), add_sub_add_right_eq_sub, ← h x y]

variable [Module ℝ X]

theorem centeredBallGauge_eq_minkowski_inf (r : ℝ) (x : X) :
    centeredBallGauge r x = sInf {t : ℝ | 0 < t ∧ x ∈ t • Metric.closedBall (0 : X) r} := rfl

end
end BanachIsometric.MetricGeometry

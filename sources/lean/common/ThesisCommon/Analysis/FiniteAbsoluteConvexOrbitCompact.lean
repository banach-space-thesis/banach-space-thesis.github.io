import ThesisCommon.Analysis.FiniteAbsoluteConvexOrbit
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.RCLike.Lemmas

/-! Compactness of an actual finite absolute-convex orbit, even in an
infinite-dimensional target. Its coefficient budget is a compact subset
of the genuine finite scalar product. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon
variable {𝕜 X ι : Type*} [RCLike 𝕜] [NormedAddCommGroup X]
  [NormedSpace 𝕜 X] [Fintype ι]

theorem isCompact_finiteAbsoluteConvexOrbit (v : ι → X) (m : ℝ) :
    IsCompact (finiteAbsoluteConvexOrbit (𝕜 := 𝕜) v m) := by
  classical
  letI : ProperSpace 𝕜 := FiniteDimensional.proper_rclike 𝕜 𝕜
  let C : Set (ι → 𝕜) := {c | (∑ i, ‖c i‖) ≤ m}
  have hCclosed : IsClosed C :=
    isClosed_le (continuous_finset_sum _ (fun i _ => (continuous_apply i).norm)) continuous_const
  have hCcompact : IsCompact C := by
    by_cases hm : 0 ≤ m
    · apply (isCompact_closedBall (0 : ι → 𝕜) m).of_isClosed_subset hCclosed
      intro c hc
      rw [Metric.mem_closedBall, dist_zero_right]
      apply (pi_norm_le_iff_of_nonneg hm).mpr
      intro i
      exact (Finset.single_le_sum (fun j _ => norm_nonneg (c j))
        (Finset.mem_univ i)).trans hc
    · have hCempty : C = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro c hc
        have hsum : 0 ≤ ∑ i, ‖c i‖ := Finset.sum_nonneg (fun i _ => norm_nonneg _)
        exact hm (hsum.trans hc)
      rw [hCempty]
      exact isCompact_empty
  have hcont : Continuous (fun c : ι → 𝕜 => ∑ i, c i • v i) :=
    continuous_finset_sum _ (fun i _ => (continuous_apply i).smul continuous_const)
  have he : finiteAbsoluteConvexOrbit (𝕜 := 𝕜) v m =
      (fun c : ι → 𝕜 => ∑ i, c i • v i) '' C := by
    ext x
    rfl
  rw [he]
  exact hCcompact.image hcont

end ThesisCommon

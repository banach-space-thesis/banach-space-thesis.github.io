import PosetsCommon.CZeroSum
import Mathlib.Order.Filter.AtTopBot.Finset

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
open Filter Topology
open scoped ENNReal
namespace ThesisCommon
variable (𝕜 : Type*) [RCLike 𝕜] {P : Type*}
variable (X : P → Type*) [∀ p, NormedAddCommGroup (X p)] [∀ p, NormedSpace 𝕜 (X p)]

/-- Retain precisely the finitely many coordinates in s. -/
def finiteProjection (s : Finset P) : DependentCZeroSum 𝕜 X →L[𝕜] DependentCZeroSum 𝕜 X :=
  ∑ p ∈ s, (sumInjection 𝕜 X p).comp (sumProjection 𝕜 X p)

theorem finiteProjection_apply (s : Finset P) (x : DependentCZeroSum 𝕜 X) (q : P) :
    (finiteProjection 𝕜 X s x).val q = if q ∈ s then x.val q else 0 := by
  classical
  simp [finiteProjection, sumInjection, sumProjection, Finset.sum_pi_single]

theorem finiteProjection_norm_le (s : Finset P) (x : DependentCZeroSum 𝕜 X) :
    ‖finiteProjection 𝕜 X s x‖ ≤ ‖x‖ := by
  apply lp.norm_le_of_forall_le (norm_nonneg x)
  intro q
  change ‖(finiteProjection 𝕜 X s x).val q‖ ≤ ‖x‖
  rw [finiteProjection_apply]
  split_ifs
  · exact lp.norm_apply_le_norm ENNReal.top_ne_zero x.val q
  · simp

/-- The net of finite truncations converges in norm, directly from vanishing
at infinity. No separability or completeness of the coordinate spaces is needed. -/
theorem finiteProjection_tendsto (x : DependentCZeroSum 𝕜 X) :
    Tendsto (fun s : Finset P => finiteProjection 𝕜 X s x) atTop (𝓝 x) := by
  classical
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hsmall := (Metric.tendsto_nhds.mp x.property) (ε / 2) (half_pos hε)
  have hfinite := eventually_cofinite.mp hsmall
  filter_upwards [eventually_ge_atTop hfinite.toFinset] with s hs
  rw [dist_eq_norm]
  apply lt_of_le_of_lt (lp.norm_le_of_forall_le (le_of_lt (half_pos hε)) ?_)
    (half_lt_self hε)
  intro q
  change ‖(finiteProjection 𝕜 X s x).val q - x.val q‖ ≤ ε / 2
  rw [finiteProjection_apply]
  split_ifs with hq
  · simpa using le_of_lt (half_pos hε)
  · have hq' : q ∉ hfinite.toFinset := fun h => hq (hs h)
    have hsmallq : dist ‖x.val q‖ 0 < ε / 2 := by
      simpa only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] using hq'
    simpa using hsmallq.le

theorem rangeProjection_tendsto (X : ℕ → Type*)
    [∀ n, NormedAddCommGroup (X n)] [∀ n, NormedSpace 𝕜 (X n)]
    (x : DependentCZeroSum 𝕜 X) :
    Tendsto (fun n => finiteProjection 𝕜 X (Finset.range n) x) atTop (𝓝 x) :=
  (finiteProjection_tendsto 𝕜 X x).comp tendsto_finset_range

end ThesisCommon

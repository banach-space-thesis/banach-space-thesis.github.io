import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Order.Filter.AtTopBot.Finset

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
open Filter Topology TopologicalSpace
open scoped ZeroAtInfty
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜] {P : Type*} [TopologicalSpace P] [DiscreteTopology P]

def discreteUnit (p : P) : C₀(P, 𝕜) where
  toFun := Set.indicator {p} (fun _ => 1)
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := by
    apply tendsto_const_nhds.congr'
    filter_upwards [(isCompact_singleton (x := p)).compl_mem_cocompact] with q hq
    exact (Set.indicator_of_notMem hq _).symm

@[simp] theorem discreteUnit_apply (p q : P) :
    discreteUnit (𝕜 := 𝕜) p q = if q = p then 1 else 0 := by
  classical
  simp [discreteUnit, Set.indicator_apply]

def discreteTruncation (F : Finset P) (f : C₀(P, 𝕜)) : C₀(P, 𝕜) :=
  ∑ p ∈ F, f p • discreteUnit p

theorem discreteTruncation_apply (F : Finset P) (f : C₀(P, 𝕜)) (q : P) :
    discreteTruncation F f q = if q ∈ F then f q else 0 := by
  classical
  induction F using Finset.induction_on with
  | empty => simp [discreteTruncation]
  | @insert p F hp ih =>
    simp only [discreteTruncation, Finset.sum_insert hp,
      ZeroAtInftyContinuousMap.add_apply, ZeroAtInftyContinuousMap.smul_apply,
      discreteUnit_apply, smul_eq_mul]
    change f p * (if q = p then 1 else 0) + discreteTruncation F f q = _
    rw [ih]
    by_cases hqp : q = p <;> simp [hqp, hp]

/-- Finite-support truncations converge in the supremum norm. -/
theorem discreteTruncation_tendsto (f : C₀(P, 𝕜)) :
    Tendsto (fun F : Finset P => discreteTruncation F f) atTop (𝓝 f) := by
  classical
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hsmall := Metric.tendsto_nhds.mp (zero_at_infty f) (ε / 2) (half_pos hε)
  rw [cocompact_eq_cofinite] at hsmall
  have hfinite := eventually_cofinite.mp hsmall
  filter_upwards [eventually_ge_atTop hfinite.toFinset] with F hF
  rw [dist_eq_norm]
  apply lt_of_le_of_lt ((BoundedContinuousFunction.norm_le (le_of_lt (half_pos hε))).mpr ?_)
    (half_lt_self hε)
  intro p
  change ‖discreteTruncation F f p - f p‖ ≤ ε / 2
  rw [discreteTruncation_apply]
  by_cases hp : p ∈ F
  · simpa [hp] using (half_pos hε).le
  · have hp' : p ∉ hfinite.toFinset := fun h => hp (hF h)
    have hs : dist (f p) 0 < ε / 2 := by
      simpa only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] using hp'
    simpa [hp] using hs.le

theorem discreteUnit_dense_span :
    Dense (Submodule.span 𝕜 (Set.range (discreteUnit (𝕜 := 𝕜) (P := P))) : Set C₀(P, 𝕜)) := by
  intro f
  apply isClosed_closure.mem_of_tendsto (discreteTruncation_tendsto f)
  apply Filter.Eventually.of_forall
  intro F
  apply subset_closure
  exact Submodule.sum_mem _ (fun p _ => Submodule.smul_mem _ _
    (Submodule.subset_span (Set.mem_range_self p)))

theorem discreteCZero_separable [Countable P] : SeparableSpace C₀(P, 𝕜) := by
  apply isSeparable_univ_iff.mp
  have hs := ((Set.countable_range (discreteUnit (𝕜 := 𝕜) (P := P))).isSeparable.span
    (R := 𝕜)).closure
  rwa [discreteUnit_dense_span.closure_eq] at hs

end ThesisCommon

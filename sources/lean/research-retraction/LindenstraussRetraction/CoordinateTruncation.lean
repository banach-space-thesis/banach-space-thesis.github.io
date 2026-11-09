import LindenstraussRetraction.SummationSpace
import Mathlib.Topology.Instances.Nat
import Mathlib.Tactic.Linarith

/-! Contractive coordinate truncations on c₀, including norm convergence. -/

noncomputable section

open scoped ZeroAtInfty
open Filter Topology

namespace LindenstraussRetraction

universe v
variable (𝕜 : Type v) [RCLike 𝕜]

theorem c0_tendsto_zero (x : C0 𝕜) : Tendsto x atTop (𝓝 0) := by
  simpa only [Filter.cocompact_eq_cofinite, Nat.cofinite_eq_atTop] using zero_at_infty x

/-- Delete all coordinates at index `N` or later. -/
def c0Truncation (N : ℕ) (x : C0 𝕜) : C0 𝕜 where
  toFun k := if k < N then x k else 0
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := by
    rw [Filter.cocompact_eq_cofinite, Nat.cofinite_eq_atTop]
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop N] with k hk
    simp only [not_lt.mpr hk, if_false]

@[simp] theorem c0Truncation_apply (N k : ℕ) (x : C0 𝕜) :
    c0Truncation 𝕜 N x k = if k < N then x k else 0 := rfl

theorem norm_c0Truncation_le (N : ℕ) (x : C0 𝕜) :
    ‖c0Truncation 𝕜 N x‖ ≤ ‖x‖ := by
  change ‖(c0Truncation 𝕜 N x).toBCF‖ ≤ ‖x.toBCF‖
  apply (BoundedContinuousFunction.norm_le (norm_nonneg _)).2
  intro k
  change ‖if k < N then x k else 0‖ ≤ ‖x.toBCF‖
  split_ifs
  · exact x.toBCF.norm_coe_le_norm k
  · simpa only [norm_zero] using norm_nonneg x.toBCF

/-- `P_N` as a continuous linear projection on c₀. -/
def c0TruncationOperator (N : ℕ) : C0 𝕜 →L[𝕜] C0 𝕜 :=
  ({ toFun := c0Truncation 𝕜 N
     map_add' := by intro x y; ext k; by_cases hk : k < N <;> simp [hk]
     map_smul' := by intro c x; ext k; by_cases hk : k < N <;> simp [hk]
     } : C0 𝕜 →ₗ[𝕜] C0 𝕜).mkContinuous 1 (fun x => by
       simpa only [one_mul] using norm_c0Truncation_le 𝕜 N x)

@[simp] theorem c0TruncationOperator_apply (N : ℕ) (x : C0 𝕜) :
    c0TruncationOperator 𝕜 N x = c0Truncation 𝕜 N x := rfl

theorem norm_c0TruncationOperator_le (N : ℕ) : ‖c0TruncationOperator 𝕜 N‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa only [one_mul] using norm_c0Truncation_le 𝕜 N x

theorem c0Truncation_comp (N M : ℕ) (x : C0 𝕜) :
    c0Truncation 𝕜 N (c0Truncation 𝕜 M x) = c0Truncation 𝕜 (min N M) x := by
  ext k
  simp only [c0Truncation_apply, lt_min_iff]
  split_ifs <;> simp_all

theorem c0Truncation_mem (m : ℕ) (x : C0 𝕜) :
    c0Truncation 𝕜 (m+1) x ∈ finiteCoordinateSubmodule 𝕜 m := by
  intro k hk
  simp [not_lt.mpr hk]

theorem c0Truncation_fix (m : ℕ) (x : FiniteCoordinateSpace 𝕜 m) :
    c0Truncation 𝕜 (m+1) x.val = x.val := by
  ext k
  by_cases hk : k < m+1
  · simp [hk]
  · simp [hk, x.property k (Nat.le_of_not_gt hk)]

/-- The coordinate truncations converge in the supremum norm, not just pointwise. -/
theorem c0Truncation_tendsto (x : C0 𝕜) :
    Tendsto (fun N => c0Truncation 𝕜 N x) atTop (𝓝 x) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 (c0_tendsto_zero 𝕜 x))
    (ε/2) (half_pos hε)
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_eq_norm]
  have hb : ‖c0Truncation 𝕜 n x - x‖ ≤ ε/2 := by
    change ‖(c0Truncation 𝕜 n x - x).toBCF‖ ≤ ε/2
    apply (BoundedContinuousFunction.norm_le (half_pos hε).le).2
    intro k
    change ‖(if k < n then x k else 0) - x k‖ ≤ ε/2
    by_cases hk : k < n
    · simp [hk, (half_pos hε).le]
    · have hnk : N ≤ k := hn.trans (Nat.le_of_not_gt hk)
      simpa [hk, dist_zero_right] using (hN k hnk).le
  exact hb.trans_lt (half_lt_self hε)

end LindenstraussRetraction

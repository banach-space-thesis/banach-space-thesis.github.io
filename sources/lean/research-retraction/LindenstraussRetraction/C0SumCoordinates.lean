import LindenstraussRetraction.C0Sum
import LindenstraussRetraction.BidualIsometry
import Mathlib.Tactic.Positivity

/-! Contractive coordinate maps and finite truncations of the dependent c₀-sum. -/

noncomputable section
open Filter Topology
open scoped ENNReal

namespace LindenstraussRetraction

universe u v
variable (𝕜 : Type v) [RCLike 𝕜]
variable (E : ℕ → Type u) [∀ n, NormedAddCommGroup (E n)] [∀ n, NormedSpace 𝕜 (E n)]

/-- The insertion into one coordinate, with zero in every other coordinate. -/
def c0SumSingle (n : ℕ) : E n →L[𝕜] C0Sum 𝕜 E :=
  (lp.singleContinuousLinearMap 𝕜 E ∞ n).codRestrict (c0SumSubmodule 𝕜 E) (by
    intro x
    change Tendsto (fun m => ‖lp.single ∞ n x m‖) atTop (𝓝 0)
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop n] with m hm
    simp [Pi.single_eq_of_ne (ne_of_gt hm)])

theorem c0SumSingle_apply (n m : ℕ) (x : E n) :
    (c0SumSingle 𝕜 E n x).val m = Pi.single n x m := rfl

@[simp] theorem c0SumSingle_apply_self (n : ℕ) (x : E n) :
    (c0SumSingle 𝕜 E n x).val n = x := lp.single_apply_self ∞ n x

@[simp] theorem c0SumSingle_apply_ne (n m : ℕ) (x : E n) (h : m ≠ n) :
    (c0SumSingle 𝕜 E n x).val m = 0 := lp.single_apply_ne ∞ n x h

@[simp] theorem norm_c0SumSingle (n : ℕ) (x : E n) :
    ‖c0SumSingle 𝕜 E n x‖ = ‖x‖ := lp.norm_single (by simp : (0 : ℝ≥0∞) < ∞) n x

def c0SumSingleIsometry (n : ℕ) : E n →ₗᵢ[𝕜] C0Sum 𝕜 E :=
  ⟨(c0SumSingle 𝕜 E n).toLinearMap, norm_c0SumSingle 𝕜 E n⟩

/-- Evaluation at a coordinate of the dependent c₀-sum. -/
def c0SumCoordinate (n : ℕ) : C0Sum 𝕜 E →L[𝕜] E n :=
  LinearMap.mkContinuous
    { toFun := fun x => x.val n
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl } 1 (by
      intro x
      simpa only [one_mul] using c0Sum_norm_coordinate_le 𝕜 E x n)

@[simp] theorem c0SumCoordinate_apply (n : ℕ) (x : C0Sum 𝕜 E) :
    c0SumCoordinate 𝕜 E n x = x.val n := rfl

theorem c0SumCoordinate_norm_le (n : ℕ) : ‖c0SumCoordinate 𝕜 E n‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    (by intro x; simpa only [one_mul] using c0Sum_norm_coordinate_le 𝕜 E x n)

@[simp] theorem c0SumCoordinate_single (n : ℕ) (x : E n) :
    c0SumCoordinate 𝕜 E n (c0SumSingle 𝕜 E n x) = x :=
  c0SumSingle_apply_self 𝕜 E n x

/-- Retaining the first `N` coordinates. -/
def c0SumTruncation (N : ℕ) : C0Sum 𝕜 E →L[𝕜] C0Sum 𝕜 E :=
  ∑ n ∈ Finset.range N, (c0SumSingle 𝕜 E n).comp (c0SumCoordinate 𝕜 E n)

theorem c0SumTruncation_apply (N : ℕ) (x : C0Sum 𝕜 E) (m : ℕ) :
    (c0SumTruncation 𝕜 E N x).val m = if m < N then x.val m else 0 := by
  classical
  change c0SumCoordinate 𝕜 E m (c0SumTruncation 𝕜 E N x) = _
  simp only [c0SumTruncation, ContinuousLinearMap.sum_apply, map_sum,
    ContinuousLinearMap.comp_apply, c0SumCoordinate_apply]
  by_cases hm : m < N
  · rw [if_pos hm, Finset.sum_eq_single m]
    · exact lp.single_apply_self ∞ m _
    · intro n _ hnm
      exact lp.single_apply_ne ∞ n _ (Ne.symm hnm)
    · intro h
      exact (h (Finset.mem_range.mpr hm)).elim
  · rw [if_neg hm]
    apply Finset.sum_eq_zero
    intro n hn
    apply lp.single_apply_ne
    intro h
    exact hm (h ▸ Finset.mem_range.mp hn)

theorem c0SumTruncation_norm_apply_le (N : ℕ) (x : C0Sum 𝕜 E) :
    ‖c0SumTruncation 𝕜 E N x‖ ≤ ‖x‖ := by
  apply c0Sum_norm_le 𝕜 E (norm_nonneg x)
  intro n
  rw [c0SumTruncation_apply]
  split_ifs
  · exact c0Sum_norm_coordinate_le 𝕜 E x n
  · simp

theorem c0SumTruncation_norm_le (N : ℕ) : ‖c0SumTruncation 𝕜 E N‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (by
    intro x
    simpa only [one_mul] using c0SumTruncation_norm_apply_le 𝕜 E N x)

theorem c0SumTruncation_tendsto (x : C0Sum 𝕜 E) :
    Tendsto (fun N => c0SumTruncation 𝕜 E N x) atTop (𝓝 x) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 x.property) (ε/2) (half_pos hε)
  refine ⟨N, fun M hM => ?_⟩
  rw [dist_eq_norm]
  have hbound : ‖c0SumTruncation 𝕜 E M x - x‖ ≤ ε/2 := by
    apply c0Sum_norm_le 𝕜 E (le_of_lt (half_pos hε))
    intro n
    change ‖(c0SumTruncation 𝕜 E M x).val n - x.val n‖ ≤ ε/2
    rw [c0SumTruncation_apply]
    split_ifs with hn
    · simp; positivity
    · simpa only [zero_sub, norm_neg, dist_zero_right, norm_norm] using
        (le_of_lt (hN n (hM.trans (Nat.le_of_not_lt hn))))
  exact lt_of_le_of_lt hbound (half_lt_self hε)

end LindenstraussRetraction

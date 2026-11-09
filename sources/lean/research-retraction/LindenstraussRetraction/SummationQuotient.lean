import LindenstraussRetraction.CoordinateTruncation
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith

/-!
# The summation operator is an isometric quotient

Coordinate truncations give contractive approximate liftings. A geometric
correction series supplies exact liftings with arbitrarily small norm excess,
which proves the paper's open-unit-ball quotient condition.
-/

noncomputable section

open Filter Function Metric Set Topology
open scoped BigOperators ENNReal

namespace LindenstraussRetraction

universe u v w

variable (𝕜 : Type w) [RCLike 𝕜]

section GeometricCorrection

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Contractive approximate liftings with error factor `r < 1` can be corrected
to exact liftings with norm at most `(1-r)⁻¹ * ‖y‖`. No continuity of the
chosen approximate liftings is assumed. -/
theorem exists_exact_lift_of_approximate
    (q : E →L[𝕜] F) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (happrox : ∀ y : F, ∃ x : E,
      ‖q x - y‖ ≤ r * ‖y‖ ∧ ‖x‖ ≤ ‖y‖) (y : F) :
    ∃ x : E, q x = y ∧ ‖x‖ ≤ (1-r)⁻¹ * ‖y‖ := by
  choose g hg using happrox
  let h : F → F := fun z => z - q (g z)
  have hle : ∀ z, ‖h z‖ ≤ r * ‖z‖ := by
    intro z
    simpa only [h, norm_sub_rev] using (hg z).1
  have hnle : ∀ n : ℕ, ‖h^[n] y‖ ≤ r ^ n * ‖y‖ := by
    intro n
    induction n with
    | zero => simp
    | succ n IH =>
      rw [Function.iterate_succ_apply']
      calc
        ‖h (h^[n] y)‖ ≤ r * ‖h^[n] y‖ := hle _
        _ ≤ r * (r^n * ‖y‖) := mul_le_mul_of_nonneg_left IH hr0
        _ = r^(n+1) * ‖y‖ := by rw [pow_succ']; ring
  let u : ℕ → E := fun n => g (h^[n] y)
  have ule : ∀ n, ‖u n‖ ≤ r^n * ‖y‖ := fun n => (hg _).2.trans (hnle n)
  have sNu : Summable (fun n => ‖u n‖) := by
    apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) ule
    exact (summable_geometric_of_lt_one hr0 hr1).mul_right ‖y‖
  have su : Summable u := sNu.of_norm
  have xbound : ‖∑' n, u n‖ ≤ (1-r)⁻¹ * ‖y‖ := by
    calc
      ‖∑' n, u n‖ ≤ ∑' n, ‖u n‖ := norm_tsum_le_tsum_norm sNu
      _ ≤ ∑' n, r^n * ‖y‖ :=
        sNu.tsum_le_tsum ule ((summable_geometric_of_lt_one hr0 hr1).mul_right ‖y‖)
      _ = (1-r)⁻¹ * ‖y‖ := by rw [tsum_mul_right, tsum_geometric_of_lt_one hr0 hr1]
  have fsumeq : ∀ n : ℕ, q (∑ i ∈ Finset.range n, u i) = y - h^[n] y := by
    intro n
    induction n with
    | zero => simp
    | succ n IH =>
      rw [Finset.sum_range_succ, map_add, IH, Function.iterate_succ_apply']
      dsimp only [u, h]
      abel
  have L₁ : Tendsto (fun n => q (∑ i ∈ Finset.range n, u i)) atTop
      (𝓝 (q (∑' n, u n))) := q.continuous.tendsto _ |>.comp su.hasSum.tendsto_sum_nat
  simp only [fsumeq] at L₁
  have hzero : Tendsto (fun n => h^[n] y) atTop (𝓝 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simp only [sub_zero]
    apply squeeze_zero (fun n => norm_nonneg _) hnle
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).mul
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => ‖y‖) atTop (𝓝 ‖y‖))
  have L₂ : Tendsto (fun n => y - h^[n] y) atTop (𝓝 (y - 0)) :=
    tendsto_const_nhds.sub hzero
  have hq : q (∑' n, u n) = y := by
    simpa only [sub_zero] using tendsto_nhds_unique L₁ L₂
  exact ⟨∑' n, u n, hq, xbound⟩

end GeometricCorrection

section ConcreteSummation

/-- Truncation into the corresponding finite-coordinate block. -/
def truncationToBlock (m : ℕ) : C0 𝕜 →L[𝕜] FiniteCoordinateSpace 𝕜 m :=
  (c0TruncationOperator 𝕜 (m+1)).codRestrict (finiteCoordinateSubmodule 𝕜 m)
    (c0Truncation_mem 𝕜 m)

/-- Put the truncation of `x` in the `m`th ℓ₁ block. -/
def summationApproximateLift (m : ℕ) : C0 𝕜 →L[𝕜] SummationSpace 𝕜 :=
  (lp.singleContinuousLinearMap 𝕜 (FiniteCoordinateSpace 𝕜) 1 m).comp
    (truncationToBlock 𝕜 m)

@[simp] theorem summationApproximateLift_apply (m : ℕ) (x : C0 𝕜) :
    summationApproximateLift 𝕜 m x =
      lp.single 1 m ⟨c0Truncation 𝕜 (m+1) x, c0Truncation_mem 𝕜 m x⟩ := rfl

theorem norm_summationApproximateLift_le (m : ℕ) (x : C0 𝕜) :
    ‖summationApproximateLift 𝕜 m x‖ ≤ ‖x‖ := by
  rw [summationApproximateLift_apply, lp.norm_single (by norm_num)]
  exact norm_c0Truncation_le 𝕜 (m+1) x

@[simp] theorem summationOperator_single (m : ℕ) (x : FiniteCoordinateSpace 𝕜 m) :
    summationOperator 𝕜 (lp.single 1 m x) = x.val := by
  classical
  rw [summationOperator_apply]
  have ht : ∀ k, (lp.single 1 m x k).val = if k = m then x.val else 0 := by
    intro k
    by_cases hk : k = m
    · subst k; simp
    · simp [hk]
  simp only [ht]
  exact tsum_ite_eq m x.val

@[simp] theorem summationOperator_approximateLift (m : ℕ) (x : C0 𝕜) :
    summationOperator 𝕜 (summationApproximateLift 𝕜 m x) =
      c0Truncation 𝕜 (m+1) x := by
  rw [summationApproximateLift_apply, summationOperator_single]

theorem summationOperator_approximate_lifts {r : ℝ} (hr : 0 < r) (y : C0 𝕜) :
    ∃ x : SummationSpace 𝕜,
      ‖summationOperator 𝕜 x - y‖ ≤ r * ‖y‖ ∧ ‖x‖ ≤ ‖y‖ := by
  by_cases hy : y = 0
  · exact ⟨0, by simp [hy]⟩
  have hε : 0 < r * ‖y‖ := mul_pos hr (norm_pos_iff.mpr hy)
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 (c0Truncation_tendsto 𝕜 y)) _ hε
  refine ⟨summationApproximateLift 𝕜 N y, ?_, norm_summationApproximateLift_le 𝕜 N y⟩
  rw [summationOperator_approximateLift, ← dist_eq_norm]
  exact (hN (N+1) (Nat.le_succ N)).le

/-- Every point of the open unit ball has a preimage in the open unit ball. -/
theorem summationOperator_openUnitBall_lift (y : C0 𝕜) (hy : ‖y‖ < 1) :
    ∃ x : SummationSpace 𝕜, summationOperator 𝕜 x = y ∧ ‖x‖ < 1 := by
  let r : ℝ := (1 - ‖y‖) / 2
  have hr0 : 0 < r := by dsimp [r]; linarith
  have hr1 : r < 1 := by dsimp [r]; linarith [norm_nonneg y]
  obtain ⟨x, hqx, hx⟩ := exists_exact_lift_of_approximate 𝕜
    (summationOperator 𝕜) hr0.le hr1 (summationOperator_approximate_lifts 𝕜 hr0) y
  refine ⟨x, hqx, hx.trans_lt ?_⟩
  have hden : 0 < 1-r := sub_pos.mpr hr1
  rw [inv_mul_lt_one₀ hden]
  dsimp [r]
  linarith

/-- The summation quotient has precisely the usual c₀ quotient norm. -/
theorem summationOperator_isNormQuotient : IsNormQuotient (summationOperator 𝕜) := by
  apply Set.ext
  intro y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_ball_zero_iff] at hx ⊢
    exact (summationLinear_norm_le 𝕜 x).trans_lt hx
  · intro hy
    rw [mem_ball_zero_iff] at hy
    obtain ⟨x, hqx, hx⟩ := summationOperator_openUnitBall_lift 𝕜 y hy
    exact ⟨x, mem_ball_zero_iff.mpr hx, hqx⟩

end ConcreteSummation

end LindenstraussRetraction

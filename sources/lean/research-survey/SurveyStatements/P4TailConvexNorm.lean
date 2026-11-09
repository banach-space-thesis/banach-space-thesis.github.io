import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

noncomputable section
set_option autoImplicit false

open Filter Topology
open scoped BigOperators

namespace SurveyStatements.P4

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Finite convex combinations of successive tails preserve norm convergence. -/
theorem finiteConvexTail_tendsto (v : ℕ → E) {y : E}
    (hv : Tendsto v atTop (𝓝 y)) (F : ℕ → Finset ℕ) (a : ℕ → ℕ → ℝ)
    (ha : ∀ k n, n ∈ F k → 0 ≤ a k n) (hsum : ∀ k, ∑ n ∈ F k, a k n = 1)
    (htail : ∀ k n, n ∈ F k → k ≤ n) :
    Tendsto (fun k => ∑ n ∈ F k, a k n • v n) atTop (𝓝 y) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hv (ε / 2) (by positivity)
  refine ⟨N, ?_⟩
  intro k hk
  have heq : (∑ n ∈ F k, a k n • v n) - y =
      ∑ n ∈ F k, a k n • (v n - y) := by
    simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hsum, one_smul]
  rw [dist_eq_norm, heq]
  calc
    ‖∑ n ∈ F k, a k n • (v n - y)‖ ≤
        ∑ n ∈ F k, ‖a k n • (v n - y)‖ := norm_sum_le _ _
    _ = ∑ n ∈ F k, a k n * ‖v n - y‖ := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [norm_smul, Real.norm_of_nonneg (ha k n hn)]
    _ ≤ ∑ n ∈ F k, a k n * (ε / 2) := by
      apply Finset.sum_le_sum
      intro n hn
      apply mul_le_mul_of_nonneg_left _ (ha k n hn)
      simpa only [dist_eq_norm] using (hN n (hk.trans (htail k n hn))).le
    _ = ε / 2 := by rw [← Finset.sum_mul, hsum k, one_mul]
    _ < ε := by linarith

end SurveyStatements.P4

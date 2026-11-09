import SurveyStatements.P4Approximation

/-! Finite convex combinations of tails retain finite rank, norm bounds,
and strong identity convergence. These are the elementary properties used
after the paper's parametrized tail-convexification lemma. -/

noncomputable section
set_option autoImplicit false

open Filter Topology
open scoped BigOperators

namespace SurveyStatements.P4

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

def finiteConvexCombination (P : ℕ → E →L[𝕜] E) (F : Finset ℕ) (a : ℕ → ℝ) :
    E →L[𝕜] E := ∑ n ∈ F, (a n : 𝕜) • P n

theorem finiteRank_finiteConvexCombination
    (P : ℕ → E →L[𝕜] E) (hP : ∀ n, HasFiniteRank 𝕜 (P n))
    (F : Finset ℕ) (a : ℕ → ℝ) : HasFiniteRank 𝕜 (finiteConvexCombination P F a) :=
  HasFiniteRank.sum F _ (fun n _ => (hP n).smul (a n : 𝕜))

theorem norm_finiteConvexCombination_le
    (P : ℕ → E →L[𝕜] E) (C : ℝ) (hP : ∀ n, ‖P n‖ ≤ C)
    (F : Finset ℕ) (a : ℕ → ℝ) (ha : ∀ n ∈ F, 0 ≤ a n) (hsum : ∑ n ∈ F, a n = 1) :
    ‖finiteConvexCombination P F a‖ ≤ C := by
  unfold finiteConvexCombination
  calc
    _ ≤ ∑ n ∈ F, ‖(a n : 𝕜) • P n‖ := norm_sum_le _ _
    _ = ∑ n ∈ F, a n * ‖P n‖ := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [norm_smul, RCLike.norm_ofReal, abs_of_nonneg (ha n hn)]
    _ ≤ ∑ n ∈ F, a n * C :=
      Finset.sum_le_sum (fun n hn => mul_le_mul_of_nonneg_left (hP n) (ha n hn))
    _ = C := by rw [← Finset.sum_mul, hsum, one_mul]

/-- Convex combinations supported increasingly far out in a strongly
convergent sequence converge strongly to the same limit. -/
theorem finiteConvexCombination_tails_tendsto
    (P : ℕ → E →L[𝕜] E)
    (hP : ∀ x : E, Tendsto (fun n => P n x) atTop (𝓝 x))
    (F : ℕ → Finset ℕ) (a : ℕ → ℕ → ℝ)
    (ha : ∀ k n, n ∈ F k → 0 ≤ a k n)
    (hsum : ∀ k, ∑ n ∈ F k, a k n = 1)
    (htail : ∀ k n, n ∈ F k → k ≤ n) :
    ∀ x : E, Tendsto (fun k => finiteConvexCombination P (F k) (a k) x) atTop (𝓝 x) := by
  intro x
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hP x) (ε / 2) (by positivity)
  refine ⟨N, ?_⟩
  intro k hk
  have heq : finiteConvexCombination P (F k) (a k) x - x =
      ∑ n ∈ F k, (a k n : 𝕜) • (P n x - x) := by
    simp only [finiteConvexCombination, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smul_apply, smul_sub, Finset.sum_sub_distrib]
    rw [← Finset.sum_smul]
    have hc : ∑ n ∈ F k, (a k n : 𝕜) = 1 := by
      simpa only [← RCLike.ofReal_sum, RCLike.ofReal_one] using congrArg
        (fun r : ℝ => (r : 𝕜)) (hsum k)
    rw [hc, one_smul]
  rw [dist_eq_norm, heq]
  have hn : ∀ n ∈ F k, ‖P n x - x‖ ≤ ε / 2 := by
    intro n hn
    have he := hN n (hk.trans (htail k n hn))
    rw [dist_eq_norm] at he
    exact he.le
  have hbound : ‖∑ n ∈ F k, (a k n : 𝕜) • (P n x - x)‖ ≤ ε / 2 := by
    calc
      _ ≤ ∑ n ∈ F k, ‖(a k n : 𝕜) • (P n x - x)‖ := norm_sum_le _ _
      _ = ∑ n ∈ F k, a k n * ‖P n x - x‖ := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [norm_smul, RCLike.norm_ofReal, abs_of_nonneg (ha k n hn)]
      _ ≤ ∑ n ∈ F k, a k n * (ε / 2) :=
        Finset.sum_le_sum (fun n hn' => mul_le_mul_of_nonneg_left (hn n hn') (ha k n hn'))
      _ = ε / 2 := by rw [← Finset.sum_mul, hsum k, one_mul]
  exact hbound.trans_lt (by linarith)

end SurveyStatements.P4

import SurveyStatements.P1WeakNullSelectionConstruction
import SurveyStatements.P1BasicCriterion
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Every normalized weakly-null complex sequence has an asymptotically
monotone basic subsequence, retaining an explicit uniform basis estimate.
The one-step losses telescope; no infinite-product theorem is needed. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open Filter Topology
open scoped BigOperators

namespace SurveyStatements.P1

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

theorem weakNull_selection_weighted_prefix_bound (e : ℕ → X) (c : ℕ → ℝ)
    (hc : ∀ n, 0 < c n)
    (hstep : ∀ n : ℕ, ∀ a : ℕ → ℂ,
      (c n / c (n + 1)) * ‖sequencePartialSum e a n‖ ≤
        ‖sequencePartialSum e a (n + 1)‖)
    (N M : ℕ) (hNM : N ≤ M) (a : ℕ → ℂ) :
    c N * ‖sequencePartialSum e a N‖ ≤ c M * ‖sequencePartialSum e a M‖ := by
  induction M, hNM using Nat.le_induction with
  | base => exact le_rfl
  | succ M hNM ih =>
    apply ih.trans
    have hs := mul_le_mul_of_nonneg_left (hstep M a) (hc (M + 1)).le
    have heq : c (M + 1) * ((c M / c (M + 1)) * ‖sequencePartialSum e a M‖) =
        c M * ‖sequencePartialSum e a M‖ := by
      field_simp [(hc (M + 1)).ne']
    rwa [heq] at hs

theorem weakNull_selection_masked_prefix (e : ℕ → X) (a : ℕ → ℂ) (p q : ℕ) :
    sequencePartialSum e (fun i => if p ≤ i then a i else 0) (q + 1) =
      ∑ i ∈ Finset.Icc p q, a i • e i := by
  classical
  simp only [sequencePartialSum, ite_smul, zero_smul]
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
  omega

/-- Normalized weakly-null sequences admit an asymptotically monotone basic
subsequence with uniform projection norm at most two. -/
theorem weakNull_exists_asymptoticallyMonotone_subsequence_with_bound
    (y : ℕ → X) (hynorm : ∀ n, ‖y n‖ = 1)
    (hy : ∀ f : X →L[ℂ] ℂ, Tendsto (fun n => f (y n)) atTop (𝓝 0)) :
    ∃ ν : ℕ → ℕ, StrictMono ν ∧ IsAsymptoticallyMonotone (y ∘ ν) ∧
      ∀ N M : ℕ, N ≤ M → ∀ a : ℕ → ℂ,
        (1 / 2 : ℝ) * ‖sequencePartialSum (y ∘ ν) a N‖ ≤
          ‖sequencePartialSum (y ∘ ν) a M‖ := by
  let c : ℕ → ℝ := fun n => 1 - (1 / 2 : ℝ) ^ (n + 1)
  have hcge (n : ℕ) : 1 / 2 ≤ c n := by
    have hp : (1 / 2 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    dsimp [c]
    rw [pow_succ]
    nlinarith
  have hc0 (n : ℕ) : 0 < c n := by linarith [hcge n]
  have hc1 (n : ℕ) : c n < 1 := by
    dsimp [c]
    have hp : 0 < (1 / 2 : ℝ) ^ (n + 1) := pow_pos (by norm_num) _
    linarith
  have hcinc (n : ℕ) : c n < c (n + 1) := by
    have hp : 0 < (1 / 2 : ℝ) ^ (n + 1) := pow_pos (by norm_num) _
    change 1 - (1 / 2 : ℝ) ^ (n + 1) < 1 - (1 / 2 : ℝ) ^ ((n + 1) + 1)
    rw [pow_succ (1 / 2 : ℝ) (n + 1)]
    nlinarith
  have hβ0 (n : ℕ) : 0 < c n / c (n + 1) := div_pos (hc0 n) (hc0 (n + 1))
  have hβ1 (n : ℕ) : c n / c (n + 1) < 1 :=
    (div_lt_one (hc0 (n + 1))).mpr (hcinc n)
  obtain ⟨ν, hν, hstep⟩ := exists_weakNull_oneStep_subsequence y hynorm hy
    (fun n => c n / c (n + 1)) hβ0 hβ1
  let e := y ∘ ν
  have henorm (n : ℕ) : ‖e n‖ = 1 := hynorm (ν n)
  have hprefix : ∀ N M : ℕ, N ≤ M → ∀ a : ℕ → ℂ,
      c N * ‖sequencePartialSum e a N‖ ≤ ‖sequencePartialSum e a M‖ := by
    intro N M hNM a
    exact (weakNull_selection_weighted_prefix_bound e c hc0 hstep N M hNM a).trans
      (by simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (hc1 M).le (norm_nonneg (sequencePartialSum e a M)))
  have hhalf : ∀ N M : ℕ, N ≤ M → ∀ a : ℕ → ℂ,
      (1 / 2 : ℝ) * ‖sequencePartialSum e a N‖ ≤ ‖sequencePartialSum e a M‖ := by
    intro N M hNM a
    exact (mul_le_mul_of_nonneg_right (hcge N) (norm_nonneg _)).trans (hprefix N M hNM a)
  have hinter : ∀ p q r : ℕ, q ≤ r → ∀ a : ℕ → ℂ,
      c (q + 1) * ‖∑ i ∈ Finset.Icc p q, a i • e i‖ ≤
        ‖∑ i ∈ Finset.Icc p r, a i • e i‖ := by
    intro p q r hqr a
    have h := hprefix (q + 1) (r + 1) (Nat.succ_le_succ hqr)
      (fun i => if p ≤ i then a i else 0)
    simpa only [weakNull_selection_masked_prefix] using h
  have hc : Tendsto c atTop (𝓝 (1 : ℝ)) := by
    have hp : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    simpa [c] using tendsto_const_nhds.sub (hp.comp (tendsto_add_atTop_nat 1))
  refine ⟨ν, hν, ⟨basicSequence_of_uniform_partialSum henorm (by norm_num) hhalf,
    henorm, ?_⟩, hhalf⟩
  intro γ hγ
  have hthreshold : 1 / (1 + γ) < (1 : ℝ) := by
    apply (div_lt_one (by linarith)).mpr
    linarith
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hc.eventually (eventually_gt_nhds hthreshold))
  refine ⟨N, ?_⟩
  intro p q r hNp hpq hqr a
  have hcn := hN (q + 1) (by omega)
  have hprod : 1 ≤ (1 + γ) * c (q + 1) := by
    have hpos : 0 < 1 + γ := by linarith
    simpa [mul_comm] using (div_le_iff₀ hpos).mp hcn.le
  have hproj := hinter p q r hqr a
  nlinarith [norm_nonneg (∑ i ∈ Finset.Icc p q, a i • e i)]

end SurveyStatements.P1

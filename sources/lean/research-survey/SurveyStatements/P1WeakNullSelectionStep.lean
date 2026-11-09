import SurveyStatements.P1BasicSelection
import Mathlib.Order.Filter.Finite
import Mathlib.Tactic.Abel

/-! The finite approximate-norming step for selection from a normalized
weakly-null sequence. Future sequence terms need only have small evaluations
under the finite norming family; no annihilation or structural dichotomy is
assumed. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open Filter Topology

namespace SurveyStatements.P1

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

theorem finite_norming_small_evaluation_bound
    (M : Submodule ℂ X) (F : Finset (X →L[ℂ] ℂ))
    {c d δ : ℝ} (hδ : 0 ≤ δ) (hcomparison : c * (1 + δ) ≤ d - δ)
    (hFnorm : ∀ f ∈ F, ‖f‖ = 1)
    (hF : ∀ x ∈ M, x ≠ 0 → ∃ f ∈ F, d * ‖x‖ < ‖f x‖)
    {y : X} (hy : ‖y‖ = 1) (hyF : ∀ f ∈ F, ‖f y‖ ≤ δ)
    {x : X} (hx : x ∈ M) (a : ℂ) : c * ‖x‖ ≤ ‖x + a • y‖ := by
  by_cases hx0 : x = 0
  · simp [hx0, norm_nonneg]
  obtain ⟨f, hf, hfx⟩ := hF x hx hx0
  have ha : ‖a‖ ≤ ‖x + a • y‖ + ‖x‖ := by
    calc
      ‖a‖ = ‖a • y‖ := by rw [norm_smul, hy, mul_one]
      _ = ‖(x + a • y) - x‖ := by congr 1; abel
      _ ≤ _ := norm_sub_le _ _
  have hfxbound : ‖f x‖ ≤ ‖x + a • y‖ + ‖a‖ * δ := by
    calc
      ‖f x‖ = ‖f (x + a • y) - a • f y‖ := by simp only [map_add, map_smul, add_sub_cancel_right]
      _ ≤ ‖f (x + a • y)‖ + ‖a • f y‖ := norm_sub_le _ _
      _ ≤ ‖x + a • y‖ + ‖a‖ * δ := by
        apply add_le_add
        · simpa only [hFnorm f hf, one_mul] using f.le_opNorm (x + a • y)
        · rw [norm_smul]
          exact mul_le_mul_of_nonneg_left (hyF f hf) (norm_nonneg a)
  have hdelta : ‖a‖ * δ ≤ (‖x + a • y‖ + ‖x‖) * δ :=
    mul_le_mul_of_nonneg_right ha hδ
  have hnorm : (d - δ) * ‖x‖ ≤ (1 + δ) * ‖x + a • y‖ := by
    nlinarith
  have hfinal : (1 + δ) * (c * ‖x‖) ≤ (1 + δ) * ‖x + a • y‖ := by
    calc
      _ = (c * (1 + δ)) * ‖x‖ := by ring
      _ ≤ (d - δ) * ‖x‖ := mul_le_mul_of_nonneg_right hcomparison (norm_nonneg x)
      _ ≤ _ := hnorm
  exact (mul_le_mul_iff_right₀ (by linarith : 0 < 1 + δ)).mp hfinal

theorem weakNull_finite_evaluations_small (y : ℕ → X)
    (hy : ∀ f : X →L[ℂ] ℂ, Tendsto (fun n => f (y n)) atTop (𝓝 0))
    (F : Finset (X →L[ℂ] ℂ)) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n in atTop, ∀ f ∈ F, ‖f (y n)‖ < δ := by
  rw [eventually_all_finset]
  intro f _
  have hf : Tendsto (fun n => ‖f (y n)‖) atTop (𝓝 (0 : ℝ)) := by
    simpa only [norm_zero] using (hy f).norm
  exact hf.eventually (eventually_lt_nhds hδ)

theorem weakNull_finite_selection_step (y : ℕ → X)
    (hynorm : ∀ n, ‖y n‖ = 1)
    (hy : ∀ f : X →L[ℂ] ℂ, Tendsto (fun n => f (y n)) atTop (𝓝 0))
    (M : Submodule ℂ X) [FiniteDimensional ℂ M]
    {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (L : ℕ) :
    ∃ n : ℕ, L ≤ n ∧ ∀ x ∈ M, ∀ a : ℂ, c * ‖x‖ ≤ ‖x + a • y n‖ := by
  let d : ℝ := (1 + c) / 2
  let δ : ℝ := (1 - c) / 4
  have hd0 : 0 < d := by dsimp [d]; linarith
  have hd1 : d < 1 := by dsimp [d]; linarith
  have hδ : 0 < δ := by dsimp [δ]; linarith
  obtain ⟨F, hFnorm, hF⟩ := finite_norming_family M hd0 hd1
  obtain ⟨N, hN⟩ := eventually_atTop.mp (weakNull_finite_evaluations_small y hy F hδ)
  refine ⟨max L N, Nat.le_max_left _ _, ?_⟩
  intro x hx a
  apply finite_norming_small_evaluation_bound M F hδ.le ?_ hFnorm hF (hynorm _) ?_ hx a
  · dsimp [d, δ]
    nlinarith [sq_nonneg (1 - c)]
  · intro f hf
    exact (hN (max L N) (Nat.le_max_right _ _) f hf).le

end SurveyStatements.P1

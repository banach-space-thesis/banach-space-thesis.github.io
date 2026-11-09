import SurveyStatements.P5Support.HaarSignSecondMoment

/-! Fourth moments of genuine finite signed scalar sums, including complex
scalars. The expectation is the actual uniform finite sign average. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped BigOperators

namespace SurveyStatements.P5OperatorReduction
open P5Support P5Support.Grothendieck
variable {𝕜 : Type*} [RCLike 𝕜]

theorem finite_sign_fourth_moment_le {n : ℕ} (a : Fin n → 𝕜) :
    mean (fun θ : Fin n → Bool => ‖∑ i, signedValue (θ i) (a i)‖ ^ 4) ≤
      3 * (∑ i, ‖a i‖ ^ 2) ^ 2 := by
  let r : (Fin n → Bool) → ℝ := rademacher (fun i => RCLike.re (a i))
  let s : (Fin n → Bool) → ℝ := rademacher (fun i => RCLike.im (a i))
  let A : ℝ := ∑ i, RCLike.re (a i) ^ 2
  let B : ℝ := ∑ i, RCLike.im (a i) ^ 2
  have hA : 0 ≤ A := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hB : 0 ≤ B := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hr : mean (fun θ => r θ ^ 4) ≤ 3 * A ^ 2 :=
    rademacher_fourth_le (fun i => RCLike.re (a i))
  have hs : mean (fun θ => s θ ^ 4) ≤ 3 * B ^ 2 :=
    rademacher_fourth_le (fun i => RCLike.im (a i))
  have hr0 : 0 ≤ mean (fun θ => r θ ^ 4) := mean_nonneg (fun _ => by positivity)
  have hs0 : 0 ≤ mean (fun θ => s θ ^ 4) := mean_nonneg (fun _ => by positivity)
  have hcross0 : 0 ≤ mean (fun θ => r θ ^ 2 * s θ ^ 2) :=
    mean_nonneg (fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hcrossSq := mean_mul_sq_le (fun θ => r θ ^ 2) (fun θ => s θ ^ 2)
  have hpow (x : ℝ) : (x ^ 2) ^ 2 = x ^ 4 := by ring
  simp only [hpow] at hcrossSq
  have hprod : mean (fun θ => r θ ^ 4) * mean (fun θ => s θ ^ 4) ≤
      (3 * A ^ 2) * (3 * B ^ 2) :=
    mul_le_mul hr hs hs0 (by positivity)
  have hcross : mean (fun θ => r θ ^ 2 * s θ ^ 2) ≤ 3 * A * B := by
    have hAB : 0 ≤ 3 * A * B := by positivity
    nlinarith [hcrossSq.trans hprod]
  have hparts (θ : Fin n → Bool) :
      ‖∑ i, signedValue (θ i) (a i)‖ ^ 2 = r θ ^ 2 + s θ ^ 2 := by
    rw [RCLike.norm_sq_eq_def]
    have hre : RCLike.re (∑ i, signedValue (θ i) (a i)) = r θ := by
      simp only [map_sum, r, rademacher]
      apply Finset.sum_congr rfl
      intro i _
      cases θ i <;> simp [signedValue]
    have him : RCLike.im (∑ i, signedValue (θ i) (a i)) = s θ := by
      simp only [map_sum, s, rademacher]
      apply Finset.sum_congr rfl
      intro i _
      cases θ i <;> simp [signedValue]
    rw [hre, him]
    ring
  have hfour (θ : Fin n → Bool) :
      ‖∑ i, signedValue (θ i) (a i)‖ ^ 4 =
        r θ ^ 4 + s θ ^ 4 + 2 * (r θ ^ 2 * s θ ^ 2) := by
    rw [← hpow, hparts]
    ring
  have hab : (∑ i, ‖a i‖ ^ 2) = A + B := by
    dsimp only [A, B]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [RCLike.norm_sq_eq_def]
    ring
  simp_rw [hfour]
  rw [mean_add, mean_add, mean_mul_left, hab]
  nlinarith

theorem finite_sign_fourth_moment_of_bound {n : ℕ} (a : Fin n → 𝕜)
    {C : ℝ} (hC : 0 ≤ C) (ha : ∀ i, ‖a i‖ ≤ C) :
    mean (fun θ : Fin n → Bool => ‖∑ i, signedValue (θ i) (a i)‖ ^ 4) ≤
      3 * (n : ℝ) ^ 2 * C ^ 4 := by
  have hsum : (∑ i, ‖a i‖ ^ 2) ≤ (n : ℝ) * C ^ 2 := by
    calc
      _ ≤ ∑ _i : Fin n, C ^ 2 := Finset.sum_le_sum (fun i _ => by
        nlinarith [ha i, norm_nonneg (a i)])
      _ = _ := by simp
  have hsum0 : 0 ≤ ∑ i, ‖a i‖ ^ 2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hbound := finite_sign_fourth_moment_le a
  have hsq := (sq_le_sq₀ hsum0 (by positivity : 0 ≤ (n : ℝ) * C ^ 2)).2 hsum
  nlinarith

end SurveyStatements.P5OperatorReduction

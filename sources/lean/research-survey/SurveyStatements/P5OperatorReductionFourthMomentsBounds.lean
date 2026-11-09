import SurveyStatements.P5OperatorReductionFourthMoments

noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace SurveyStatements.P5OperatorReduction
open P5Support P5Support.Grothendieck
variable {𝕜 : Type*} [RCLike 𝕜]

theorem finite_signed_sum_norm_le {n : ℕ} (a : Fin n → 𝕜)
    {C : ℝ} (ha : ∀ i, ‖a i‖ ≤ C) (θ : Fin n → Bool) :
    ‖∑ i, signedValue (θ i) (a i)‖ ≤ (n : ℝ) * C := by
  calc
    _ ≤ ∑ i, ‖signedValue (θ i) (a i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin n, C := Finset.sum_le_sum (fun i _ => by
      simpa only [norm_signedValue] using ha i)
    _ = _ := by simp

theorem finite_sign_normalized_rpow_moment_le {n : ℕ} (hn : 0 < n)
    (a : Fin n → 𝕜) (ha : ∀ i, ‖a i‖ ≤ (n : ℝ)⁻¹)
    {q : ℝ} (hq : 4 ≤ q) :
    mean (fun θ : Fin n → Bool => ‖∑ i, signedValue (θ i) (a i)‖ ^ q) ≤
      3 / (n : ℝ) ^ 2 := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsum (θ : Fin n → Bool) : ‖∑ i, signedValue (θ i) (a i)‖ ≤ 1 :=
    (finite_signed_sum_norm_le a ha θ).trans_eq (mul_inv_cancel₀ hnR.ne')
  have hmono : mean (fun θ : Fin n → Bool =>
      ‖∑ i, signedValue (θ i) (a i)‖ ^ q) ≤
        mean (fun θ : Fin n → Bool => ‖∑ i, signedValue (θ i) (a i)‖ ^ 4) := by
    apply mean_mono
    intro θ
    simpa only [Real.rpow_ofNat] using
      Real.rpow_le_rpow_of_exponent_ge' (norm_nonneg _) (hsum θ)
        (by norm_num : (0 : ℝ) ≤ 4) hq
  have hfour := finite_sign_fourth_moment_of_bound a (inv_nonneg.mpr hnR.le) ha
  have heq : 3 * (n : ℝ) ^ 2 * ((n : ℝ)⁻¹) ^ 4 = 3 / (n : ℝ) ^ 2 := by
    field_simp
  exact hmono.trans (hfour.trans_eq heq)

end SurveyStatements.P5OperatorReduction

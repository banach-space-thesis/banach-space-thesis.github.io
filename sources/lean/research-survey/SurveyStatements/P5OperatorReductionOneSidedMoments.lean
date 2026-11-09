import SurveyStatements.P5Support.LpHaarSubsetSignSelection
import SurveyStatements.P5OperatorReductionMoments

/-! Uniform primal-side signed moments for actual scalar Lp functionals.
The functionals and selected packet subsets may both vary with the level. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter
open scoped ENNReal Classical BigOperators Topology
namespace SurveyStatements.P5OperatorReduction
open SurveyStatements.P5Support SurveyStatements.P5Support.Grothendieck
variable {𝕜 : Type*} [RCLike 𝕜]

theorem functional_signedBlock_eq_signed_sum (p : BanachExponent)
    (φ : IntervalLp 𝕜 p →L[𝕜] 𝕜) (n : ℕ)
    (S : Finset (Fin (2 ^ n))) (θ : Fin (2 ^ n) → Bool) :
    φ (lpHaarSignedBlock 𝕜 p n S θ) =
      ∑ k, signedValue (θ k) (φ (if k ∈ S then lpHaarDyadic 𝕜 p n k else 0)) := by
  rw [lpHaarSignedBlock, map_sum]
  have hterm (k : Fin (2 ^ n)) :
      signedValue (θ k) (φ (if k ∈ S then lpHaarDyadic 𝕜 p n k else 0)) =
        if k ∈ S then φ (signedValue (θ k) (lpHaarDyadic 𝕜 p n k)) else 0 := by
    by_cases hk : k ∈ S <;> cases θ k <;> simp [signedValue, hk]
  simp_rw [hterm]
  rw [← Finset.sum_filter]
  have hf : Finset.univ.filter (fun k => k ∈ S) = S := by ext k; simp
  rw [hf]

theorem functional_signedBlock_second_moment_le (p : BanachExponent) (hp : p.val ≠ ∞)
    (φ : IntervalLp 𝕜 p →L[𝕜] 𝕜) (n : ℕ) (S : Finset (Fin (2 ^ n))) :
    mean (fun θ => ‖φ (lpHaarSignedBlock 𝕜 p n S θ)‖ ^ 2) ≤
      ‖φ‖ ^ 2 * intervalLpDyadicRadius n ^ (1 / p.val.toReal) := by
  simp_rw [functional_signedBlock_eq_signed_sum, haar_sign_second_moment]
  exact lpHaarDyadic_subset_variance_le 𝕜 p hp n S φ

theorem functional_signedBlock_second_moment_le_uniform (p : BanachExponent)
    (hp : p.val ≠ ∞) (φ : IntervalLp 𝕜 p →L[𝕜] 𝕜)
    {C : ℝ} (hC : 0 ≤ C) (hφ : ‖φ‖ ≤ C)
    (n : ℕ) (S : Finset (Fin (2 ^ n))) :
    mean (fun θ => ‖φ (lpHaarSignedBlock 𝕜 p n S θ)‖ ^ 2) ≤
      C ^ 2 * intervalLpDyadicRadius n ^ (1 / p.val.toReal) := by
  apply (functional_signedBlock_second_moment_le p hp φ n S).trans
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (intervalLpDyadicRadius_pos n).le _)
  nlinarith [norm_nonneg φ]

theorem functional_signedBlock_family_moments_eventually_small
    (p : BanachExponent) (hp : p.val ≠ ∞) {m : ℕ}
    (φ : ℕ → Fin m → IntervalLp 𝕜 p →L[𝕜] 𝕜)
    {C : ℝ} (hC : 0 ≤ C) (hφ : ∀ n i, ‖φ n i‖ ≤ C)
    (S : ∀ n, Finset (Fin (2 ^ n))) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, (∑ i, mean (fun θ =>
      ‖φ n i (lpHaarSignedBlock 𝕜 p n (S n) θ)‖ ^ 2)) < ε ^ 2 := by
  have ht : Tendsto (fun n => (m : ℝ) * C ^ 2 *
      intervalLpDyadicRadius n ^ (1 / p.val.toReal)) atTop (𝓝 0) := by
    simpa using (lpHaarDyadic_norm_radius_tendsto_zero p hp).const_mul ((m : ℝ) * C ^ 2)
  filter_upwards [(tendsto_order.mp ht).2 (ε ^ 2) (sq_pos_of_pos hε)] with n hn
  apply lt_of_le_of_lt _ hn
  calc
    _ ≤ ∑ i : Fin m, C ^ 2 * intervalLpDyadicRadius n ^ (1 / p.val.toReal) :=
      Finset.sum_le_sum (fun i _ =>
        functional_signedBlock_second_moment_le_uniform p hp (φ n i) hC (hφ n i) n (S n))
    _ = _ := by simp [mul_assoc]

end SurveyStatements.P5OperatorReduction

import SurveyStatements.P5OperatorReductionFourthMomentsBounds
import SurveyStatements.P5Support.LebesgueLpPartition
import SurveyStatements.P5Support.LpHaarLevelVariation

/-! Finite sign moments of actual scalar Lp sums. All finite averages are
interchanged with the actual Lebesgue integral. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open MeasureTheory Filter
open scoped ENNReal BigOperators

namespace SurveyStatements.P5OperatorReduction
open P5Support P5Support.Grothendieck
variable {𝕜 α : Type*} [RCLike 𝕜] [MeasurableSpace α]
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ : Measure α}

theorem signedLp_sum_ae {n : ℕ} (f : Fin n → Lp 𝕜 p μ) (θ : Fin n → Bool) :
    (fun x => (∑ i, signedValue (θ i) (f i)) x) =ᵐ[μ]
      fun x => ∑ i, signedValue (θ i) (f i x) := by
  have hsign (i : Fin n) :
      (fun x => signedValue (θ i) (f i) x) =ᵐ[μ]
        fun x => signedValue (θ i) (f i x) := by
    cases θ i
    · simpa only [signedValue, Bool.false_eq_true, if_false] using Lp.coeFn_neg (f i)
    · exact Filter.EventuallyEq.rfl
  filter_upwards [lpHaar_coeFn_finset_sum Finset.univ
    (fun i => signedValue (θ i) (f i)), ae_all_iff.mpr hsign] with x hx hs
  exact hx.trans (Finset.sum_congr rfl (fun i _ => hs i))

theorem finite_Lp_norm_moment {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (hp : p ≠ ∞) (f : Ω → Lp 𝕜 p μ) :
    ENNReal.ofReal (mean (fun θ => ‖f θ‖ ^ p.toReal)) =
      ∫⁻ x, ENNReal.ofReal (mean (fun θ => ‖f θ x‖ ^ p.toReal)) ∂μ := by
  have hfun (θ : Ω) : (fun x => ENNReal.ofReal (‖f θ x‖ ^ p.toReal)) =
      (fun x => ‖f θ x‖ₑ ^ p.toReal) := by
    funext x
    rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg (f θ x)) ENNReal.toReal_nonneg,
      ofReal_norm_eq_enorm]
  have hnorm (θ : Ω) : ENNReal.ofReal (‖f θ‖ ^ p.toReal) =
      ∫⁻ x, ENNReal.ofReal (‖f θ x‖ ^ p.toReal) ∂μ := by
    rw [lebesgueLp_norm_rpow hp, hfun θ]
  have hmeas (θ : Ω) :
      AEMeasurable (fun x => ENNReal.ofReal (‖f θ x‖ ^ p.toReal)) μ := by
    rw [hfun θ]
    exact (Lp.aestronglyMeasurable (f θ)).enorm.pow_const _
  simp only [mean]
  rw [ENNReal.ofReal_mul (by positivity)]
  rw [ENNReal.ofReal_sum_of_nonneg (fun θ _ => Real.rpow_nonneg (norm_nonneg _) _)]
  simp_rw [hnorm]
  rw [← lintegral_finset_sum' Finset.univ (fun θ _ => hmeas θ)]
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr
  intro x
  rw [ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_sum_of_nonneg (fun θ _ => Real.rpow_nonneg (norm_nonneg _) _)]

theorem mean_signedLp_norm_rpow_le [IsProbabilityMeasure μ]
    (hp : p ≠ ∞) (hp4 : 4 ≤ p.toReal) {n : ℕ} (hn : 0 < n)
    (f : Fin n → Lp 𝕜 p μ)
    (hf : ∀ i, ∀ᵐ x ∂μ, ‖f i x‖ ≤ (n : ℝ)⁻¹) :
    mean (fun θ : Fin n → Bool => ‖∑ i, signedValue (θ i) (f i)‖ ^ p.toReal) ≤
      3 / (n : ℝ) ^ 2 := by
  have hmean0 : 0 ≤ mean (fun θ : Fin n → Bool =>
      ‖∑ i, signedValue (θ i) (f i)‖ ^ p.toReal) :=
    mean_nonneg (fun _ => Real.rpow_nonneg (norm_nonneg _) _)
  apply (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ 3 / (n : ℝ) ^ 2)).mp
  rw [finite_Lp_norm_moment hp]
  calc
    _ ≤ ∫⁻ _x, ENNReal.ofReal (3 / (n : ℝ) ^ 2) ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [ae_all_iff.mpr hf,
        ae_all_iff.mpr (fun θ : Fin n → Bool => signedLp_sum_ae f θ)] with x hx hs
      apply ENNReal.ofReal_le_ofReal
      simp_rw [hs]
      exact finite_sign_normalized_rpow_moment_le hn (fun i => f i x) hx hp4
    _ = _ := by simp

end SurveyStatements.P5OperatorReduction

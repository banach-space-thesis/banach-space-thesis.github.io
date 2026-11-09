import SurveyStatements.P5OperatorReductionSignedLpGrowthMoments
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-! Uniform sublinear sign averages in every finite scalar Lp space on a
probability space. The family may change with the number of terms. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open MeasureTheory Filter
open scoped ENNReal BigOperators

namespace SurveyStatements.P5OperatorReduction
open P5Support P5Support.Grothendieck
variable {𝕜 α : Type*} [RCLike 𝕜] [MeasurableSpace α]
variable {μ : Measure α} [IsProbabilityMeasure μ]

theorem mean_norm_rpow_le {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (z : Ω → ℝ) (hz : ∀ θ, 0 ≤ z θ) {q : ℝ} (hq : 1 ≤ q) :
    (mean z) ^ q ≤ mean (fun θ => z θ ^ q) := by
  have h := Real.rpow_arith_mean_le_arith_mean_rpow Finset.univ
    (fun _ : Ω => (Fintype.card Ω : ℝ)⁻¹) z
    (by intros; positivity) (by simp) (fun θ _ => hz θ) hq
  simpa only [mean, ← Finset.mul_sum] using h

theorem uniform_signedLp_tiny_family_mean_small
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 0 < N ∧
      ∀ n : ℕ, N ≤ n → ∀ f : Fin n → Lp 𝕜 p μ,
        (∀ i, ∀ᵐ x ∂μ, ‖f i x‖ ≤ (n : ℝ)⁻¹) →
          mean (fun θ : Fin n → Bool => ‖∑ i, signedValue (θ i) (f i)‖) < ε := by
  let q : ℝ≥0∞ := max p 4
  have hpq : p ≤ q := le_max_left _ _
  have h4q : (4 : ℝ≥0∞) ≤ q := le_max_right _ _
  have hq : q ≠ ∞ := by
    dsimp only [q]
    exact (max_lt (lt_top_iff_ne_top.mpr hp)
      (by norm_num : (4 : ℝ≥0∞) < ∞)).ne
  letI : Fact (1 ≤ q) := ⟨(Fact.out : 1 ≤ p).trans hpq⟩
  have hqr : (4 : ℝ) ≤ q.toReal := by
    simpa only [ENNReal.toReal_ofNat] using ENNReal.toReal_mono hq h4q
  have hqr0 : 0 < q.toReal := lt_of_lt_of_le (by norm_num) hqr
  intro ε hε
  have hεq : 0 < ε ^ q.toReal := Real.rpow_pos_of_pos hε _
  obtain ⟨N, hN⟩ := exists_nat_gt (3 / ε ^ q.toReal + 1)
  have hN0 : 0 < N := by
    have : (0 : ℝ) < N := lt_trans (by positivity) hN
    exact_mod_cast this
  refine ⟨N, hN0, fun n hn f hf => ?_⟩
  have hn0 : 0 < n := hN0.trans_le hn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn0
  have hnlarge : 3 / ε ^ q.toReal + 1 < (n : ℝ) :=
    hN.trans_le (by exact_mod_cast hn)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn0
  have hfrac : 3 / (n : ℝ) ^ 2 < ε ^ q.toReal := by
    apply (div_lt_iff₀ (sq_pos_of_pos hnR)).mpr
    have hdiv : 3 / ε ^ q.toReal < (n : ℝ) := by linarith
    have hprod : 3 < (n : ℝ) * ε ^ q.toReal := (div_lt_iff₀ hεq).mp hdiv
    have hsq : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
    simpa only [mul_comm] using
      hprod.trans_le (mul_le_mul_of_nonneg_right hsq hεq.le)
  have hgmem (i : Fin n) : MemLp (f i) q μ :=
    MemLp.of_bound (Lp.aestronglyMeasurable (f i)) (n : ℝ)⁻¹ (hf i)
  let g : Fin n → Lp 𝕜 q μ := fun i => (hgmem i).toLp (f i)
  have hgf (i : Fin n) : g i =ᵐ[μ] f i := MemLp.coeFn_toLp (hgmem i)
  have hg (i : Fin n) : ∀ᵐ x ∂μ, ‖g i x‖ ≤ (n : ℝ)⁻¹ := by
    filter_upwards [hgf i, hf i] with x hx hb
    simpa only [hx] using hb
  have hsum (θ : Fin n → Bool) :
      (fun x => (∑ i, signedValue (θ i) (f i)) x) =ᵐ[μ]
        fun x => (∑ i, signedValue (θ i) (g i)) x := by
    filter_upwards [signedLp_sum_ae f θ, signedLp_sum_ae g θ,
      ae_all_iff.mpr hgf] with x hf' hg' heq
    rw [hf', hg']
    exact Finset.sum_congr rfl (fun i _ => congrArg (signedValue (θ i)) (heq i).symm)
  have hnorm (θ : Fin n → Bool) : ‖∑ i, signedValue (θ i) (f i)‖ ≤
      ‖∑ i, signedValue (θ i) (g i)‖ := by
    rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (hsum θ)]
    exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top _)
      (eLpNorm_le_eLpNorm_of_exponent_le hpq (Lp.aestronglyMeasurable _))
  have hmean := mean_mono hnorm
  have hmoment := mean_signedLp_norm_rpow_le hq hqr hn0 g hg
  have hjensen := mean_norm_rpow_le
    (fun θ : Fin n → Bool => ‖∑ i, signedValue (θ i) (g i)‖)
    (fun _ => norm_nonneg _) (by linarith : 1 ≤ q.toReal)
  have hsmall : mean (fun θ : Fin n → Bool => ‖∑ i, signedValue (θ i) (g i)‖) < ε :=
    (Real.rpow_lt_rpow_iff (mean_nonneg (fun _ => norm_nonneg _)) hε.le hqr0).mp
      ((hjensen.trans hmoment).trans_lt hfrac)
  exact hmean.trans_lt hsmall

end SurveyStatements.P5OperatorReduction

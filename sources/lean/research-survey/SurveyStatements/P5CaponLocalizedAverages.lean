import SurveyStatements.P5CaponLocalizedRademacher

/-! The localized outer averages converge in every finite Lp exponent.
Their exact second moment retains the dyadic root's measure. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter Set
open scoped ENNReal BigOperators RealInnerProductSpace

namespace SurveyStatements.P5
open P5Support
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def caponLocalAverage (m : ℕ) (root : Fin (2 ^ m))
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (N : ℕ) : Lp ℝ p unitIntervalMeasure :=
  ((N + 1 : ℕ) : ℝ)⁻¹ •
    ∑ n ∈ Finset.range (N + 1), caponLocalRademacher m root p n

theorem caponLocalAverage_mean_zero (m : ℕ) (root : Fin (2 ^ m)) (N : ℕ) :
    probabilityLpMean (𝕜 := ℝ) (caponLocalAverage m root p N) = 0 := by
  simp only [caponLocalAverage, map_smul, map_sum, caponLocalRademacher_mean_zero,
    Finset.sum_const_zero, smul_zero]

theorem caponLocalAverage_ae_l2 (m : ℕ) (root : Fin (2 ^ m)) (N : ℕ) :
    caponLocalAverage m root p N =ᵐ[unitIntervalMeasure] caponLocalAverage m root 2 N := by
  have hlevels (n : ℕ) : caponLocalRademacher m root p n =ᵐ[unitIntervalMeasure]
      caponLocalRademacher m root 2 n :=
    (caponLocalRademacher_ae (p := p) m root n).trans
      (caponLocalRademacher_ae (p := 2) m root n).symm
  have hs : (⇑(∑ n ∈ Finset.range (N + 1), caponLocalRademacher m root p n))
      =ᵐ[unitIntervalMeasure] ⇑(∑ n ∈ Finset.range (N + 1), caponLocalRademacher m root 2 n) := by
    filter_upwards [scalarLp_sum_ae (Finset.range (N + 1))
      (fun n => caponLocalRademacher m root p n),
      scalarLp_sum_ae (Finset.range (N + 1)) (fun n => caponLocalRademacher m root 2 n),
      ae_all_iff.mpr hlevels] with x hp h2 hx
    rw [hp, h2]
    exact Finset.sum_congr rfl (fun n _ => hx n)
  exact (Lp.coeFn_smul _ _).trans
    ((hs.const_smul _) |>.trans (Lp.coeFn_smul _ _).symm)

theorem caponLocalAverage_bound (m : ℕ) (root : Fin (2 ^ m)) (N : ℕ) :
    ∀ᵐ x ∂unitIntervalMeasure, ‖caponLocalAverage m root p N x‖ ≤ 1 := by
  have hN : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
  have hsum : ∀ᵐ x ∂unitIntervalMeasure,
      ‖(∑ n ∈ Finset.range (N + 1), caponLocalRademacher m root p n) x‖ ≤
        ((N + 1 : ℕ) : ℝ) := by
    filter_upwards [scalarLp_sum_ae (Finset.range (N + 1))
      (fun n => caponLocalRademacher m root p n),
      ae_all_iff.mpr (caponLocalRademacher_bound (p := p) m root)] with x hx hb
    rw [hx]
    calc
      _ ≤ ∑ n ∈ Finset.range (N + 1), ‖caponLocalRademacher m root p n x‖ := norm_sum_le _ _
      _ ≤ ∑ _n ∈ Finset.range (N + 1), (1 : ℝ) := Finset.sum_le_sum (fun n _ => hb n)
      _ = ((N + 1 : ℕ) : ℝ) := by simp
  filter_upwards [Lp.coeFn_smul (((N + 1 : ℕ) : ℝ)⁻¹)
    (∑ n ∈ Finset.range (N + 1), caponLocalRademacher m root p n), hsum] with x hx hb
  change ‖(caponLocalAverage m root p N) x‖ ≤ 1
  rw [caponLocalAverage, hx, Pi.smul_apply, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr hN.le)]
  exact (mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hN.le)).trans_eq
    (inv_mul_cancel₀ hN.ne')

theorem norm_caponLocalRademacher_L2_sum_sq (m : ℕ) (root : Fin (2 ^ m)) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, caponLocalRademacher m root 2 n‖ ^ 2 =
      (N : ℝ) * intervalLpDyadicRadius m := by
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  simp_rw [inner_sum, caponLocalRademacher_L2_inner]
  simp [Finset.filter_true_of_mem, Finset.mem_range]
  rw [Finset.sum_congr rfl (fun n hn => if_pos (Finset.mem_range.mp hn))]
  simp

theorem norm_caponLocalAverage_L2_sq (m : ℕ) (root : Fin (2 ^ m)) (N : ℕ) :
    ‖caponLocalAverage m root 2 N‖ ^ 2 =
      ((N + 1 : ℕ) : ℝ)⁻¹ * intervalLpDyadicRadius m := by
  have hN : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
  rw [caponLocalAverage, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr hN.le), mul_pow,
    norm_caponLocalRademacher_L2_sum_sq]
  field_simp

theorem tendsto_caponLocalAverage_L2_sq (m : ℕ) (root : Fin (2 ^ m)) :
    Tendsto (fun N => ‖caponLocalAverage m root 2 N‖ ^ 2) atTop (nhds 0) := by
  have hinv : Tendsto (fun N : ℕ => ((N + 1 : ℕ) : ℝ)⁻¹) atTop (nhds 0) := by
    simpa only [Nat.cast_add, Nat.cast_one, one_div] using
      tendsto_one_div_add_atTop_nhds_zero_nat
  simpa only [norm_caponLocalAverage_L2_sq, zero_mul] using
    hinv.mul_const (intervalLpDyadicRadius m)

theorem tendsto_norm_caponLocalAverage_L2 (m : ℕ) (root : Fin (2 ^ m)) :
    Tendsto (fun N => ‖caponLocalAverage m root 2 N‖) atTop (nhds 0) := by
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using
    (Real.continuous_sqrt.tendsto 0).comp (tendsto_caponLocalAverage_L2_sq m root)

theorem tendsto_caponLocalAverage (hp_finite : p ≠ ∞) (m : ℕ) (root : Fin (2 ^ m)) :
    Tendsto (caponLocalAverage m root p) atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  by_cases hp2 : p ≤ 2
  · exact squeeze_zero (fun N => norm_nonneg _) (fun N =>
      norm_le_l2_of_ae_eq hp2 _ _ (caponLocalAverage_ae_l2 m root N))
      (tendsto_norm_caponLocalAverage_L2 m root)
  · have hpr : 0 < p.toReal := ENNReal.toReal_pos
      (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' hp_finite
    have ha : 0 < p.toReal⁻¹ := inv_pos.mpr hpr
    have hlim : Tendsto (fun N => (‖caponLocalAverage m root 2 N‖ ^ 2) ^ p.toReal⁻¹)
        atTop (nhds 0) := by
      simpa only [Real.zero_rpow ha.ne'] using
        (tendsto_caponLocalAverage_L2_sq m root).rpow_const (Or.inr ha.le)
    exact squeeze_zero (fun N => norm_nonneg _) (fun N =>
      norm_le_l2_moment_of_bound (le_of_not_ge hp2) hp_finite _ _
        (caponLocalAverage_ae_l2 m root N) (caponLocalAverage_bound m root N)) hlim

end SurveyStatements.P5

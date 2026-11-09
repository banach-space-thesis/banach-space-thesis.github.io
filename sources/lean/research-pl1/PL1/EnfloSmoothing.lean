import PL1.EnfloTruncation
import PL1.EnfloHypercontractive
import PL1.EnfloDyadicDecay

/-! # Positive-time noise destroys the maximum mass of every L1 dyadic bush

The source operator is arbitrary. A common integrable majorant controls
the truncation tails, and the actual Lp-to-L2 noise contraction controls
the bounded part. No compactness or extraction theorem is assumed.
-/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology NNReal ENNReal

namespace PL1.EnfloBush
open Walsh Noise NoiseHypercontractivity DyadicTrace

theorem noise_maxMass_le_truncated (u : ℝ≥0) (n : ℕ) (f : ℕ → Lp ℝ 1 haar)
    (M : ℝ) (hM : 0 ≤ M) (g : Walsh.Group → ℝ) (hg : Integrable g haar)
    (hg0 : ∀ x, 0 ≤ g x)
    (hfg : ∀ᵐ x ∂haar, (∑ j ∈ Finset.range n, |f j x|) ≤ g x) :
    maxMass n (fun j => noiseL1 ℝ constantRates u (f j)) ≤
      maxMass n (fun j => noiseL1 ℝ constantRates u (truncateLp M hM (f j))) +
        ∫ x, max (g x - M) 0 ∂haar := by
  apply (maxMass_le_add_sum_norm_sub n _ _).trans
  apply add_le_add le_rfl
  apply le_trans _ (sum_norm_truncation_error_le n f M hM g hg hg0 hfg)
  apply Finset.sum_le_sum
  intro j _
  rw [← map_sub]
  calc
    _ ≤ ‖noiseL1 ℝ constantRates u‖ * ‖f j - truncateLp M hM (f j)‖ :=
      (noiseL1 ℝ constantRates u).le_opNorm _
    _ ≤ 1 * ‖f j - truncateLp M hM (f j)‖ :=
      mul_le_mul_of_nonneg_right (norm_noiseL1_le_one ℝ constantRates u) (norm_nonneg _)
    _ = _ := one_mul _

def truncatedDyadicNoiseMass (u : ℝ≥0) (S : IntervalL1 ℝ →L[ℝ] Lp ℝ 1 haar)
    (M : ℝ) (hM : 0 ≤ M) (m : ℕ) : ℝ :=
  maxMass (2 ^ m) (fun j => noiseL1 ℝ constantRates u
    (truncateLp M hM (S (dyadicVector m j))))

theorem truncatedDyadicNoiseMass_nonneg (u : ℝ≥0)
    (S : IntervalL1 ℝ →L[ℝ] Lp ℝ 1 haar) (M : ℝ) (hM : 0 ≤ M) (m : ℕ) :
    0 ≤ truncatedDyadicNoiseMass u S M hM m := maxMass_nonneg _ _

theorem truncatedDyadicNoiseMass_sq_le (u : ℝ≥0)
    (S : IntervalL1 ℝ →L[ℝ] Lp ℝ 1 haar) (M : ℝ) (hM : 0 ≤ M) (m : ℕ) :
    truncatedDyadicNoiseMass u S M hM m ^ 2 ≤
      M ^ (2 * (1 - 1 / (exponent u).toReal)) *
        (‖S‖ * ((2 : ℝ) ^ m)⁻¹) ^ (2 / (exponent u).toReal - 1) * ‖S‖ := by
  apply bounded_family_noise_max_sq_le u (2 ^ m)
    (fun j => truncateLp M hM (S (dyadicVector m j))) M hM
    (fun j => truncateLp_bound M hM _) _ _ (by positivity) (norm_nonneg S)
  · intro j hj
    exact (norm_truncateLp_le M hM _).trans (norm_image_dyadicVector_le S m j hj)
  · exact (Finset.sum_le_sum (fun j _ => norm_truncateLp_le M hM _)).trans
      (dyadicSumMass_le S m)

theorem truncatedDyadicNoiseMass_tendsto (u : ℝ≥0) (hu : 0 < u)
    (S : IntervalL1 ℝ →L[ℝ] Lp ℝ 1 haar) (M : ℝ) (hM : 0 ≤ M) :
    Tendsto (truncatedDyadicNoiseMass u S M hM) atTop (𝓝 0) := by
  have hlim : Tendsto (fun m => M ^ (2 * (1 - 1 / (exponent u).toReal)) *
      (‖S‖ * ((2 : ℝ) ^ m)⁻¹) ^ (2 / (exponent u).toReal - 1) * ‖S‖) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_mul] using ((hypercontractive_dyadic_decay S u hu).const_mul
      (M ^ (2 * (1 - 1 / (exponent u).toReal)))).mul_const ‖S‖
  have hs := squeeze_zero (fun m => sq_nonneg (truncatedDyadicNoiseMass u S M hM m))
    (truncatedDyadicNoiseMass_sq_le u S M hM) hlim
  have hr := hs.sqrt
  simpa only [Real.sqrt_zero, Real.sqrt_sq_eq_abs,
    abs_of_nonneg (truncatedDyadicNoiseMass_nonneg u S M hM _)] using hr

/-- Every actual L1 operator followed by positive constant-rate noise has
vanishing maximum mass on the full interval dyadic partitions. -/
theorem noise_comp_dyadicVanishing (u : ℝ≥0) (hu : 0 < u)
    (S : IntervalL1 ℝ →L[ℝ] Lp ℝ 1 haar) :
    DyadicVanishing ((noiseL1 ℝ constantRates u).comp S) := by
  obtain ⟨g, hg, hg0, hfg⟩ := exists_dyadic_majorant S
  have hbound (M m : ℕ) :
      dyadicMaxMass ((noiseL1 ℝ constantRates u).comp S) m ≤
        truncatedDyadicNoiseMass u S M (Nat.cast_nonneg M) m +
          ∫ x, max (g x - (M : ℝ)) 0 ∂haar := by
    apply noise_maxMass_le_truncated u (2 ^ m)
      (fun j => S (dyadicVector m j)) M (Nat.cast_nonneg M) g hg hg0
    filter_upwards [hfg] with x hx
    exact hx m
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨M, hM⟩ := ((integral_tail_tendsto_zero g hg hg0).eventually_lt_const (half_pos hε)).exists
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((truncatedDyadicNoiseMass_tendsto u hu S M (Nat.cast_nonneg M)).eventually_lt_const (half_pos hε))
  refine ⟨N, fun m hm => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (dyadicMaxMass_nonneg _ m)]
  have hb := hbound M m
  have hn := hN m hm
  linarith

#print axioms noise_comp_dyadicVanishing

end PL1.EnfloBush

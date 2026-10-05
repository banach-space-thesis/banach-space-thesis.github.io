import ThesisCommon.Analysis.GowersMaureyInterpolationBarriers
import ThesisCommon.Analysis.GowersMaureyRISSumSupport
import ThesisCommon.Analysis.GowersMaureyRISNormalizedSupport

/-! RIS estimates for the actual interpolation profile attached to all
special sizes of the constructed space. All numerical profile conditions
are discharged. Only the later gap-value hypothesis is retained where
the normalized Lemma 7 bound explicitly needs it. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem RISData.sum_norm_le_interpolation {D : ConstructionData 𝕜} {N : ℕ} {ε : ℝ}
    {x : Fin N → C00 𝕜} (h : RISData D ε x) :
    implicitNorm D (∑ i, x i) ≤ (1 + 2 * ε) * interpolationG D.specialSizes N := by
  let K := D.specialSizes
  let g : ℕ → ℝ := fun k => interpolationProfile K k
  have hg : ∀ k : ℕ, 2 ≤ k → Real.sqrt (logarithmicWeight k) ≤ g k := by
    intro k hk
    exact interpolationProfile_ge_sqrt K (by exact_mod_cast (show 1 ≤ k by omega))
  have hgpos : ∀ k, 2 ≤ k → 0 < g k := by
    intro k hk
    exact (zero_lt_one.trans_le (one_le_sqrt_logarithmicWeight
      (by exact_mod_cast (show 1 ≤ k by omega)))).trans_le (hg k hk)
  have hgf : ∀ k : ℕ, 2 ≤ k → g k ≤ logarithmicWeight k := by
    intro k hk
    exact interpolationProfile_le_weight K (by exact_mod_cast (show 1 ≤ k by omega))
  have hgs : ∀ k, k ∈ D.specialSizes → g k ≤ Real.sqrt (logarithmicWeight k) := by
    intro k hk
    exact interpolationProfile_le_sqrt_at_selected_size K (by have := D.specialSize_ge_two hk; omega) hk
  apply h.sum_norm_le_of_support (interpolationG K) g
    (interpolationG_concaveOn K) (interpolationG_monotoneOn K)
    (fun t ht ht1 => interpolationG_small K ht ht1) interpolation_support_slope_nonneg
    (fun u hu => interpolationG_support K hu) (by linarith)
    (fun r s hr hs => interpolationG_mul_le K hr hs) hg
    (fun k hk => interpolationProfile_inverse_mul K (by exact_mod_cast hk))
  intro E r hr hn
  exact h.exists_norming_form g hgpos hgf hgs E hr hn

theorem RISData.normalized_intervalNorm_le_of_interpolation_value
    {D : ConstructionData 𝕜} {N : ℕ} {ε : ℝ}
    {x : Fin N → C00 𝕜} (h : RISData D ε x) {n : ℕ} (hn : 0 < n) (hnN : n ≤ N)
    (hvalue : interpolationProfile D.specialSizes ((N : ℝ) / n) = logarithmicWeight ((N : ℝ) / n))
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hf : logarithmicWeight N ≤ (1 + δ) * logarithmicWeight ((N : ℝ) / n)) :
    intervalNorm D n ((logarithmicWeight N / N) • (∑ i, x i)) ≤ (1 + δ) * (1 + 3 * ε) := by
  let K := D.specialSizes
  let g : ℕ → ℝ := fun k => interpolationProfile K k
  have hratio : 1 ≤ (N : ℝ) / n := by
    rw [le_div_iff₀ (by exact_mod_cast hn : (0 : ℝ) < n), one_mul]
    exact_mod_cast hnN
  have hGvalue : interpolationG K ((N : ℝ) / n) =
      ((N : ℝ) / n) / logarithmicWeight ((N : ℝ) / n) := by
    have hh := interpolationProfile_inverse_mul K hratio
    rw [hvalue] at hh
    simpa only [div_eq_mul_inv, mul_comm] using hh.symm
  apply h.normalized_intervalNorm_le_of_support_profile (interpolationG K) g
    (interpolationG_concaveOn K) (interpolationG_monotoneOn K)
    (fun t ht ht1 => interpolationG_small K ht ht1) interpolation_support_slope_nonneg
    (fun u hu => interpolationG_support K hu) (by linarith)
    (fun r s hr hs => interpolationG_mul_le K hr hs)
    (fun k hk => interpolationProfile_ge_sqrt K (by exact_mod_cast (show 1 ≤ k by omega)))
    (fun k hk => interpolationProfile_le_weight K (by exact_mod_cast (show 1 ≤ k by omega)))
    (fun k hk => interpolationProfile_le_sqrt_at_selected_size K
      (by have := D.specialSize_ge_two hk; omega) hk)
    (fun k hk => interpolationProfile_inverse_mul K (by exact_mod_cast hk)) hn hnN hGvalue hδ hf

end ThesisCommon.GowersMaurey

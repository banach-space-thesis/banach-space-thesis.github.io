import ThesisCommon.Analysis.GowersMaureyRISIntervalEstimate
import ThesisCommon.Analysis.GowersMaureyRISRemainder

/-! Source Lemma 7's exact quantitative conclusion, once its numerical
interpolation profile is supplied. The profile construction is separate;
all space, interval, RIS, and normalization estimates are proved here. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem RISData.normalized_intervalNorm_le_of_admissible_profile
    {D : ConstructionData 𝕜} {N : ℕ} {ε : ℝ}
    {x : Fin N → C00 𝕜} (h : RISData D ε x) (G : ℝ → ℝ) (g : ℕ → ℝ) {d : ℝ}
    (hG : ConcaveOn ℝ (Set.Ici 0) G) (hmono : MonotoneOn G (Set.Ici 0))
    (hsmallG : ∀ t, 0 ≤ t → t ≤ 1 → G t = t) (hd : 0 ≤ d)
    (hderiv : HasDerivWithinAt G d (Set.Ioi 1) 1)
    (hgap : 1 / (4 * Real.log 2) ≤ 1 - d)
    (hmul : ∀ r s, 0 ≤ r → 0 ≤ s → G r * G s ≤ G (r * s))
    (hg : ∀ k : ℕ, 2 ≤ k → Real.sqrt (logarithmicWeight k) ≤ g k)
    (hgf : ∀ k : ℕ, 2 ≤ k → g k ≤ logarithmicWeight k)
    (hgspecial : ∀ k, k ∈ D.specialSizes → g k ≤ Real.sqrt (logarithmicWeight k))
    (hgprofile : ∀ k : ℕ, 1 ≤ k → (g k)⁻¹ * k = G k)
    {n : ℕ} (hn : 0 < n) (hnN : n ≤ N)
    (hprofile : G ((N : ℝ) / n) = ((N : ℝ) / n) / logarithmicWeight ((N : ℝ) / n))
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hf : logarithmicWeight N ≤ (1 + δ) * logarithmicWeight ((N : ℝ) / n)) :
    intervalNorm D n ((logarithmicWeight N / N) • (∑ i, x i)) ≤ (1 + δ) * (1 + 3 * ε) := by
  have hN : 0 < N := lt_of_lt_of_le hn hnN
  have ht : 1 ≤ (1 + δ) * (1 + 3 * ε) := by
    nlinarith [h.epsilon_pos, mul_nonneg hδ h.epsilon_pos.le]
  by_cases hN1 : N = 1
  · subst N
    have hn1 : n = 1 := by omega
    subst n
    simp only [Nat.cast_one, logarithmicWeight_one, div_one, one_smul, Fin.sum_univ_one,
      intervalNorm_one]
    exact (h.vector_norm_le_one 0).trans ht
  have hN2 : 2 ≤ N := by omega
  let i0 : Fin N := ⟨0, hN⟩
  have hmin : ∀ i, h.size i0 ≤ h.size i := fun i => h.size_strict.monotone (by
    change 0 ≤ i.val
    exact Nat.zero_le _)
  have hbound := h.intervalNorm_sum_le_of_admissible_profile G g hG hmono hsmallG hd
    hderiv hgap hmul hg hgf hgspecial hgprofile i0 hmin hn
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hratio : 1 ≤ (N : ℝ) / n := by
    rw [le_div_iff₀ hnr, one_mul]
    exact_mod_cast hnN
  have hfr : 0 < logarithmicWeight ((N : ℝ) / n) := by
    have hh := logarithmicWeight_strictMonoOn.monotoneOn (by norm_num : (1 : ℝ) ∈ Set.Ici 1)
      hratio hratio
    rw [logarithmicWeight_one] at hh
    exact zero_lt_one.trans_le hh
  have hfn : 0 ≤ logarithmicWeight N := zero_le_one.trans (one_le_logarithmicWeight hN)
  have hC : 0 ≤ 1 + 2 * ε := by linarith [h.epsilon_pos]
  have hsize : (0 : ℝ) < h.size i0 := by exact_mod_cast h.size_pos i0
  have hmain : logarithmicWeight N / logarithmicWeight ((N : ℝ) / n) ≤ 1 + δ :=
    (div_le_iff₀ hfr).mpr hf
  rw [seminorm_real_smul, abs_of_nonneg (div_nonneg hfn hNr.le)]
  calc
    _ ≤ (logarithmicWeight N / N) * ((1 + 2 * ε) *
        ((n : ℝ) * G ((N : ℝ) / n) + n * ((N : ℝ) / h.size i0))) :=
      mul_le_mul_of_nonneg_left hbound (div_nonneg hfn hNr.le)
    _ = (1 + 2 * ε) * (logarithmicWeight N / logarithmicWeight ((N : ℝ) / n)) +
        (1 + 2 * ε) * n * logarithmicWeight N / h.size i0 := by
      rw [hprofile]
      field_simp
    _ ≤ (1 + 2 * ε) * (1 + δ) + ε := add_le_add
      (mul_le_mul_of_nonneg_left hmain hC) (h.normalized_interval_remainder_le hN2 hnN i0)
    _ ≤ (1 + δ) * (1 + 3 * ε) := by nlinarith [mul_nonneg hδ h.epsilon_pos.le]

end ThesisCommon.GowersMaurey

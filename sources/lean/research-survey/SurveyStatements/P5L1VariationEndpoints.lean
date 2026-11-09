import SurveyStatements.P5L1VariationMeanZero

/-! Finite rooted-branch variation including both endpoint values. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace SurveyStatements.P5L1Variation
open SurveyStatements.P5Support

theorem finite_branch_variation_endpoints_le (𝕜 : Type*) [RCLike 𝕜]
    (D : IntervalL1 𝕜 →L[𝕜] IntervalL1 𝕜)
    (d : (n : ℕ) → Fin (2 ^ n) → 𝕜)
    (hD : ∀ (n : ℕ) (k : Fin (2 ^ n)),
      D (lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ n k) = d n k • lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ n k)
    {r : ℕ} (B : DyadicBranch r) (N : ℕ) :
    ‖B.symbol 𝕜 d 0‖ + (∑ j ∈ Finset.range N,
      ‖B.symbol 𝕜 d (j + 1) - B.symbol 𝕜 d j‖) + ‖B.symbol 𝕜 d N‖ ≤ 8 * ‖D‖ := by
  have hv := B.finite_variation_le 𝕜 D d hD N
  have hroot := multiplier_symbol_norm_le 𝕜 D d hD (r + 0) (B.index 0)
  have hend := multiplier_symbol_norm_le 𝕜 D d hD (r + N) (B.index N)
  change ‖B.symbol 𝕜 d 0‖ ≤ ‖D‖ at hroot
  change ‖B.symbol 𝕜 d N‖ ≤ ‖D‖ at hend
  linarith

theorem meanZero_finite_branch_variation_endpoints_le (𝕜 : Type*) [RCLike 𝕜]
    (R : MeanZeroL1 𝕜 →L[𝕜] MeanZeroL1 𝕜)
    (d : (n : ℕ) → Fin (2 ^ n) → 𝕜)
    (hR : ∀ n k, R (meanZeroHaar 𝕜 n k) = d n k • meanZeroHaar 𝕜 n k)
    {r : ℕ} (B : DyadicBranch r) (N : ℕ) :
    ‖B.symbol 𝕜 d 0‖ + (∑ j ∈ Finset.range N,
      ‖B.symbol 𝕜 d (j + 1) - B.symbol 𝕜 d j‖) + ‖B.symbol 𝕜 d N‖ ≤ 16 * ‖R‖ := by
  have hv := finite_branch_variation_endpoints_le 𝕜 (extendMeanZero 𝕜 R) d
    (extendMeanZero_haar 𝕜 R d hR) B N
  have hn := extendMeanZero_norm_le 𝕜 R
  linarith

end SurveyStatements.P5L1Variation

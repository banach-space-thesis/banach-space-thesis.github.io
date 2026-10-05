import ThesisCommon.Analysis.GowersMaureyRISWeightMeasureSupport
import ThesisCommon.Analysis.GowersMaureyWeightedIntervalNorm

/-! The higher-interval estimate with the supporting-line hypothesis.
This form applies directly to concave envelopes bounded by the source's
smooth reciprocal square-root-logarithmic barrier. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem RISData.intervalNorm_sum_le_of_support_profile
    {D : ConstructionData 𝕜} {N : ℕ} {ε : ℝ}
    {x : Fin N → C00 𝕜} (h : RISData D ε x) (G : ℝ → ℝ) (g : ℕ → ℝ) {d : ℝ}
    (hG : ConcaveOn ℝ (Set.Ici 0) G) (hmono : MonotoneOn G (Set.Ici 0))
    (hsmallG : ∀ t, 0 ≤ t → t ≤ 1 → G t = t) (hd : 0 ≤ d)
    (hsupport : ∀ u, 1 ≤ u → G u ≤ 1 + d * (u - 1))
    (hgap : 1 / (4 * Real.log 2) ≤ 1 - d)
    (hmul : ∀ r s, 0 ≤ r → 0 ≤ s → G r * G s ≤ G (r * s))
    (hg : ∀ k : ℕ, 2 ≤ k → Real.sqrt (logarithmicWeight k) ≤ g k)
    (hgf : ∀ k : ℕ, 2 ≤ k → g k ≤ logarithmicWeight k)
    (hgspecial : ∀ k, k ∈ D.specialSizes → g k ≤ Real.sqrt (logarithmicWeight k))
    (hgprofile : ∀ k : ℕ, 1 ≤ k → (g k)⁻¹ * k = G k)
    (i0 : Fin N) (hmin : ∀ i, h.size i0 ≤ h.size i) {n : ℕ} (hn : 0 < n) :
    intervalNorm D n (∑ i, x i) ≤ (1 + 2 * ε) *
      ((n : ℝ) * G ((N : ℝ) / n) + n * ((N : ℝ) / h.size i0)) := by
  have hC : 0 ≤ 1 + 2 * ε := by linarith [h.epsilon_pos]
  by_cases hx0 : (∑ i, x i) = 0
  · rw [hx0, map_zero]
    apply mul_nonneg hC
    apply add_nonneg
    · apply mul_nonneg (Nat.cast_nonneg n)
      rw [← hsmallG 0 le_rfl (by norm_num)]
      have hquot : 0 ≤ (N : ℝ) / n := div_nonneg (Nat.cast_nonneg N) (Nat.cast_nonneg n)
      exact hmono (by norm_num) hquot hquot
    · exact mul_nonneg (Nat.cast_nonneg n) (div_nonneg (Nat.cast_nonneg N) (Nat.cast_nonneg _))
  · obtain ⟨μ, hμ, _, htotal, hbound⟩ := h.exists_weight_measure_of_support G g hG hmono
      hsmallG hd hsupport hgap hmul hg hgf hgspecial hgprofile i0 hmin hx0
    exact intervalNorm_le_of_weight_measure D _ hn G hG hmono hC μ hμ htotal hbound

end ThesisCommon.GowersMaurey


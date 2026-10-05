import ThesisCommon.Analysis.IntervalPrimariness
import ThesisCommon.Analysis.CompactMetricMilutin

/-! The uncountable compact metric case, using the actual Milutin equivalence
and the checked interval factorization theorem. All Banach sequence exponents,
including one and infinity, are included. -/

noncomputable section
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable (K : Type*) [MetricSpace K] [CompactSpace K] [Uncountable K]

theorem uncountable_compactMetric_hasUPFP : HasUPFP 𝕜 C(K, 𝕜) :=
  interval_hasUPFP.of_equiv (milutinCompactMetricEquivInterval (𝕜 := 𝕜) K).symm

theorem uncountable_compactMetric_primary : IsPrimary 𝕜 C(K, 𝕜) :=
  (uncountable_compactMetric_hasUPFP K).isPrimary_of_sequenceSelfSimilar
    (compactMetric_sequenceSelfSimilar K)

theorem uncountable_compactMetric_cZero_upfp_primary :
    HasUPFP 𝕜 (CZeroSum C(K, 𝕜)) ∧ IsPrimary 𝕜 (CZeroSum C(K, 𝕜)) := by
  have h := (uncountable_compactMetric_hasUPFP (𝕜 := 𝕜) K).of_equiv
    (compactMetricCZeroEquiv K)
  exact ⟨h, h.cZero_isPrimary⟩

theorem uncountable_compactMetric_lp_upfp_primary (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    HasUPFP 𝕜 (lp (fun _ : ℕ => C(K, 𝕜)) p) ∧
      IsPrimary 𝕜 (lp (fun _ : ℕ => C(K, 𝕜)) p) := by
  have h := (interval_lp_unconditional_upfp_primary (𝕜 := 𝕜) p).1.of_equiv
    (lpMapEquiv p (milutinCompactMetricEquivInterval (𝕜 := 𝕜) K).symm)
  exact ⟨h, h.lp_isPrimary⟩

theorem uncountable_compactMetric_sequence_upfp_primary (p : BanachExponent) :
    HasUPFP 𝕜 (SequenceSum p C(K, 𝕜)) ∧ IsPrimary 𝕜 (SequenceSum p C(K, 𝕜)) :=
  uncountable_compactMetric_lp_upfp_primary K p.val

end ThesisCommon

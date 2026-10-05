import ThesisCommon.Analysis.MilutinEquivalence

/-! Concrete consequences of the checked Milutin isomorphism: independence
of the uncountable compact metric model and countable c₀ self-similarity. -/

noncomputable section
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

/-- Milutin's theorem depends only on metrizability of the given topology. -/
theorem milutin_compactMetrizable_equiv_interval (K : Type*)
    [TopologicalSpace K] [TopologicalSpace.MetrizableSpace K]
    [CompactSpace K] [Uncountable K] :
    Nonempty (C(K, 𝕜) ≃L[𝕜] IntervalContinuous 𝕜) := by
  letI : MetricSpace K := TopologicalSpace.metrizableSpaceMetric K
  exact milutin_compactMetric_equiv_interval (𝕜 := 𝕜) K

/-- Any two uncountable compact metric spaces have isomorphic spaces of
continuous real or complex functions. -/
def milutinCompactMetricEquiv (K L : Type*)
    [MetricSpace K] [CompactSpace K] [Uncountable K]
    [MetricSpace L] [CompactSpace L] [Uncountable L] :
    C(K, 𝕜) ≃L[𝕜] C(L, 𝕜) :=
  (milutinCompactMetricEquivInterval K).trans (milutinCompactMetricEquivInterval L).symm

/-- The concrete c₀ self-similarity needed by Pełczyński's primariness
argument for uncountable compact metric C(K). -/
def compactMetricCZeroEquiv (K : Type*)
    [MetricSpace K] [CompactSpace K] [Uncountable K] :
    C(K, 𝕜) ≃L[𝕜] CZeroSum C(K, 𝕜) :=
  (milutinCompactMetricEquivInterval K).trans
    (intervalCZeroEquiv.trans
      (cZeroMapEquiv (ι := ℕ) (milutinCompactMetricEquivInterval K).symm))

theorem compactMetric_sequenceSelfSimilar (K : Type*)
    [MetricSpace K] [CompactSpace K] [Uncountable K] :
    IsSequenceSelfSimilar 𝕜 C(K, 𝕜) :=
  Or.inr ⟨compactMetricCZeroEquiv K⟩

end ThesisCommon

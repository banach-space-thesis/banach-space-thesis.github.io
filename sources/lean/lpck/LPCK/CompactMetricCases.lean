import LPCK.MainStatements
import ThesisCommon.Analysis.FiniteCompactPrimariness
import ThesisCommon.Analysis.UncountableCompactMetricPrimariness

/-! Unconditional finite and uncountable compact metric cases of Corollary
1.3. The general countably infinite compact metric case remains a separate
obligation; these specializations do not assert the entire corollary. -/
noncomputable section
namespace LPCK
open ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

theorem corollary_1_3_finite (K : Type*) [MetricSpace K] [CompactSpace K]
    [Finite K] (p : BanachExponent) : Corollary_1_3 𝕜 K p :=
  (finiteCompact_sequence_upfp_primary (𝕜 := 𝕜) K p).2

theorem corollary_1_3_uncountable (K : Type*) [MetricSpace K] [CompactSpace K]
    [Uncountable K] (p : BanachExponent) : Corollary_1_3 𝕜 K p :=
  (uncountable_compactMetric_sequence_upfp_primary (𝕜 := 𝕜) K p).2

end LPCK

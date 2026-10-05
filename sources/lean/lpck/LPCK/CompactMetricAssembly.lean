import LPCK.CompactMetricCases
import ThesisCommon.Analysis.CountableCompactClassification
import ThesisCommon.Analysis.ContinuousMapPullback
import LPCK.CountableOrdinalSequence

/-! The full compact-metric classification assembly for Corollary 1.3.
The unconditional proof uses the checked countable ordinal theorem and
Milutin's equivalence for uncountable compact metric spaces. -/
noncomputable section
universe u
namespace LPCK
open ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

theorem corollary_1_3_of_ordinal_theorem
    (hOrdinal : ∀ (α : Ordinal.{u}) (p : BanachExponent), Theorem_1_1 𝕜 α p)
    (K : Type u) [MetricSpace K] [CompactSpace K] (p : BanachExponent) :
    Corollary_1_3 𝕜 K p := by
  classical
  by_cases hf : Finite K
  · letI : Finite K := hf
    exact corollary_1_3_finite K p
  letI : Infinite K := not_finite_iff_infinite.mp hf
  by_cases hc : Countable K
  · letI : Countable K := hc
    obtain ⟨α, ⟨e⟩⟩ := countableCompact_exists_ordinal_model K
    let eC : C(K, 𝕜) ≃L[𝕜] OrdinalContinuous 𝕜 α := continuousMapHomeomorphEquiv e
    have h := (hOrdinal α p).1.of_equiv (lpMapEquiv p.val eC).symm
    exact h.lp_isPrimary
  · letI : Uncountable K := ⟨hc⟩
    exact corollary_1_3_uncountable K p

theorem corollary_1_3_proof (K : Type u) [MetricSpace K] [CompactSpace K]
    (p : BanachExponent) : Corollary_1_3 𝕜 K p := by
  classical
  by_cases hf : Finite K
  · letI : Finite K := hf
    exact corollary_1_3_finite K p
  letI : Infinite K := not_finite_iff_infinite.mp hf
  by_cases hc : Countable K
  · letI : Countable K := hc
    obtain ⟨α, ⟨e⟩⟩ := countableCompact_exists_ordinal_model K
    letI : Countable (OrdinalInterval α) := e.symm.injective.countable
    have hα := ordinal_lt_aleph_one_of_countable_interval α
    let eC : C(K, 𝕜) ≃L[𝕜] OrdinalContinuous 𝕜 α := continuousMapHomeomorphEquiv e
    have h := (theorem_1_1_countable (𝕜 := 𝕜) hα p).1.of_equiv (lpMapEquiv p.val eC).symm
    exact h.lp_isPrimary
  · letI : Uncountable K := ⟨hc⟩
    exact corollary_1_3_uncountable K p

end LPCK

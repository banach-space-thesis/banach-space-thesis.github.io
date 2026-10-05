import ThesisCommon.Analysis.L1SubsigmaModulus
import ThesisCommon.Analysis.L1SingularRestriction

/-! Singularity of the actual operator between trimmed L1 spaces follows
from modulus preservation for S minus/plus the constant-kernel rank one.
The compatibility of that rank one is proved from preservation of integrals
and the constant-one function by the actual sigma-algebra embeddings. -/
noncomputable section
open MeasureTheory Set
open scoped ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon
variable {X Y : Type*} {m₀ : MeasurableSpace X} {n₀ : MeasurableSpace Y}
variable {μ : @Measure X m₀} {ν : @Measure Y n₀}
variable [IsFiniteMeasure μ] [IsFiniteMeasure ν]

theorem lOneSubsigmaEmbedding_rankOne {m : MeasurableSpace X} {n : MeasurableSpace Y}
    (hm : m ≤ m₀) (hn : n ≤ n₀) :
    (lOneSubsigmaEmbedding ν hn).toContinuousLinearMap.comp
        (integralRankOne (μ.trim hm) (ν.trim hn)) =
      (@integralRankOne X Y m₀ n₀ μ ν _ _).comp
        (lOneSubsigmaEmbedding μ hm).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro f
  simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    integralRankOne_apply, map_smul, lOneSubsigmaEmbedding_indicator,
    integral_lOneSubsigmaEmbedding]

theorem isSingularOperator_lOneSubsigmaLift
    (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hS : IsSingularOperator S)
    {m : MeasurableSpace X} {n : MeasurableSpace Y} (hm : m ≤ m₀) (hn : n ≤ n₀)
    (hmap : ∀ f, S ((lOneSubsigmaEmbedding μ hm) f) ∈ lOneSubsigma ν n)
    (hminus : @L1SubsigmaPreservesModulus X Y m₀ n₀ μ ν
      (S - @integralRankOne X Y m₀ n₀ μ ν _ _) m hm)
    (hplus : @L1SubsigmaPreservesModulus X Y m₀ n₀ μ ν
      (S + @integralRankOne X Y m₀ n₀ μ ν _ _) m hm) :
    IsSingularOperator (lOneSubsigmaLift ν hn
      (S.comp (lOneSubsigmaEmbedding μ hm).toContinuousLinearMap) hmap) := by
  apply @isSingularOperator_of_modulus_preserving_restriction X Y X Y m₀ n₀ m n
    μ ν (μ.trim hm) (ν.trim hn) _ _ _ _ S hS _
    (lOneSubsigmaEmbedding μ hm).toContinuousLinearMap
    (lOneSubsigmaEmbedding ν hn).toContinuousLinearMap
    (lOneSubsigmaEmbedding ν hn).injective (lOneSubsigmaEmbedding_abs ν hn)
    (lOneSubsigmaEmbedding_lift ν hn _ hmap) (lOneSubsigmaEmbedding_rankOne hm hn)
  · simpa only [L1SubsigmaPreservesModulus, abs_lOneOperator_eq] using hminus
  · simpa only [L1SubsigmaPreservesModulus, abs_lOneOperator_eq] using hplus

end ThesisCommon

import ThesisCommon.Analysis.L1Subsigma
import ThesisCommon.Analysis.L1ModulusRestrictionMono

/-! Modulus preservation for the actual embedding of a trimmed real L1
space. A fixed countable set of ambient input vectors suffices for every
subsequent sigma-algebra enlargement. -/
noncomputable section
open MeasureTheory Set
open scoped ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon
variable {X Y : Type*} {m₀ : MeasurableSpace X} [MeasurableSpace Y]
variable {μ : @Measure X m₀} {ν : Measure Y} [IsFiniteMeasure μ]

def L1SubsigmaPreservesModulus (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν)
    {m : MeasurableSpace X} (hm : m ≤ m₀) : Prop :=
  |T.comp (lOneSubsigmaEmbedding μ hm).toContinuousLinearMap| =
    |T|.comp (lOneSubsigmaEmbedding μ hm).toContinuousLinearMap

theorem exists_countable_lOne_subsigma_modulus_witnesses
    (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) :
    ∃ W : Set (Lp ℝ 1 μ), W.Countable ∧
      ∀ (m : MeasurableSpace X) (hm : m ≤ m₀),
        W ⊆ lOneSubsigma μ m → L1SubsigmaPreservesModulus T hm := by
  obtain ⟨W, hc, hW, hsup⟩ := lOneOperatorModulus_countable_witnesses T
    (lOneIndicator μ univ MeasurableSet.univ) (lOneIndicator_nonneg _ _)
  refine ⟨W, hc, ?_⟩
  intro m hm hrange
  have h := @lOneOperatorModulus_comp_eq_of_witnesses X Y X m₀ _ m
    μ ν (μ.trim hm) _ _ T
    (lOneSubsigmaEmbedding μ hm).toContinuousLinearMap
    (lOneSubsigmaEmbedding_le_iff μ hm)
    (lOneSubsigmaEmbedding_indicator μ hm univ MeasurableSet.univ) W hW hsup
    (by simpa only [LinearIsometry.coe_toContinuousLinearMap,
      range_lOneSubsigmaEmbedding] using hrange)
  simpa only [L1SubsigmaPreservesModulus, abs_lOneOperator_eq] using h

theorem L1SubsigmaPreservesModulus.mono
    {T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν}
    {m m' : MeasurableSpace X} {hm : m ≤ m₀} {hm' : m' ≤ m₀}
    (hT : L1SubsigmaPreservesModulus T hm)
    (hsub : lOneSubsigma μ m ≤ lOneSubsigma μ m') :
    L1SubsigmaPreservesModulus T hm' := by
  unfold L1SubsigmaPreservesModulus at hT ⊢
  simp only [abs_lOneOperator_eq] at hT ⊢
  apply @lOneOperatorModulus_comp_eq_of_range_mono X Y X X m₀ _ m m'
    μ ν (μ.trim hm) (μ.trim hm') _ _ _ T
    (lOneSubsigmaEmbedding μ hm).toContinuousLinearMap
    (lOneSubsigmaEmbedding μ hm').toContinuousLinearMap
    (lOneSubsigmaEmbedding_le_iff μ hm) (lOneSubsigmaEmbedding_le_iff μ hm')
    (lOneSubsigmaEmbedding_indicator μ hm univ MeasurableSet.univ)
    (lOneSubsigmaEmbedding_indicator μ hm' univ MeasurableSet.univ)
  · simpa only [LinearIsometry.coe_toContinuousLinearMap,
      range_lOneSubsigmaEmbedding] using hsub
  · exact hT

end ThesisCommon

import PEMS.StrictlyLocalizableUniformTruncation
import ThesisCommon.Analysis.DecomposableLocalizedKernelApproximation

/-! The localized clipping approximation comes with positive bounded-range
approximants, enabling genuine weak compactness after the lattice sign lift. -/
noncomputable section
open MeasureTheory ThesisCommon
open scoped ThesisCommon.PositiveOperatorOrder
namespace PEMS
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}
attribute [local instance] strictlyLocalizablePart_isFiniteMeasure

theorem exists_positive_strictlyLocalizable_localized_boundedRange_approx
    (hμ : StrictlyLocalizable μ) (Θ : Set Y) (hΘ : MeasurableSet Θ)
    [IsFiniteMeasure (ν.restrict Θ)]
    (T : LOne ℝ μ →L[ℝ] LOne ℝ ν) (hT : 0 ≤ T)
    (k : strictlyLocalizableParts hμ → X × Y → ℝ)
    (hk : ∀ i, IsIntegralKernel (k i)
      (localizedIntegralPart Θ (strictlyLocalizableInputPiece hμ T i)))
    (hpos : ∀ i z, 0 ≤ k i z) (c : ℝ) (hc : 0 ≤ c)
    (htail : ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, ∀ i,
      ‖localizedIntegralRemainder Θ hΘ (strictlyLocalizableInputPiece hμ T i) +
        (lebesgueLpExtend (𝕜 := ℝ) Θ hΘ).toContinuousLinearMap.comp
          ((hk i).truncatedOperator n)‖ ≤ c + ε) :
    ∃ H : LOne ℝ μ →L[ℝ] LOne ℝ (ν.restrict Θ),
      IsWeaklyCompactOperator H ∧ HasPositiveBoundedRangeApproximants H ∧ 0 ≤ H ∧
      (lebesgueLpExtend (𝕜 := ℝ) Θ hΘ).toContinuousLinearMap.comp H ≤ T ∧
      ‖T - (lebesgueLpExtend (𝕜 := ℝ) Θ hΘ).toContinuousLinearMap.comp H‖ ≤ c := by
  letI : ∀ i : strictlyLocalizableParts hμ, IsFiniteMeasure (μ.restrict i.val) :=
    strictlyLocalizablePart_isFiniteMeasure hμ
  apply exists_positive_decomposable_localized_boundedRange_approx
    (fun i : strictlyLocalizableParts hμ => i.val)
    (strictlyLocalizablePart_measurable hμ) (strictlyLocalizableParts_disjoint hμ)
    (strictlyLocalizable_sum_restrict hμ) Θ hΘ T
    (fun i => localizedIntegralRemainder Θ hΘ (strictlyLocalizableInputPiece hμ T i))
    (fun i => localizedIntegralPart Θ (strictlyLocalizableInputPiece hμ T i))
    (fun i => localizedIntegralRemainder_nonneg Θ hΘ (strictlyLocalizableInputPiece_nonneg hμ hT i))
    k hk hpos _ ‖T‖ (norm_nonneg T) _ c hc htail
  · intro i
    exact (localizedIntegralRemainder_add_part Θ hΘ (strictlyLocalizableInputPiece hμ T i)).symm
  · intro i
    exact (norm_localizedIntegralPart_le Θ (strictlyLocalizableInputPiece hμ T i)).trans
      (norm_strictlyLocalizableInputPiece_le hμ T i)



theorem exists_positive_strictlyLocalizable_alpha_boundedRange_approximation
    (hμ : StrictlyLocalizable μ) (Θ : Set Y) (hΘ : MeasurableSet Θ)
    [IsFiniteMeasure (ν.restrict Θ)]
    (T : LOne ℝ μ →L[ℝ] LOne ℝ ν) (hT : 0 ≤ T) :
    ∃ H : LOne ℝ μ →L[ℝ] LOne ℝ (ν.restrict Θ),
      IsWeaklyCompactOperator H ∧ HasPositiveBoundedRangeApproximants H ∧ 0 ≤ H ∧
      (lebesgueLpExtend (𝕜 := ℝ) Θ hΘ).toContinuousLinearMap.comp H ≤ T ∧
      ‖T - (lebesgueLpExtend (𝕜 := ℝ) Θ hΘ).toContinuousLinearMap.comp H‖ ≤ alphaTheta T Θ := by
  obtain ⟨k, hk, hpos⟩ := exists_strictlyLocalizable_nonneg_localized_kernels hμ Θ T hT
  exact exists_positive_strictlyLocalizable_localized_boundedRange_approx hμ Θ hΘ T hT k hk hpos
    (alphaTheta T Θ) (alphaTheta_bounds T Θ hΘ).1
    (strictlyLocalizable_uniform_localized_truncation hμ Θ hΘ T hT k hk hpos)

end PEMS

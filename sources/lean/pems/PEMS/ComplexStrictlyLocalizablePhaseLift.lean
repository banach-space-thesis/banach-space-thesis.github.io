import PEMS.StrictlyLocalizableDecomposition
import ThesisCommon.Analysis.DecomposableComplexPhaseLift

/-! Complex phase lifting from the actual finite-measure decomposition of
a strictly localizable input. No countability of the partition is imposed. -/
noncomputable section
open MeasureTheory ThesisCommon
open scoped ThesisCommon.PositiveOperatorOrder
namespace PEMS
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}

theorem exists_complex_strictlyLocalizable_localized_phaseLift
    (hμ : StrictlyLocalizable μ) (Θ : Set Y) (hΘ : MeasurableSet Θ)
    [IsFiniteMeasure (ν.restrict Θ)]
    (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν)
    (H : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 (ν.restrict Θ)) (hH : 0 ≤ H)
    (hApprox : HasPositiveBoundedRangeApproximants H)
    (hHM : (lebesgueLpExtend (𝕜 := ℝ) Θ hΘ).toContinuousLinearMap.comp H ≤
      complexL1OperatorModulus T) :
    ∃ W : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν, IsWeaklyCompactOperator W ∧
      L1OperatorSupportedOn Θ W ∧
      complexL1OperatorModulus W =
        (lebesgueLpExtend (𝕜 := ℝ) Θ hΘ).toContinuousLinearMap.comp H ∧
      complexL1OperatorModulus (T - W) = complexL1OperatorModulus T -
        (lebesgueLpExtend (𝕜 := ℝ) Θ hΘ).toContinuousLinearMap.comp H := by
  letI : ∀ i : strictlyLocalizableParts hμ, IsFiniteMeasure (μ.restrict i.val) :=
    strictlyLocalizablePart_isFiniteMeasure hμ
  obtain ⟨V, _, hMV, herr⟩ := exists_decomposable_complex_localized_phaseLift
    (fun i : strictlyLocalizableParts hμ => i.val)
    (strictlyLocalizablePart_measurable hμ) (strictlyLocalizableParts_disjoint hμ)
    (strictlyLocalizable_sum_restrict hμ) T Θ hΘ H hH hApprox hHM
  let W := (lebesgueLpExtend (𝕜 := ℂ) (μ := ν) Θ hΘ).toContinuousLinearMap.comp V
  have hMW : complexL1OperatorModulus W =
      (lebesgueLpExtend (𝕜 := ℝ) Θ hΘ).toContinuousLinearMap.comp H := by
    dsimp only [W]
    rw [complexL1OperatorModulus_outputExtend Θ hΘ, hMV]
  exact ⟨W, hApprox.weaklyCompact_of_complex_modulus_le_extend Θ hΘ hMW.le,
    l1OperatorSupportedOn_of_complex_modulus_le_extend Θ hΘ hMW.le, hMW, herr⟩

end PEMS

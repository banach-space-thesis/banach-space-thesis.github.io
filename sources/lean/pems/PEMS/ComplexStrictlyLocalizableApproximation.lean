import PEMS.ComplexStrictlyLocalizablePhaseLift
import PEMS.StrictlyLocalizableBoundedApproximation
import PEMS.SupportedWeakEssentialNorm
import PEMS.ComplexL1WeakNoncompactnessModulus

/-! The complex form of Theorem 4.18 for finite output localizations and
arbitrary strictly localizable input spaces. The supported weak essential
norm equals alphaTheta and is attained by a genuine weakly compact map. -/
noncomputable section
open MeasureTheory ThesisCommon
open scoped ThesisCommon.PositiveOperatorOrder
namespace PEMS
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}

theorem exists_complex_strictlyLocalizable_alpha_approximation
    (hμ : StrictlyLocalizable μ) (Θ : Set Y) (hΘ : MeasurableSet Θ)
    [IsFiniteMeasure (ν.restrict Θ)]
    (T : LOne ℂ μ →L[ℂ] LOne ℂ ν) :
    ∃ W : LOne ℂ μ →L[ℂ] LOne ℂ ν, IsWeaklyCompactOperator W ∧
      L1OperatorSupportedOn Θ W ∧ ‖T - W‖ ≤ alphaTheta T Θ := by
  obtain ⟨H, _, hHa, hH0, hHT, herr⟩ :=
    exists_positive_strictlyLocalizable_alpha_boundedRange_approximation hμ Θ hΘ
      (complexL1OperatorModulus T) (complexL1OperatorModulus_nonneg T)
  obtain ⟨W, hW, hs, _, he⟩ :=
    exists_complex_strictlyLocalizable_localized_phaseLift hμ Θ hΘ T H hH0 hHa hHT
  refine ⟨W, hW, hs, ?_⟩
  calc
    ‖T - W‖ = ‖complexL1OperatorModulus (T - W)‖ := (norm_complexL1OperatorModulus _).symm
    _ = ‖complexL1OperatorModulus T -
        (lebesgueLpExtend (𝕜 := ℝ) Θ hΘ).toContinuousLinearMap.comp H‖ := by rw [he]
    _ ≤ alphaTheta (complexL1OperatorModulus T) Θ := herr
    _ = alphaTheta T Θ := alphaTheta_complex_modulus T Θ hΘ

theorem supportedWeakEssentialNorm_eq_alphaTheta_complex_strictlyLocalizable
    (hμ : StrictlyLocalizable μ) (Θ : Set Y) (hΘ : MeasurableSet Θ)
    [IsFiniteMeasure (ν.restrict Θ)]
    (T : LOne ℂ μ →L[ℂ] LOne ℂ ν) :
    supportedWeakEssentialNorm Θ T = alphaTheta T Θ := by
  obtain ⟨W, hW, hs, herr⟩ := exists_complex_strictlyLocalizable_alpha_approximation hμ Θ hΘ T
  exact le_antisymm ((supportedWeakEssentialNorm_le Θ T hW hs).trans herr)
    (proposition_4_16_complex T Θ hΘ)

theorem exists_complex_finite_supported_bestApproximation
    (hμ : StrictlyLocalizable μ) (Θ : Set Y) (hΘ : MeasurableSet Θ)
    [IsFiniteMeasure (ν.restrict Θ)]
    (T : LOne ℂ μ →L[ℂ] LOne ℂ ν) :
    ∃ W : LOne ℂ μ →L[ℂ] LOne ℂ ν, IsWeaklyCompactOperator W ∧
      L1OperatorSupportedOn Θ W ∧ ‖T - W‖ = supportedWeakEssentialNorm Θ T := by
  obtain ⟨W, hW, hs, herr⟩ := exists_complex_strictlyLocalizable_alpha_approximation hμ Θ hΘ T
  refine ⟨W, hW, hs, le_antisymm ?_ (supportedWeakEssentialNorm_le Θ T hW hs)⟩
  exact herr.trans (proposition_4_16_complex T Θ hΘ)

end PEMS

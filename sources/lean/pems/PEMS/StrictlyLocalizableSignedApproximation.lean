import PEMS.StrictlyLocalizableBoundedApproximation
import PEMS.SupportedWeakEssentialNorm
import PEMS.L1WeakNoncompactnessModulus
import ThesisCommon.Analysis.L1SupportedDomination

/-! The signed real form of Theorem 4.18 on arbitrary strictly localizable
input spaces and finite output localizations. The supported distance is
attained and equals the actual small-set functional alphaTheta. -/
noncomputable section
open MeasureTheory ThesisCommon
open scoped ThesisCommon.PositiveOperatorOrder
namespace PEMS
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}

theorem exists_real_strictlyLocalizable_alpha_approximation
    (hμ : StrictlyLocalizable μ) (Θ : Set Y) (hΘ : MeasurableSet Θ)
    [IsFiniteMeasure (ν.restrict Θ)]
    (T : LOne ℝ μ →L[ℝ] LOne ℝ ν) :
    ∃ W : LOne ℝ μ →L[ℝ] LOne ℝ ν, IsWeaklyCompactOperator W ∧
      L1OperatorSupportedOn Θ W ∧ ‖T - W‖ ≤ alphaTheta T Θ := by
  obtain ⟨H, _, hHa, hH0, hHT, herr⟩ :=
    exists_positive_strictlyLocalizable_alpha_boundedRange_approximation hμ Θ hΘ |T| (abs_nonneg T)
  let G := (lebesgueLpExtend (𝕜 := ℝ) Θ hΘ).toContinuousLinearMap.comp H
  have hG0 : 0 ≤ G := fun f hf => lebesgueL1Extend_nonneg Θ hΘ (H f) (hH0 f hf)
  let W := latticeSignLift T G
  have hWabs : |W| = G := abs_latticeSignLift T hG0 hHT
  have hWdom : |W| ≤ G := hWabs.le
  refine ⟨W, hHa.weaklyCompact_of_abs_le_extend Θ hΘ hWdom,
    l1OperatorSupportedOn_of_abs_le_extend Θ hΘ hWdom, ?_⟩
  calc
    ‖T - W‖ = ‖|T - W|‖ := (norm_abs_lOneOperator _).symm
    _ = ‖|T| - G‖ := by rw [show |T - W| = |T| - G from abs_sub_latticeSignLift T hG0 hHT]
    _ ≤ alphaTheta |T| Θ := herr
    _ = alphaTheta T Θ := alphaTheta_abs T Θ hΘ

theorem supportedWeakEssentialNorm_eq_alphaTheta_real_strictlyLocalizable
    (hμ : StrictlyLocalizable μ) (Θ : Set Y) (hΘ : MeasurableSet Θ)
    [IsFiniteMeasure (ν.restrict Θ)]
    (T : LOne ℝ μ →L[ℝ] LOne ℝ ν) :
    supportedWeakEssentialNorm Θ T = alphaTheta T Θ := by
  obtain ⟨W, hW, hs, herr⟩ := exists_real_strictlyLocalizable_alpha_approximation hμ Θ hΘ T
  exact le_antisymm ((supportedWeakEssentialNorm_le Θ T hW hs).trans herr)
    (proposition_4_16_real T Θ hΘ)

theorem exists_real_finite_supported_bestApproximation
    (hμ : StrictlyLocalizable μ) (Θ : Set Y) (hΘ : MeasurableSet Θ)
    [IsFiniteMeasure (ν.restrict Θ)]
    (T : LOne ℝ μ →L[ℝ] LOne ℝ ν) :
    ∃ W : LOne ℝ μ →L[ℝ] LOne ℝ ν, IsWeaklyCompactOperator W ∧
      L1OperatorSupportedOn Θ W ∧ ‖T - W‖ = supportedWeakEssentialNorm Θ T := by
  obtain ⟨W, hW, hs, herr⟩ := exists_real_strictlyLocalizable_alpha_approximation hμ Θ hΘ T
  refine ⟨W, hW, hs, le_antisymm ?_ (supportedWeakEssentialNorm_le Θ T hW hs)⟩
  exact herr.trans (proposition_4_16_real T Θ hΘ)

end PEMS

import PEMS.StrictlyLocalizableOperators
import ThesisCommon.Analysis.L1LocalizedIntegralPart
import ThesisCommon.Analysis.DecomposableLocalizedKernelClipping

/-! Canonical finite input pieces and the uniform-budget gluing step of
Theorem 4.18. The uniform tail estimate is kept explicit here; it is the
quantitative content of Proposition 4.17. -/
noncomputable section
open MeasureTheory ThesisCommon
open scoped ThesisCommon.PositiveOperatorOrder
namespace PEMS
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}

def strictlyLocalizableInputPiece {𝕜 : Type*} [RCLike 𝕜]
    (hμ : StrictlyLocalizable μ) (T : LOne 𝕜 μ →L[𝕜] LOne 𝕜 ν)
    (i : strictlyLocalizableParts hμ) : LOne 𝕜 (μ.restrict i.val) →L[𝕜] LOne 𝕜 ν :=
  T.comp (lebesgueLpExtend (𝕜 := 𝕜) i.val (strictlyLocalizablePart_measurable hμ i)).toContinuousLinearMap

theorem norm_strictlyLocalizableInputPiece_le {𝕜 : Type*} [RCLike 𝕜]
    (hμ : StrictlyLocalizable μ) (T : LOne 𝕜 μ →L[𝕜] LOne 𝕜 ν)
    (i : strictlyLocalizableParts hμ) : ‖strictlyLocalizableInputPiece hμ T i‖ ≤ ‖T‖ :=
  (T.opNorm_comp_le _).trans ((mul_le_mul_of_nonneg_left
    (lebesgueLpExtend (𝕜 := 𝕜) (E := 𝕜) (p := 1) i.val
      (strictlyLocalizablePart_measurable hμ i)).norm_toContinuousLinearMap_le
    (norm_nonneg T)).trans_eq (mul_one _))

theorem strictlyLocalizableInputPiece_nonneg (hμ : StrictlyLocalizable μ)
    {T : LOne ℝ μ →L[ℝ] LOne ℝ ν} (hT : 0 ≤ T) (i : strictlyLocalizableParts hμ) :
    0 ≤ strictlyLocalizableInputPiece hμ T i := fun f hf =>
  hT _ (lebesgueL1Extend_nonneg i.val (strictlyLocalizablePart_measurable hμ i) f hf)

attribute [local instance] strictlyLocalizablePart_isFiniteMeasure

theorem exists_strictlyLocalizable_nonneg_localized_kernels
    (hμ : StrictlyLocalizable μ) (Θ : Set Y) [IsFiniteMeasure (ν.restrict Θ)]
    (T : LOne ℝ μ →L[ℝ] LOne ℝ ν) (hT : 0 ≤ T) :
    ∃ k : strictlyLocalizableParts hμ → X × Y → ℝ,
      (∀ i, IsIntegralKernel (k i) (localizedIntegralPart Θ (strictlyLocalizableInputPiece hμ T i))) ∧
      ∀ i z, 0 ≤ k i z := by
  choose k hk using fun i : strictlyLocalizableParts hμ =>
    localizedIntegralPart_isIntegral Θ (strictlyLocalizableInputPiece hμ T i)
  refine ⟨fun i z => |k i z|, fun i => ?_, fun i z => abs_nonneg _⟩
  simpa only [abs_of_nonneg (localizedIntegralPart_nonneg Θ
    (strictlyLocalizableInputPiece_nonneg hμ hT i))] using (hk i).abs

theorem exists_positive_strictlyLocalizable_localized_budget_approx
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
      IsWeaklyCompactOperator H ∧ 0 ≤ H ∧
      (lebesgueLpExtend (𝕜 := ℝ) Θ hΘ).toContinuousLinearMap.comp H ≤ T ∧
      ‖T - (lebesgueLpExtend (𝕜 := ℝ) Θ hΘ).toContinuousLinearMap.comp H‖ ≤ c := by
  letI : ∀ i : strictlyLocalizableParts hμ, IsFiniteMeasure (μ.restrict i.val) :=
    strictlyLocalizablePart_isFiniteMeasure hμ
  apply exists_positive_weaklyCompact_decomposable_localized_budget_approx
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

end PEMS

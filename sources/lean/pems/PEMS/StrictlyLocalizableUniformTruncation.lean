import PEMS.LocalizedTruncationLowerBound
import PEMS.StrictlyLocalizableBudgetApproximation

/-! A single truncation threshold works over all finite input pieces of a
strictly localizable measure. This supplies Proposition 4.17's quantitative
lower step and the positive approximation of Theorem 4.18. -/
noncomputable section
open MeasureTheory Set Filter ThesisCommon
open scoped ENNReal ThesisCommon.PositiveOperatorOrder
namespace PEMS
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}
attribute [local instance] strictlyLocalizablePart_isFiniteMeasure

theorem strictlyLocalizable_uniform_localized_truncation
    (hμ : StrictlyLocalizable μ) (Θ : Set Y) (hΘ : MeasurableSet Θ)
    [IsFiniteMeasure (ν.restrict Θ)]
    (T : LOne ℝ μ →L[ℝ] LOne ℝ ν) (hT : 0 ≤ T)
    (k : strictlyLocalizableParts hμ → X × Y → ℝ)
    (hk : ∀ i, IsIntegralKernel (k i)
      (localizedIntegralPart Θ (strictlyLocalizableInputPiece hμ T i)))
    (hpos : ∀ i z, 0 ≤ k i z) :
    ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, ∀ i,
      ‖localizedIntegralRemainder Θ hΘ (strictlyLocalizableInputPiece hμ T i) +
        (lebesgueLpExtend (𝕜 := ℝ) Θ hΘ).toContinuousLinearMap.comp
          ((hk i).truncatedOperator n)‖ ≤ alphaTheta T Θ + ε := by
  intro ε hε
  obtain ⟨q, ⟨δ, hδ, rfl⟩, hq⟩ := exists_lt_of_csInf_lt
    (s := {q : ℝ | ∃ δ : ℝ, 0 < δ ∧ q = smallSetSup T Θ δ})
    ⟨_, 1, zero_lt_one, rfl⟩
    (show alphaTheta T Θ < alphaTheta T Θ + ε by linarith)
  obtain ⟨n, hn⟩ := exists_nat_gt (max (2 * ‖T‖ / δ) 0)
  have hnpos : 0 < (n : ℝ) := (le_max_right _ _).trans_lt hn
  have hsize : 2 * ‖T‖ / (n : ℝ) < δ := by
    apply (div_lt_iff₀ hnpos).mpr
    have hh := (div_lt_iff₀ hδ).mp ((le_max_left _ _).trans_lt hn)
    nlinarith
  refine ⟨n, fun i => ?_⟩
  let J := (lebesgueLpExtend (𝕜 := ℝ) (E := ℝ) (p := 1) (μ := μ)
    i.val (strictlyLocalizablePart_measurable hμ i)).toContinuousLinearMap
  have hJ : ‖J‖ ≤ 1 := (lebesgueLpExtend (𝕜 := ℝ) (E := ℝ) (p := 1)
    i.val (strictlyLocalizablePart_measurable hμ i)).norm_toContinuousLinearMap_le
  have hKC := (norm_localizedIntegralPart_le Θ (strictlyLocalizableInputPiece hμ T i)).trans
    (norm_strictlyLocalizableInputPiece_le hμ T i)
  exact (localized_truncation_le_smallSetSup_of_input_contraction T J hJ
    (strictlyLocalizableInputPiece_nonneg hμ hT i) Θ hΘ (hk i) (hpos i)
    (norm_nonneg T) hKC hδ hnpos hsize).trans hq.le

theorem exists_positive_strictlyLocalizable_alpha_approximation
    (hμ : StrictlyLocalizable μ) (Θ : Set Y) (hΘ : MeasurableSet Θ)
    [IsFiniteMeasure (ν.restrict Θ)]
    (T : LOne ℝ μ →L[ℝ] LOne ℝ ν) (hT : 0 ≤ T) :
    ∃ H : LOne ℝ μ →L[ℝ] LOne ℝ (ν.restrict Θ),
      IsWeaklyCompactOperator H ∧ 0 ≤ H ∧
      (lebesgueLpExtend (𝕜 := ℝ) Θ hΘ).toContinuousLinearMap.comp H ≤ T ∧
      ‖T - (lebesgueLpExtend (𝕜 := ℝ) Θ hΘ).toContinuousLinearMap.comp H‖ ≤ alphaTheta T Θ := by
  obtain ⟨k, hk, hpos⟩ := exists_strictlyLocalizable_nonneg_localized_kernels hμ Θ T hT
  exact exists_positive_strictlyLocalizable_localized_budget_approx hμ Θ hΘ T hT k hk hpos
    (alphaTheta T Θ) (alphaTheta_bounds T Θ hΘ).1
    (strictlyLocalizable_uniform_localized_truncation hμ Θ hΘ T hT k hk hpos)

end PEMS

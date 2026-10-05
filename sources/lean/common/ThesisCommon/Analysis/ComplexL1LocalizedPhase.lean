import ThesisCommon.Analysis.ComplexL1ModulusRestrictions
import ThesisCommon.Analysis.ComplexIntegralPhaseLift

/-! Exact phase lifts on a sigma-finite output band of an arbitrary ambient
measure space. The ambient error modulus retains its full outside mass. -/
noncomputable section
open MeasureTheory Set
open scoped ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}

theorem complex_modulus_sub_outputExtend_of_localized
    (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν) (Θ : Set Y) (hΘ : MeasurableSet Θ)
    (V : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 (ν.restrict Θ))
    (H : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 (ν.restrict Θ))
    (herr : complexL1OperatorModulus ((lebesgueLpRestrict (𝕜 := ℂ) Θ).comp T - V) =
      complexL1OperatorModulus ((lebesgueLpRestrict (𝕜 := ℂ) Θ).comp T) - H) :
    complexL1OperatorModulus (T - (lebesgueLpExtend (𝕜 := ℂ) Θ hΘ).toContinuousLinearMap.comp V) =
      complexL1OperatorModulus T - (lebesgueLpExtend (𝕜 := ℝ) Θ hΘ).toContinuousLinearMap.comp H := by
  let U := T - (lebesgueLpExtend (𝕜 := ℂ) Θ hΘ).toContinuousLinearMap.comp V
  have hout : (lpCutL Θᶜ hΘ.compl).comp U = (lpCutL Θᶜ hΘ.compl).comp T := by
    apply ContinuousLinearMap.ext
    intro f
    change lpCutL Θᶜ hΘ.compl (T f - lebesgueLpExtend (𝕜 := ℂ) Θ hΘ (V f)) = _
    rw [map_sub]
    change lpCut Θᶜ hΘ.compl (T f) - lpCut Θᶜ hΘ.compl
      (lebesgueLpExtend (𝕜 := ℂ) Θ hΘ (V f)) = lpCut Θᶜ hΘ.compl (T f)
    rw [lpCut_compl_extend, sub_zero]
  have hin : (lebesgueLpRestrict (𝕜 := ℂ) Θ).comp U =
      (lebesgueLpRestrict (𝕜 := ℂ) Θ).comp T - V := by
    apply ContinuousLinearMap.ext
    intro f
    change lebesgueLpRestrict (𝕜 := ℂ) Θ
      (T f - lebesgueLpExtend (𝕜 := ℂ) Θ hΘ (V f)) = _
    rw [map_sub, lebesgueLpRestrict_extend]
    rfl
  calc
    complexL1OperatorModulus U = (lpCutL Θᶜ hΘ.compl).comp (complexL1OperatorModulus U) +
        (lebesgueLpExtend (𝕜 := ℝ) Θ hΘ).toContinuousLinearMap.comp
          ((lebesgueLpRestrict (𝕜 := ℝ) Θ).comp (complexL1OperatorModulus U)) :=
      (lOne_localized_decomposition (complexL1OperatorModulus U) Θ hΘ).symm
    _ = (lpCutL Θᶜ hΘ.compl).comp (complexL1OperatorModulus T) +
        (lebesgueLpExtend (𝕜 := ℝ) Θ hΘ).toContinuousLinearMap.comp
          ((lebesgueLpRestrict (𝕜 := ℝ) Θ).comp (complexL1OperatorModulus T) - H) := by
      rw [← complexL1OperatorModulus_outputCut, hout, complexL1OperatorModulus_outputCut,
        ← complexL1OperatorModulus_outputRestrict U Θ hΘ, hin, herr,
        complexL1OperatorModulus_outputRestrict T Θ hΘ]
    _ = _ := by rw [ContinuousLinearMap.comp_sub, ← add_sub_assoc, lOne_localized_decomposition]

theorem exists_complex_localized_integral_phaseLift [SigmaFinite μ]
    (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν) (Θ : Set Y) (hΘ : MeasurableSet Θ)
    [SigmaFinite (ν.restrict Θ)]
    (H : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 (ν.restrict Θ)) (hH : 0 ≤ H)
    (hHI : IsIntegralOperator H)
    (hHM : H ≤ (lebesgueLpRestrict (𝕜 := ℝ) Θ).comp (complexL1OperatorModulus T)) :
    ∃ V : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 (ν.restrict Θ), IsIntegralOperator V ∧
      complexL1OperatorModulus V = H ∧
      complexL1OperatorModulus (T - (lebesgueLpExtend (𝕜 := ℂ) Θ hΘ).toContinuousLinearMap.comp V) =
        complexL1OperatorModulus T - (lebesgueLpExtend (𝕜 := ℝ) Θ hΘ).toContinuousLinearMap.comp H := by
  have hHP : H ≤ integralBandProjection
      (complexL1OperatorModulus ((lebesgueLpRestrict (𝕜 := ℂ) Θ).comp T)) := by
    rw [complexL1OperatorModulus_outputRestrict T Θ hΘ]
    have h := positive_operator_monotone integralBandProjection_nonneg hHM
    rwa [integralBandProjection_eq_self hHI] at h
  obtain ⟨V, hV, hMV, herr⟩ := exists_complex_integral_phaseLift
    ((lebesgueLpRestrict (𝕜 := ℂ) Θ).comp T) hH hHP
  exact ⟨V, hV, hMV, complex_modulus_sub_outputExtend_of_localized T Θ hΘ V H herr⟩

end ThesisCommon

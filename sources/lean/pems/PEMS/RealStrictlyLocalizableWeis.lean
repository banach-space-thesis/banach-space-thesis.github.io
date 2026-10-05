import PEMS.StrictlyLocalizableSignedApproximation
import ThesisCommon.Analysis.SupportedBestApproximationNormalization
import ThesisCommon.Analysis.SupportedWeakEssentialNormAssembly

/-! The actual real Theorem 1.1 on strictly localizable input spaces.
Finite supported attainment is transported to every measurable sigma-finite
support by a proved positive density isometry; a genuine minimizing sequence
then yields a global best approximant. The exact original localized
functional is identified with the weak essential norm. The output measure
is arbitrary, so the source's strictly localizable output hypothesis is
retained in the final numbered statement but is not needed by this proof. -/
noncomputable section
open MeasureTheory Set ThesisCommon
open scoped ThesisCommon.PositiveOperatorOrder
namespace PEMS
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}

theorem exists_real_sigmaFinite_supported_bestApproximation
    (hμ : StrictlyLocalizable μ) (Θ : Set Y) (hΘ : MeasurableSet Θ)
    [SigmaFinite (ν.restrict Θ)] (T : LOne ℝ μ →L[ℝ] LOne ℝ ν) :
    ∃ W : LOne ℝ μ →L[ℝ] LOne ℝ ν, IsWeaklyCompactOperator W ∧
      L1OperatorSupportedOn Θ W ∧ ‖T - W‖ = supportedWeakEssentialNorm Θ T := by
  apply exists_supported_bestApproximation_sigmaFinite_of_finite Θ hΘ T
  intro ν' hfin R
  letI := hfin
  exact exists_real_finite_supported_bestApproximation hμ Θ hΘ R

theorem weakEssentialNorm_eq_localized_real_strictlyLocalizable
    (hμ : StrictlyLocalizable μ) (T : LOne ℝ μ →L[ℝ] LOne ℝ ν) :
    weakEssentialNorm T = localizedWeakNoncompactness T := by
  apply le_antisymm _ (localizedWeakNoncompactness_le_weakEssentialNorm_arbitrary_output T)
  apply le_csInf
  · exact ⟨_, ∅, MeasurableSet.empty, by simp, rfl⟩
  · rintro r ⟨Θ, hΘ, hfin, rfl⟩
    letI : IsFiniteMeasure (ν.restrict Θ) := isFiniteMeasure_restrict.mpr hfin.ne
    rw [← supportedWeakEssentialNorm_eq_alphaTheta_real_strictlyLocalizable hμ Θ hΘ T]
    exact weakEssentialNorm_le_supported Θ T

theorem weakEssentialNorm_abs_real_strictlyLocalizable
    (hμ : StrictlyLocalizable μ) (T : LOne ℝ μ →L[ℝ] LOne ℝ ν) :
    weakEssentialNorm |T| = weakEssentialNorm T := by
  rw [weakEssentialNorm_eq_localized_real_strictlyLocalizable hμ,
    localizedWeakNoncompactness_abs, weakEssentialNorm_eq_localized_real_strictlyLocalizable hμ]

theorem weaklyCompact_abs_iff_real_strictlyLocalizable
    (hμ : StrictlyLocalizable μ) (T : LOne ℝ μ →L[ℝ] LOne ℝ ν) :
    IsWeaklyCompactOperator |T| ↔ IsWeaklyCompactOperator T := by
  rw [← weakEssentialNorm_eq_zero_iff |T|, ← weakEssentialNorm_eq_zero_iff T,
    weakEssentialNorm_abs_real_strictlyLocalizable hμ]

theorem exists_real_strictlyLocalizable_weaklyCompact_bestApproximation
    (hμ : StrictlyLocalizable μ) (T : LOne ℝ μ →L[ℝ] LOne ℝ ν) :
    ∃ W : LOne ℝ μ →L[ℝ] LOne ℝ ν, IsWeaklyCompactOperator W ∧
      ‖T - W‖ = weakEssentialNorm T := by
  apply exists_real_weaklyCompact_bestApproximation_of_supported T
  intro Θ hΘ hσ
  letI := hσ
  exact exists_real_sigmaFinite_supported_bestApproximation hμ Θ hΘ T

theorem real_strictlyLocalizable_attained_weis_formula
    (hμ : StrictlyLocalizable μ) (T : LOne ℝ μ →L[ℝ] LOne ℝ ν) :
    ∃ W : LOne ℝ μ →L[ℝ] LOne ℝ ν, IsWeaklyCompactOperator W ∧
      weakEssentialNorm T = ‖T - W‖ ∧ ‖T - W‖ = localizedWeakNoncompactness T := by
  obtain ⟨W, hW, heq⟩ := exists_real_strictlyLocalizable_weaklyCompact_bestApproximation hμ T
  exact ⟨W, hW, heq.symm, heq.trans (weakEssentialNorm_eq_localized_real_strictlyLocalizable hμ T)⟩

theorem theorem_1_1_real (T : LOne ℝ μ →L[ℝ] LOne ℝ ν) : Theorem_1_1 μ ν T := by
  intro hμ _
  exact real_strictlyLocalizable_attained_weis_formula hμ T

end PEMS

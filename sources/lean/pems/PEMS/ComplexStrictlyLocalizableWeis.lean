import PEMS.ComplexStrictlyLocalizableApproximation
import PEMS.RealStrictlyLocalizableWeis
import ThesisCommon.Analysis.SupportedBestApproximationNormalization
import ThesisCommon.Analysis.SupportedWeakEssentialNormAssembly

/-! The complex Theorem 1.1 on strictly localizable input spaces. Actual
finite supported best approximations are transported by the proved complex
density isometry to sigma-finite supports. A minimizing sequence of genuine
weakly compact operators supplies one such support and a global best
approximation. No representation or approximation hypothesis is assumed.
The output measure may be arbitrary; the numbered statement retains both
strict localizability hypotheses from the source. -/
noncomputable section
open MeasureTheory Set ThesisCommon
namespace PEMS
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}

theorem exists_complex_sigmaFinite_supported_bestApproximation
    (hμ : StrictlyLocalizable μ) (Θ : Set Y) (hΘ : MeasurableSet Θ)
    [SigmaFinite (ν.restrict Θ)] (T : LOne ℂ μ →L[ℂ] LOne ℂ ν) :
    ∃ W : LOne ℂ μ →L[ℂ] LOne ℂ ν, IsWeaklyCompactOperator W ∧
      L1OperatorSupportedOn Θ W ∧ ‖T - W‖ = supportedWeakEssentialNorm Θ T := by
  apply exists_supported_bestApproximation_sigmaFinite_of_finite Θ hΘ T
  intro ν' hfin R
  letI := hfin
  exact exists_complex_finite_supported_bestApproximation hμ Θ hΘ R

theorem weakEssentialNorm_eq_localized_complex_strictlyLocalizable
    (hμ : StrictlyLocalizable μ) (T : LOne ℂ μ →L[ℂ] LOne ℂ ν) :
    weakEssentialNorm T = localizedWeakNoncompactness T := by
  apply le_antisymm _ (localizedWeakNoncompactness_le_complex_weakEssentialNorm T)
  apply le_csInf
  · exact ⟨_, ∅, MeasurableSet.empty, by simp, rfl⟩
  · rintro r ⟨Θ, hΘ, hfin, rfl⟩
    letI : IsFiniteMeasure (ν.restrict Θ) := isFiniteMeasure_restrict.mpr hfin.ne
    rw [← supportedWeakEssentialNorm_eq_alphaTheta_complex_strictlyLocalizable hμ Θ hΘ T]
    exact weakEssentialNorm_le_supported Θ T

theorem weakEssentialNorm_complex_modulus_strictlyLocalizable
    (hμ : StrictlyLocalizable μ) (T : LOne ℂ μ →L[ℂ] LOne ℂ ν) :
    weakEssentialNorm (complexL1OperatorModulus T) = weakEssentialNorm T := by
  rw [weakEssentialNorm_eq_localized_real_strictlyLocalizable hμ,
    localizedWeakNoncompactness_complex_modulus,
    weakEssentialNorm_eq_localized_complex_strictlyLocalizable hμ]

theorem weaklyCompact_complex_modulus_iff_strictlyLocalizable
    (hμ : StrictlyLocalizable μ) (T : LOne ℂ μ →L[ℂ] LOne ℂ ν) :
    IsWeaklyCompactOperator (complexL1OperatorModulus T) ↔ IsWeaklyCompactOperator T := by
  rw [← weakEssentialNorm_eq_zero_iff (complexL1OperatorModulus T),
    ← weakEssentialNorm_eq_zero_iff T, weakEssentialNorm_complex_modulus_strictlyLocalizable hμ]

theorem exists_complex_strictlyLocalizable_weaklyCompact_bestApproximation
    (hμ : StrictlyLocalizable μ) (T : LOne ℂ μ →L[ℂ] LOne ℂ ν) :
    ∃ W : LOne ℂ μ →L[ℂ] LOne ℂ ν, IsWeaklyCompactOperator W ∧
      ‖T - W‖ = weakEssentialNorm T := by
  apply exists_complex_weaklyCompact_bestApproximation_of_supported T
  intro Θ hΘ hσ
  letI := hσ
  exact exists_complex_sigmaFinite_supported_bestApproximation hμ Θ hΘ T

theorem complex_strictlyLocalizable_attained_weis_formula
    (hμ : StrictlyLocalizable μ) (T : LOne ℂ μ →L[ℂ] LOne ℂ ν) :
    ∃ W : LOne ℂ μ →L[ℂ] LOne ℂ ν, IsWeaklyCompactOperator W ∧
      weakEssentialNorm T = ‖T - W‖ ∧ ‖T - W‖ = localizedWeakNoncompactness T := by
  obtain ⟨W, hW, heq⟩ := exists_complex_strictlyLocalizable_weaklyCompact_bestApproximation hμ T
  exact ⟨W, hW, heq.symm,
    heq.trans (weakEssentialNorm_eq_localized_complex_strictlyLocalizable hμ T)⟩

theorem theorem_1_1_complex (T : LOne ℂ μ →L[ℂ] LOne ℂ ν) : Theorem_1_1 μ ν T := by
  intro hμ _
  exact complex_strictlyLocalizable_attained_weis_formula hμ T

end PEMS

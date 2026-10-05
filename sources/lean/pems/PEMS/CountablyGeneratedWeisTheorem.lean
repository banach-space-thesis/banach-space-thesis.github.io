import PEMS.MainStatements
import PEMS.RealWeisEssSup
import PEMS.CountablyGeneratedWeisBestApproximation
import ThesisCommon.Analysis.BanachAdjointNorm

/-! The complete real-kernel statement of Theorem 4.4, including its
singular-operator consequence, and the attained norm formula on these spaces.
The original main theorem has a wider scalar and measure-space scope. -/
noncomputable section
open MeasureTheory Set ThesisCommon
open scoped ENNReal ThesisCommon.PositiveOperatorOrder
namespace PEMS
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}
variable [MeasurableSpace.CountablyGenerated X] [MeasurableSpace.CountablyGenerated Y]
variable [IsFiniteMeasure μ] [IsFiniteMeasure ν]

theorem singular_countablyGenerated_alpha_eq_norm
    (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hS : IsSingularOperator S) :
    alphaTheta S univ = ‖S‖ := by
  have h := real_countablyGenerated_weis_essSup_formula S 0 hS isIntegralKernel_zero
  simp only [add_zero, truncatedKernel, Set.indicator_zero, abs_zero, integral_zero,
    Set.range_const, csInf_singleton] at h
  rw [← localizedWeakNoncompactness_eq_alphaTheta_univ, ← h.1, h.2,
    ← norm_eq_essSup_positiveAdjointOne, norm_abs_lOneOperator]

def Theorem_4_4_real (T S K : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (k : X × Y → ℝ) : Prop :=
  T = S + K → IsSingularOperator S → IsIntegralKernel k K →
    alphaTheta T univ = sInf (Set.range (fun n : ℕ =>
      essSup (fun x => positiveAdjointOne |S| (abs_nonneg S) x +
        ∫ y, |truncatedKernel (n : ℝ) k (x, y)| ∂ν) μ)) ∧
    alphaTheta S univ = ‖banachAdjoint S‖ ∧ ‖banachAdjoint S‖ = ‖S‖

theorem theorem_4_4_real_proof (T S K : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (k : X × Y → ℝ) :
    Theorem_4_4_real T S K k := by
  intro hT hS hk
  obtain ⟨hΔ, hinf⟩ := real_countablyGenerated_weis_essSup_formula_of_decomposition T S K hT hS hk
  refine ⟨?_, ?_, norm_banachAdjoint S⟩
  · rw [← localizedWeakNoncompactness_eq_alphaTheta_univ, ← hΔ]
    exact hinf
  · rw [norm_banachAdjoint]
    exact singular_countablyGenerated_alpha_eq_norm S hS

theorem real_countablyGenerated_attained_weis_formula
    (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) :
    ∃ W : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν, IsWeaklyCompactOperator W ∧
      weakEssentialNorm T = ‖T - W‖ ∧ ‖T - W‖ = localizedWeakNoncompactness T := by
  obtain ⟨W, hW, heq⟩ := exists_real_countablyGenerated_weaklyCompact_bestApproximation T
  exact ⟨W, hW, heq.symm, heq.trans (weakEssentialNorm_eq_localized_real_countablyGenerated T)⟩

/-- The main target is discharged in this real finite countably generated case.
Its strictly-localizable antecedents need not be used in this stronger case. -/
theorem theorem_1_1_real_finite_countablyGenerated
    (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) : Theorem_1_1 μ ν T := by
  intro _ _
  exact real_countablyGenerated_attained_weis_formula T

end PEMS

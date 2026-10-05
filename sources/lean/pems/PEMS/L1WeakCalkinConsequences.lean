import PEMS.StrictlyLocalizableEllOneFactorization
import PEMS.BonsallFromFactorization
import PEMS.NoncompactnessProofs

/-! Bonsall minimality and uniqueness of normalized weak-noncompactness
measures on actual strictly localizable L1 spaces. The sharp factorization
hypothesis is discharged by the constructed L1 theorem. Abstract AL-space
statements additionally require the representation theorem. -/
noncomputable section
open MeasureTheory ThesisCommon
namespace PEMS
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem bonsallWeakCalkinMinimality_real_strictlyLocalizable
    (hμ : StrictlyLocalizable μ) :
    HasBonsallWeakCalkinMinimality ℝ (LOne ℝ μ) weakEssentialNorm :=
  bonsallWeakCalkinMinimality_of_ellOne_factorization
    (weakEssentialNorm_eq_factorizationSup_real_strictlyLocalizable hμ)

theorem corollary_1_11_real_strictlyLocalizable
    (hμ : StrictlyLocalizable μ) : Corollary_1_11 (𝕜 := ℝ) (LOne ℝ μ) := by
  intro _
  exact bonsallWeakCalkinMinimality_real_strictlyLocalizable hμ

theorem proposition_5_11_real_strictlyLocalizable
    (hμ : StrictlyLocalizable μ) (α : (LOne ℝ μ →L[ℝ] LOne ℝ μ) → ℝ)
    (hα : NormalizedWeakNoncompactnessMeasure α) (T : LOne ℝ μ →L[ℝ] LOne ℝ μ) :
    α T = weakEssentialNorm T :=
  proposition_5_11_of_factorization α hα T
    (weakEssentialNorm_eq_factorizationSup_real_strictlyLocalizable hμ T)

theorem bonsallWeakCalkinMinimality_complex_strictlyLocalizable
    (hμ : StrictlyLocalizable μ) :
    HasBonsallWeakCalkinMinimality ℂ (LOne ℂ μ) weakEssentialNorm :=
  bonsallWeakCalkinMinimality_of_ellOne_factorization
    (weakEssentialNorm_eq_factorizationSup_complex_strictlyLocalizable hμ)

theorem corollary_1_11_complex_strictlyLocalizable
    (hμ : StrictlyLocalizable μ) : Corollary_1_11 (𝕜 := ℂ) (LOne ℂ μ) := by
  intro _
  exact bonsallWeakCalkinMinimality_complex_strictlyLocalizable hμ

theorem proposition_5_11_complex_strictlyLocalizable
    (hμ : StrictlyLocalizable μ) (α : (LOne ℂ μ →L[ℂ] LOne ℂ μ) → ℝ)
    (hα : NormalizedWeakNoncompactnessMeasure α) (T : LOne ℂ μ →L[ℂ] LOne ℂ μ) :
    α T = weakEssentialNorm T :=
  proposition_5_11_of_factorization α hα T
    (weakEssentialNorm_eq_factorizationSup_complex_strictlyLocalizable hμ T)

end PEMS

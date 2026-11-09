import PEMS.ExactSection5Bidual
import PEMS.ExactSection5Truncation
import PEMS.StrictlyLocalizableEllOneFactorization

/-! Corollary 5.14 of the PEMS paper, including the two weak-star quantities
and the finite-measure simplification. The display's output space is the
same X with measure μ; A denotes the finite-measure localization to avoid
reusing the name E of the Banach space. -/

noncomputable section
open Set MeasureTheory ThesisCommon

namespace PEMS

variable {𝕜 X : Type*} [RCLike 𝕜] [MeasurableSpace X] {μ : Measure X}

/-- All equalities in Corollary 5.14. The finite case uses Δ(T) = α_univ(T)
and the excess integral with the constant c on the entire measure space. -/
def Corollary_5_14 (T : LOne 𝕜 μ →L[𝕜] LOne 𝕜 μ) : Prop :=
  StrictlyLocalizable μ →
    weakEssentialNorm T = localizedWeakNoncompactness T ∧
    weakEssentialNorm T = deBlasiOperator T ∧
    weakEssentialNorm T = section5Wk (𝕜 := 𝕜) (T '' Metric.closedBall 0 1) ∧
    weakEssentialNorm T = section5Wck (𝕜 := 𝕜) (T '' Metric.closedBall 0 1) ∧
    weakEssentialNorm T = section5LocalizedTruncationInf T ∧
    (IsFiniteMeasure μ → weakEssentialNorm T = alphaTheta T univ ∧
      weakEssentialNorm T = section5UnivTruncationInf T)

private theorem corollary_5_14_assemble (T : LOne 𝕜 μ →L[𝕜] LOne 𝕜 μ)
    (hα : weakEssentialNorm T = localizedWeakNoncompactness T)
    (hfac : weakEssentialNorm T = factorizationSup (EllOne 𝕜) T) :
    Corollary_5_14 T := by
  intro _
  have h₁ : weakEssentialNorm T ≤ section5Wck (𝕜 := 𝕜) (T '' Metric.closedBall 0 1) :=
    hfac.le.trans (section5_factorizationSup_le_wckOperator T)
  have h₂ := section5Wck_le_wkOperator T
  have h₃ := section5Wk_le_deBlasiOperator T
  have h₄ := deBlasiOperator_le_weakEssentialNorm T
  refine ⟨hα, le_antisymm (h₁.trans (h₂.trans h₃)) h₄,
    le_antisymm (h₁.trans h₂) (h₃.trans h₄),
    le_antisymm h₁ (h₂.trans (h₃.trans h₄)),
    hα.trans (section5LocalizedTruncationInf_eq_localized T).symm, ?_⟩
  intro hfin
  letI := hfin
  have heq := hα.trans (localizedWeakNoncompactness_eq_alphaTheta_univ T)
  exact ⟨heq, heq.trans (section5UnivTruncationInf_eq_alphaTheta T).symm⟩

theorem corollary_5_14_real (T : LOne ℝ μ →L[ℝ] LOne ℝ μ) : Corollary_5_14 T := by
  intro hμ
  exact corollary_5_14_assemble T (weakEssentialNorm_eq_localized_real_strictlyLocalizable hμ T)
    (weakEssentialNorm_eq_factorizationSup_real_strictlyLocalizable hμ T) hμ

theorem corollary_5_14_complex (T : LOne ℂ μ →L[ℂ] LOne ℂ μ) : Corollary_5_14 T := by
  intro hμ
  exact corollary_5_14_assemble T (weakEssentialNorm_eq_localized_complex_strictlyLocalizable hμ T)
    (weakEssentialNorm_eq_factorizationSup_complex_strictlyLocalizable hμ T) hμ

end PEMS

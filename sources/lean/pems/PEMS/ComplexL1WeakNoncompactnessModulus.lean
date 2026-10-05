import PEMS.MeasureChecks
import ThesisCommon.Analysis.ComplexL1CutModulus

/-! The actual complex cutoff and localized small-set functionals equal
their real operator-modulus counterparts, for arbitrary measures. -/
noncomputable section
open MeasureTheory Set ThesisCommon
namespace PEMS
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}

theorem cutOperatorNorm_complex_modulus (T : LOne ℂ μ →L[ℂ] LOne ℂ ν)
    (B : Set Y) (hB : MeasurableSet B) :
    cutOperatorNorm (complexL1OperatorModulus T) B = cutOperatorNorm T B := by
  rw [cutOperatorNorm_eq _ B hB, cutOperatorNorm_eq _ B hB,
    norm_outputCut_complexL1OperatorModulus]

theorem smallSetSup_complex_modulus (T : LOne ℂ μ →L[ℂ] LOne ℂ ν)
    (Θ : Set Y) (hΘ : MeasurableSet Θ) (δ : ℝ) :
    smallSetSup (complexL1OperatorModulus T) Θ δ = smallSetSup T Θ δ := by
  unfold smallSetSup
  congr 1
  ext q
  constructor <;> rintro ⟨B, hB, hsub, hsmall, heq⟩
  · exact ⟨B, hB, hsub, hsmall,
      heq.trans (cutOperatorNorm_complex_modulus T _ (hΘ.compl.union hB))⟩
  · exact ⟨B, hB, hsub, hsmall,
      heq.trans (cutOperatorNorm_complex_modulus T _ (hΘ.compl.union hB)).symm⟩

theorem alphaTheta_complex_modulus (T : LOne ℂ μ →L[ℂ] LOne ℂ ν)
    (Θ : Set Y) (hΘ : MeasurableSet Θ) :
    alphaTheta (complexL1OperatorModulus T) Θ = alphaTheta T Θ := by
  simp only [alphaTheta, smallSetSup_complex_modulus T Θ hΘ]

theorem localizedWeakNoncompactness_complex_modulus (T : LOne ℂ μ →L[ℂ] LOne ℂ ν) :
    localizedWeakNoncompactness (complexL1OperatorModulus T) = localizedWeakNoncompactness T := by
  unfold localizedWeakNoncompactness
  congr 1
  ext r
  constructor <;> rintro ⟨Θ, hΘ, hfin, heq⟩
  · exact ⟨Θ, hΘ, hfin, heq.trans (alphaTheta_complex_modulus T Θ hΘ)⟩
  · exact ⟨Θ, hΘ, hfin, heq.trans (alphaTheta_complex_modulus T Θ hΘ).symm⟩

end PEMS

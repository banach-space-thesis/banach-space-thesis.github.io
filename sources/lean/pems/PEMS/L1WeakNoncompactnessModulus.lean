import PEMS.MeasureChecks
import ThesisCommon.Analysis.L1CutModulus

/-! The paper's actual cutoff and localized noncompactness functionals are
unchanged by real operator modulus. No measure-finiteness hypothesis is used. -/
noncomputable section
open MeasureTheory Set
open scoped ThesisCommon.PositiveOperatorOrder
namespace PEMS
open ThesisCommon
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}

theorem cutOperatorNorm_abs (T : LOne ℝ μ →L[ℝ] LOne ℝ ν)
    (B : Set Y) (hB : MeasurableSet B) : cutOperatorNorm |T| B = cutOperatorNorm T B := by
  rw [cutOperatorNorm_eq _ B hB, cutOperatorNorm_eq _ B hB,
    norm_outputCut_abs_lOneOperator]

theorem smallSetSup_abs (T : LOne ℝ μ →L[ℝ] LOne ℝ ν)
    (Θ : Set Y) (hΘ : MeasurableSet Θ) (δ : ℝ) :
    smallSetSup |T| Θ δ = smallSetSup T Θ δ := by
  unfold smallSetSup
  congr 1
  ext q
  constructor <;> rintro ⟨B, hB, hsub, hsmall, heq⟩
  · exact ⟨B, hB, hsub, hsmall, heq.trans (cutOperatorNorm_abs T _ (hΘ.compl.union hB))⟩
  · exact ⟨B, hB, hsub, hsmall, heq.trans (cutOperatorNorm_abs T _ (hΘ.compl.union hB)).symm⟩

theorem alphaTheta_abs (T : LOne ℝ μ →L[ℝ] LOne ℝ ν)
    (Θ : Set Y) (hΘ : MeasurableSet Θ) : alphaTheta |T| Θ = alphaTheta T Θ := by
  simp only [alphaTheta, smallSetSup_abs T Θ hΘ]

theorem localizedWeakNoncompactness_abs (T : LOne ℝ μ →L[ℝ] LOne ℝ ν) :
    localizedWeakNoncompactness |T| = localizedWeakNoncompactness T := by
  unfold localizedWeakNoncompactness
  congr 1
  ext r
  constructor <;> rintro ⟨Θ, hΘ, hfin, heq⟩
  · exact ⟨Θ, hΘ, hfin, heq.trans (alphaTheta_abs T Θ hΘ)⟩
  · exact ⟨Θ, hΘ, hfin, heq.trans (alphaTheta_abs T Θ hΘ).symm⟩

end PEMS

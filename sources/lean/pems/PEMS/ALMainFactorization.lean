import PEMS.KakutaniRepresentation
import PEMS.StrictlyLocalizableEllOneFactorization
import PEMS.FactorizationSupTransport

/-! Theorem 1.4 in its full intrinsic real and complex AL-space scope.
The representing L1 spaces are constructed, and exact isometries transport
both the weak essential norm and all factorization witnesses. -/
noncomputable section
open MeasureTheory ThesisCommon
namespace PEMS
variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

section Real
variable [NormedSpace ℝ E] [NormedSpace ℝ F] [CompleteSpace E] [CompleteSpace F]

theorem weakEssentialNorm_eq_factorizationSup_real_AL (T : E →L[ℝ] F)
    (hE : IsALSpace ℝ E) (hF : IsALSpace ℝ F) :
    weakEssentialNorm T = factorizationSup (EllOne ℝ) T := by
  obtain ⟨X, mX, μ, hμ, ⟨a⟩⟩ := exists_lOne_representation_of_real_isAL hE
  letI := mX
  obtain ⟨Y, mY, ν, _, ⟨b⟩⟩ := exists_lOne_representation_of_real_isAL hF
  letI := mY
  have h := weakEssentialNorm_eq_factorizationSup_real_strictlyLocalizable hμ
    (operatorTransport a b T)
  simpa only [weakEssentialNorm_operatorTransport, factorizationSup_operatorTransport] using h

theorem theorem_1_4_real (T : E →L[ℝ] F) : Theorem_1_4 E F T := by
  intro hE hF
  exact weakEssentialNorm_eq_factorizationSup_real_AL T hE hF

end Real

section Complex
variable [NormedSpace ℂ E] [NormedSpace ℂ F] [CompleteSpace E] [CompleteSpace F]
variable [NormedSpace ℝ E] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ E] [IsScalarTower ℝ ℂ F]

theorem weakEssentialNorm_eq_factorizationSup_complex_AL (T : E →L[ℂ] F)
    (hE : IsALSpace ℂ E) (hF : IsALSpace ℂ F) :
    weakEssentialNorm T = factorizationSup (EllOne ℂ) T := by
  obtain ⟨X, mX, μ, hμ, ⟨a⟩⟩ := exists_lOne_representation_of_complex_isAL hE
  letI := mX
  obtain ⟨Y, mY, ν, _, ⟨b⟩⟩ := exists_lOne_representation_of_complex_isAL hF
  letI := mY
  have h := weakEssentialNorm_eq_factorizationSup_complex_strictlyLocalizable hμ
    (operatorTransport a b T)
  simpa only [weakEssentialNorm_operatorTransport, factorizationSup_operatorTransport] using h

theorem theorem_1_4_complex (T : E →L[ℂ] F) : Theorem_1_4 E F T := by
  intro hE hF
  exact weakEssentialNorm_eq_factorizationSup_complex_AL T hE hF

end Complex

end PEMS

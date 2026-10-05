import PEMS.KakutaniRepresentation
import PEMS.RealStrictlyLocalizableWeis
import PEMS.ComplexStrictlyLocalizableWeis
import ThesisCommon.Analysis.OperatorIsometryTransport

/-! Best weakly compact approximants on intrinsic real and complex AL spaces,
transported from the proved L1 theorem through constructed Kakutani models. -/
noncomputable section
open MeasureTheory ThesisCommon
namespace PEMS
variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

section Real
variable [NormedSpace ℝ E] [NormedSpace ℝ F] [CompleteSpace E] [CompleteSpace F]

theorem exists_real_AL_weaklyCompact_bestApproximation (T : E →L[ℝ] F)
    (hE : IsALSpace ℝ E) (hF : IsALSpace ℝ F) :
    ∃ W : E →L[ℝ] F, IsWeaklyCompactOperator W ∧ ‖T - W‖ = weakEssentialNorm T := by
  obtain ⟨X, mX, μ, hμ, ⟨a⟩⟩ := exists_lOne_representation_of_real_isAL hE
  letI := mX
  obtain ⟨Y, mY, ν, _, ⟨b⟩⟩ := exists_lOne_representation_of_real_isAL hF
  letI := mY
  obtain ⟨W, hW, he⟩ := exists_real_strictlyLocalizable_weaklyCompact_bestApproximation hμ
    (operatorTransport a b T)
  refine ⟨operatorTransport a.symm b.symm W,
    (weaklyCompact_operatorTransport_iff a.symm b.symm W).mpr hW, ?_⟩
  have h := norm_operatorTransport a.symm b.symm (operatorTransport a b T - W)
  rw [operatorTransport_sub, operatorTransport_symm] at h
  rw [h, he, weakEssentialNorm_operatorTransport]

end Real

section Complex
variable [NormedSpace ℂ E] [NormedSpace ℂ F] [CompleteSpace E] [CompleteSpace F]
variable [NormedSpace ℝ E] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ E] [IsScalarTower ℝ ℂ F]

theorem exists_complex_AL_weaklyCompact_bestApproximation (T : E →L[ℂ] F)
    (hE : IsALSpace ℂ E) (hF : IsALSpace ℂ F) :
    ∃ W : E →L[ℂ] F, IsWeaklyCompactOperator W ∧ ‖T - W‖ = weakEssentialNorm T := by
  obtain ⟨X, mX, μ, hμ, ⟨a⟩⟩ := exists_lOne_representation_of_complex_isAL hE
  letI := mX
  obtain ⟨Y, mY, ν, _, ⟨b⟩⟩ := exists_lOne_representation_of_complex_isAL hF
  letI := mY
  obtain ⟨W, hW, he⟩ := exists_complex_strictlyLocalizable_weaklyCompact_bestApproximation hμ
    (operatorTransport a b T)
  refine ⟨operatorTransport a.symm b.symm W,
    (weaklyCompact_operatorTransport_iff a.symm b.symm W).mpr hW, ?_⟩
  have h := norm_operatorTransport a.symm b.symm (operatorTransport a b T - W)
  rw [operatorTransport_sub, operatorTransport_symm] at h
  rw [h, he, weakEssentialNorm_operatorTransport]

end Complex

end PEMS

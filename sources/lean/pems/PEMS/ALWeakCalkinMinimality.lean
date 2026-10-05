import PEMS.ALMainFactorization
import PEMS.GenericFactorizationNormConsequences
import ThesisCommon.Analysis.EllOneAlgebraGeometry

/-! Unrestricted minimality for intrinsic real and complex AL-spaces.
This proves the minimality part of Corollary 1.7 without a measure-space
classification, a self-similarity premise on E, or completeness of competing norms. -/
noncomputable section
open ThesisCommon
namespace PEMS
variable {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]

theorem minimal_weakCalkinNorm_real_AL [NormedSpace ℝ E] (hE : IsALSpace ℝ E) :
    IsMinimalWeakCalkinNorm ℝ E weakEssentialNorm := by
  obtain ⟨I, Q, hd, ho⟩ := exists_orthogonal_selfCopies_scalarEllOne (𝕜 := ℝ)
  exact minimal_weakEssentialNorm_of_generic_factorization not_weaklyCompact_id_scalarEllOne
    I Q hd ho (fun T => weakEssentialNorm_eq_factorizationSup_real_AL T hE hE)

theorem minimal_weakCalkinNorm_complex_AL [NormedSpace ℂ E]
    [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] (hE : IsALSpace ℂ E) :
    IsMinimalWeakCalkinNorm ℂ E weakEssentialNorm := by
  obtain ⟨I, Q, hd, ho⟩ := exists_orthogonal_selfCopies_scalarEllOne (𝕜 := ℂ)
  exact minimal_weakEssentialNorm_of_generic_factorization not_weaklyCompact_id_scalarEllOne
    I Q hd ho (fun T => weakEssentialNorm_eq_factorizationSup_complex_AL T hE hE)

end PEMS

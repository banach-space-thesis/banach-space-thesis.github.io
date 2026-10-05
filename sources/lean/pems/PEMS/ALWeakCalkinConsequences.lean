import PEMS.ALMainFactorization
import PEMS.BonsallFromFactorization
import PEMS.NoncompactnessProofs

/-! Full intrinsic AL-space Corollary1.11 and Proposition5.11. The sharp
factorization formula is discharged by the actual representation proof. -/
noncomputable section
open MeasureTheory ThesisCommon
namespace PEMS
variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

section Real
variable [NormedSpace ℝ E] [NormedSpace ℝ F] [CompleteSpace E] [CompleteSpace F]

theorem corollary_1_11_real : Corollary_1_11 (𝕜 := ℝ) E := by
  intro hE
  exact bonsallWeakCalkinMinimality_of_ellOne_factorization
    (fun T => weakEssentialNorm_eq_factorizationSup_real_AL T hE hE)

theorem proposition_5_11_real (α : (E →L[ℝ] E) → ℝ) (T : E →L[ℝ] E) :
    Proposition_5_11 α T := by
  intro hE hα
  exact proposition_5_11_of_factorization α hα T
    (weakEssentialNorm_eq_factorizationSup_real_AL T hE hE)

end Real

section Complex
variable [NormedSpace ℂ E] [NormedSpace ℂ F] [CompleteSpace E] [CompleteSpace F]
variable [NormedSpace ℝ E] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ E] [IsScalarTower ℝ ℂ F]

theorem corollary_1_11_complex : Corollary_1_11 (𝕜 := ℂ) E := by
  intro hE
  exact bonsallWeakCalkinMinimality_of_ellOne_factorization
    (fun T => weakEssentialNorm_eq_factorizationSup_complex_AL T hE hE)

theorem proposition_5_11_complex (α : (E →L[ℂ] E) → ℝ) (T : E →L[ℂ] E) :
    Proposition_5_11 α T := by
  intro hE hα
  exact proposition_5_11_of_factorization α hα T
    (weakEssentialNorm_eq_factorizationSup_complex_AL T hE hE)

end Complex

end PEMS

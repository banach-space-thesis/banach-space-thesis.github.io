import PEMS.ALMainFactorization
import PEMS.WeakCalkinCornerAutomaticBound
import ThesisCommon.Analysis.RealALCornerCopies
import ThesisCommon.Analysis.OperatorCornerTransport
import ThesisCommon.Analysis.ComplexLatticeOperatorExtension

/-! Full Corollary 1.7 for intrinsic real and complex AL-spaces.
Actual homogeneous principal-band geometry constructs the orthogonal
corners and their weakly compact remainder. Sharp factorization supplies
the lower bound; the corner series supplies the upper bound for every
competing algebra norm, with no continuity or completeness assumption. -/
noncomputable section
open ThesisCommon
namespace PEMS
variable {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]

theorem corollary_1_7_real [NormedSpace ℝ E] : Corollary_1_7 (𝕜 := ℝ) E := by
  intro hE
  have hfactor := fun T : E →L[ℝ] E => weakEssentialNorm_eq_factorizationSup_real_AL T hE hE
  obtain ⟨B, hB⟩ := hE
  letI : CompleteSpace B.realForm := B.closed_realForm.isComplete.completeSpace_coe
  obtain ⟨Q, J, P, hd, ho, hr⟩ := exists_real_AL_orthogonal_cornerCopies hB
  obtain ⟨R, U, V, hd', ho', hr'⟩ := B.exists_real_cornerCopies_of_realForm Q J P hd ho hr
  exact uniqueWeakCalkinAlgebraNorm_of_factorization_and_upperBounds hfactor
    (fun m hm => exists_weakCalkinAlgebraNorm_upperBound_of_corner_selfCopies U V R hd' ho' hr' m hm)

theorem corollary_1_7_complex [NormedSpace ℂ E] [NormedSpace ℝ E]
    [IsScalarTower ℝ ℂ E] : Corollary_1_7 (𝕜 := ℂ) E := by
  intro hE
  have hfactor := fun T : E →L[ℂ] E => weakEssentialNorm_eq_factorizationSup_complex_AL T hE hE
  obtain ⟨B, hB⟩ := hE
  letI : CompleteSpace B.realForm := B.closed_realForm.isComplete.completeSpace_coe
  obtain ⟨Q, J, P, hd, ho, hr⟩ := exists_real_AL_orthogonal_cornerCopies hB
  obtain ⟨R, U, V, hd', ho', hr'⟩ := B.exists_cornerCopies_of_realForm Q J P hd ho hr
  exact uniqueWeakCalkinAlgebraNorm_of_factorization_and_upperBounds hfactor
    (fun m hm => exists_weakCalkinAlgebraNorm_upperBound_of_corner_selfCopies U V R hd' ho' hr' m hm)

end PEMS

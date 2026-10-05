import PEMS.ALMainFactorization
import PEMS.WeakCalkinComplementedReduction
import ThesisCommon.Analysis.OperatorAlgebraLpSelfCopies
import ThesisCommon.Analysis.RealALModel

/-! Genuine uniqueness consequences where the required geometry is already
constructed: complete atomic real AL-spaces and real/complex Lebesgue L1[0,1].
These are explicit subcases of Corollary 1.7, not the general atomless theorem. -/
noncomputable section
open ThesisCommon MeasureTheory Set
namespace PEMS

theorem uniqueWeakCalkinAlgebraNorm_atomic_real_AL
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Lattice E]
    [IsOrderedAddMonoid E] [IsOrderedModule ℝ E] [HasSolidNorm E] [CompleteSpace E]
    (hAL : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x+y‖ = ‖x‖+‖y‖)
    (hAtom : ∀ x : E, 0 ≤ x → x ≠ 0 → ∃ a : E, IsPositiveLatticeAtom a ∧ a ≤ x) :
    HasUniqueWeakCalkinAlgebraNorm ℝ E := by
  rcases atomic_AL_weaklyCompact_id_or_selfCopies hAL hAtom with hId | ⟨J, P, hd, ho⟩
  · exact uniqueWeakCalkinAlgebraNorm_of_weaklyCompact_id hId
  · have hE : IsALSpace ℝ E := isALSpace_of_real_lattice E hAL
    exact uniqueWeakCalkinAlgebraNorm_of_factorization_and_upperBounds
      (fun T => weakEssentialNorm_eq_factorizationSup_real_AL T hE hE)
      (fun m hm => exists_weakCalkinAlgebraNorm_upperBound_of_selfCopies J P hd ho m hm)

theorem uniqueWeakCalkinAlgebraNorm_intervalL1_real :
    HasUniqueWeakCalkinAlgebraNorm ℝ (Lp ℝ 1 (volume.restrict (Icc (0 : ℝ) 1))) := by
  obtain ⟨J, P, hd, ho⟩ := exists_orthogonal_selfCopies_intervalLp
    (𝕜 := ℝ) ⟨1, le_refl _⟩ (by simp)
  exact uniqueWeakCalkinAlgebraNorm_of_factorization_and_upperBounds
    weakEssentialNorm_eq_factorizationSup_real_finite
    (fun m hm => exists_weakCalkinAlgebraNorm_upperBound_of_selfCopies J P hd ho m hm)

theorem uniqueWeakCalkinAlgebraNorm_intervalL1_complex :
    HasUniqueWeakCalkinAlgebraNorm ℂ (Lp ℂ 1 (volume.restrict (Icc (0 : ℝ) 1))) := by
  obtain ⟨J, P, hd, ho⟩ := exists_orthogonal_selfCopies_intervalLp
    (𝕜 := ℂ) ⟨1, le_refl _⟩ (by simp)
  exact uniqueWeakCalkinAlgebraNorm_of_factorization_and_upperBounds
    weakEssentialNorm_eq_factorizationSup_complex_finite
    (fun m hm => exists_weakCalkinAlgebraNorm_upperBound_of_selfCopies J P hd ho m hm)

end PEMS

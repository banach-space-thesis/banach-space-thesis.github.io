import PEMS.WeakCalkinNormComparison
import ThesisCommon.Analysis.OperatorAlgebraSelfCopies

/-! Genuine upper bounds for arbitrary, possibly incomplete algebra norms
on the weak Calkin quotient. Automatic boundedness is proved using exact
orthogonal self-copies; weakly compact perturbations then replace the
operator norm bound by the canonical quotient norm bound. -/
noncomputable section
open ThesisCommon Set
namespace PEMS
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [CompleteSpace E]

theorem exists_weakCalkinAlgebraNorm_upperBound_of_selfCopies
    (J P : ℕ → E →L[𝕜] E)
    (hdiag : ∀ n, (P n).comp (J n) = ContinuousLinearMap.id 𝕜 E)
    (hoff : ∀ n m, n ≠ m → (P n).comp (J m) = 0)
    (m : WeakCalkin 𝕜 E → ℝ) (hm : IsWeakCalkinAlgebraNorm 𝕜 E m) :
    ∃ C : ℝ, 0 < C ∧ ∀ x, m x ≤ C * weakCalkinNorm 𝕜 E x := by
  let α : (E →L[𝕜] E) → ℝ := fun T => m (weakCalkinMk 𝕜 E T)
  have hzero : α 0 = 0 := by
    change m ((weakCalkinMkCLM 𝕜 E) 0) = 0
    rw [map_zero]
    exact (hm.2.1 0).mpr rfl
  have hsmul (a : 𝕜) (T : E →L[𝕜] E) : α (a • T) = ‖a‖ * α T := by
    change m ((weakCalkinMkCLM 𝕜 E) (a • T)) = ‖a‖ * m ((weakCalkinMkCLM 𝕜 E) T)
    rw [map_smul]
    exact hm.2.2.2.1 a _
  obtain ⟨C, hC, hbound⟩ := exists_algebra_seminorm_bound_of_orthogonal_selfCopies
    J P hdiag hoff α (fun T => hm.1 _) hzero hsmul (fun S T => hm.2.2.2.2 S T)
  refine ⟨C, hC, fun x => ?_⟩
  refine Submodule.Quotient.induction_on _ x fun T => ?_
  change α T ≤ C * weakCalkinNorm 𝕜 E (weakCalkinMk 𝕜 E T)
  rw [weakCalkinNorm_mk]
  have hdiv : α T / C ≤ weakEssentialNorm T := by
    apply le_csInf
    · exact ⟨‖T - 0‖, 0, weaklyCompact_zero, rfl⟩
    · rintro r ⟨W, hW, rfl⟩
      have hWzero : (weakCalkinMkCLM 𝕜 E) W = 0 :=
        (Submodule.Quotient.mk_eq_zero (p := weaklyCompactSubmodule 𝕜 E E)).mpr hW
      have heq : α (T - W) = α T := by
        change m ((weakCalkinMkCLM 𝕜 E) (T - W)) = m ((weakCalkinMkCLM 𝕜 E) T)
        rw [map_sub, hWzero, sub_zero]
      apply (div_le_iff₀ hC).mpr
      simpa only [heq, mul_comm] using hbound (T - W)
  simpa only [mul_comm] using (div_le_iff₀ hC).mp hdiv

theorem exists_weakCalkinAlgebraNorm_upperBound_of_square_equiv
    (e : E ≃L[𝕜] E × E) (m : WeakCalkin 𝕜 E → ℝ)
    (hm : IsWeakCalkinAlgebraNorm 𝕜 E m) :
    ∃ C : ℝ, 0 < C ∧ ∀ x, m x ≤ C * weakCalkinNorm 𝕜 E x := by
  obtain ⟨J, P, hdiag, hoff⟩ := exists_orthogonal_selfCopies_of_square_equiv e
  exact exists_weakCalkinAlgebraNorm_upperBound_of_selfCopies J P hdiag hoff m hm

/-- Generic uniqueness with every analytic input constructed except for the
explicit geometric square equivalence and sharp factorization formula. -/
theorem uniqueWeakCalkinAlgebraNorm_of_square_and_factorization
    (e : E ≃L[𝕜] E × E)
    (hfactor : ∀ T : E →L[𝕜] E, weakEssentialNorm T = factorizationSup (EllOne 𝕜) T) :
    HasUniqueWeakCalkinAlgebraNorm 𝕜 E :=
  uniqueWeakCalkinAlgebraNorm_of_factorization_and_upperBounds hfactor
    (fun m hm => exists_weakCalkinAlgebraNorm_upperBound_of_square_equiv e m hm)

theorem minimalWeakCalkinNorm_of_square_and_factorization
    (e : E ≃L[𝕜] E × E)
    (hfactor : ∀ T : E →L[𝕜] E, weakEssentialNorm T = factorizationSup (EllOne 𝕜) T) :
    IsMinimalWeakCalkinNorm 𝕜 E weakEssentialNorm :=
  minimalWeakCalkinNorm_of_factorization_and_upperBounds hfactor
    (fun m hm => exists_weakCalkinAlgebraNorm_upperBound_of_square_equiv e m hm)

theorem uniqueWeakCalkinAlgebraNorm_of_weaklyCompact_id
    (hId : IsWeaklyCompactOperator (ContinuousLinearMap.id 𝕜 E)) :
    HasUniqueWeakCalkinAlgebraNorm 𝕜 E := by
  refine ⟨weakCalkinNorm 𝕜 E, weakCalkinNorm_isAlgebraNorm, ?_⟩
  intro m hm
  refine ⟨1, 1, zero_lt_one, zero_lt_one, fun x => ?_⟩
  have hx : x = 0 := by
    refine Submodule.Quotient.induction_on _ x fun T => ?_
    apply (Submodule.Quotient.mk_eq_zero (p := weaklyCompactSubmodule 𝕜 E E)).mpr
    have hT := hId.comp_left T
    simpa only [ContinuousLinearMap.comp_id] using hT
  have hnzero : weakCalkinNorm 𝕜 E 0 = 0 :=
    (weakCalkinNorm_isAlgebraNorm (𝕜 := 𝕜) (E := E)).2.1 0 |>.mpr rfl
  rw [hx, (hm.2.1 0).mpr rfl, hnzero]
  simp

/-- The zero-quotient case needs no self-similarity. In the remaining case,
the required geometric input is an actual bounded square isomorphism. -/
theorem uniqueWeakCalkinAlgebraNorm_of_factorization_and_nonreflexive_square
    (hfactor : ∀ T : E →L[𝕜] E, weakEssentialNorm T = factorizationSup (EllOne 𝕜) T)
    (hsquare : ¬ IsWeaklyCompactOperator (ContinuousLinearMap.id 𝕜 E) →
      Nonempty (E ≃L[𝕜] E × E)) :
    HasUniqueWeakCalkinAlgebraNorm 𝕜 E := by
  by_cases hId : IsWeaklyCompactOperator (ContinuousLinearMap.id 𝕜 E)
  · exact uniqueWeakCalkinAlgebraNorm_of_weaklyCompact_id hId
  · obtain ⟨e⟩ := hsquare hId
    exact uniqueWeakCalkinAlgebraNorm_of_square_and_factorization e hfactor

end PEMS

import JLMS.CalkinConjugation
import JLMS.OperatorNormUniqueness
import JLMS.CompactCZeroEquiv
import JLMS.ScatteredCZeroFactorization

/-!
# Section 9: uniqueness of every Calkin algebra norm

Automatic continuity bounds a competing norm by the operator norm on quotient
representatives. Taking compact perturbations gives an essential-norm upper
bound. Theorem 1.1 supplies the lower bound. Completeness of the competing
norm is never assumed.
-/

noncomputable section
namespace JLMS
universe u w
variable {𝕜 : Type w} [RCLike 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

theorem calkinNorm_upper_bound_of_automaticContinuity
    (hE : ∀ (A : Type u) [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
      [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] [CompleteSpace A],
      ∀ φ : (E →L[𝕜] E) →ₙₐ[𝕜] A, Continuous φ)
    (n : Calkin 𝕜 E → ℝ) (hn : IsCalkinAlgebraNorm 𝕜 E n) :
    ∃ C : ℝ, 0 < C ∧ ∀ T, n (calkinMk 𝕜 E T) ≤ C * essentialNorm T := by
  obtain ⟨C, hC, hupper⟩ := algebraNorm_bound_of_hom_automaticContinuity hE
    calkinQuotientHom n ((isCalkinAlgebraNorm_iff n).mp hn)
  refine ⟨C, hC, fun T => ?_⟩
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨S, hS, happrox⟩ := exists_compact_norm_sub_lt T (div_pos hε hC)
  have heq : calkinMk 𝕜 E (T - S) = calkinMk 𝕜 E T := by
    apply (Submodule.Quotient.eq (compactOperator (RingHom.id 𝕜) E E)).mpr
    simpa using hS
  have h := hupper (T - S)
  change n (calkinMk 𝕜 E (T - S)) ≤ _ at h
  rw [heq] at h
  have hh := mul_le_mul_of_nonneg_left happrox.le hC.le
  have hcancel : C * (ε / C) = ε := mul_div_cancel₀ ε hC.ne'
  nlinarith

theorem hasUniqueCalkinNorm_of_minimal_automaticContinuity
    (hminimal : EssentialNormIsMinimal 𝕜 E)
    (hE : ∀ (A : Type u) [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
      [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] [CompleteSpace A],
      ∀ φ : (E →L[𝕜] E) →ₙₐ[𝕜] A, Continuous φ) :
    HasUniqueCalkinNorm 𝕜 E := by
  intro n m hn hm
  obtain ⟨cn, hcn, hnl⟩ := hminimal n hn
  obtain ⟨cm, hcm, hml⟩ := hminimal m hm
  obtain ⟨Cn, hCn, hnu⟩ := calkinNorm_upper_bound_of_automaticContinuity hE n hn
  obtain ⟨Cm, hCm, hmu⟩ := calkinNorm_upper_bound_of_automaticContinuity hE m hm
  apply equivalentNorms_of_reference_bounds (fun q => ‖q‖) n m hcn hCn hcm hCm
  · intro q
    induction q using Submodule.Quotient.induction_on with
    | H T => simpa only [essentialNorm_eq_quotient_norm] using And.intro (hnl T) (hnu T)
  · intro q
    induction q using Submodule.Quotient.induction_on with
    | H T => simpa only [essentialNorm_eq_quotient_norm] using And.intro (hml T) (hmu T)

theorem corollary_1_4_of_theorem_1_3 (α : Ordinal.{u})
    (hα : Theorem_1_3.{u, max (u + 1) w, w} (𝕜 := 𝕜) α) :
    Corollary_1_4 (𝕜 := 𝕜) α := by
  refine ⟨ordinal_operatorNorm_unique_of_theorem_1_3 α hα, ?_⟩
  apply hasUniqueCalkinNorm_of_minimal_automaticContinuity ?_ hα
  exact essentialNormIsMinimal_of_isometryEquiv (ordinalContinuousCZeroEquiv α)
    ((theorem_1_1 (𝕜 := 𝕜) (K := OrdinalInterval α) (scattered_ordinalInterval α)).1)

end JLMS

import JLMS.CompetingNorms
import JLMS.EssentialNorm

/-!
# Complete uniqueness as a consequence of minimality

A complete competing Calkin norm has a lower comparison with the quotient
Banach norm by minimality. Open mapping gives the upper comparison. Applying
this to each of two complete norms proves their equivalence. This is the
complete-uniqueness clause of Theorem 1.1, isolated from its factorization proof.
-/

noncomputable section

namespace JLMS

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]

/-- Minimality and completeness imply the uniqueness of complete Calkin norms. -/
theorem hasUniqueCompleteCalkinNorm_of_minimal (hminimal : EssentialNormIsMinimal 𝕜 E) :
    HasUniqueCompleteCalkinNorm 𝕜 E := by
  letI : IsClosed (compactOperator (RingHom.id 𝕜) E E : Set (E →L[𝕜] E)) :=
    isClosed_setOf_isCompactOperator
  intro n m hn hm hcn hcm
  obtain ⟨cn, hcnpos, hnlower⟩ := hminimal n hn
  obtain ⟨cm, hcmpos, hmlower⟩ := hminimal m hm
  have hnq (q : Calkin 𝕜 E) : cn * ‖q‖ ≤ n q := by
    induction q using Submodule.Quotient.induction_on with
    | H T => simpa only [essentialNorm_eq_quotient_norm] using hnlower T
  have hmq (q : Calkin 𝕜 E) : cm * ‖q‖ ≤ m q := by
    induction q using Submodule.Quotient.induction_on with
    | H T => simpa only [essentialNorm_eq_quotient_norm] using hmlower T
  obtain ⟨Cn, hCn, hnupper⟩ := completeNorm_upper_bound_of_lower (𝕜 := 𝕜) n hn.1 hcn hcnpos hnq
  obtain ⟨Cm, hCm, hmupper⟩ := completeNorm_upper_bound_of_lower (𝕜 := 𝕜) m hm.1 hcm hcmpos hmq
  refine ⟨cm / Cn, div_pos hcmpos hCn, Cm / cn, div_pos hCm hcnpos, ?_⟩
  intro q
  constructor
  · have h := mul_le_mul_of_nonneg_left (hnupper q) (div_pos hcmpos hCn).le
    have heq : cm / Cn * (Cn * ‖q‖) = cm * ‖q‖ := by field_simp
    rw [heq] at h
    exact h.trans (hmq q)
  · have h := mul_le_mul_of_nonneg_left (hnq q) (div_pos hCm hcnpos).le
    have heq : Cm / cn * (cn * ‖q‖) = Cm * ‖q‖ := by field_simp
    rw [heq] at h
    exact (hmupper q).trans h

end JLMS

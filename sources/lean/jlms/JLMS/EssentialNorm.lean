import JLMS.Definitions
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Tactic

/-!
# Essential norm: reusable operator calculus

These lemmas use the paper's distance-to-compact-operators definition, and
identify it with mathlib's quotient norm. They apply to general normed spaces;
scatteredness and the special structure of C₀(K) are not needed here.
-/

noncomputable section

namespace JLMS

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The definition in the paper agrees with the norm on the actual quotient. -/
theorem essentialNorm_eq_quotient_norm (T : E →L[𝕜] F) :
    essentialNorm T =
      ‖(Submodule.Quotient.mk T :
        (E →L[𝕜] F) ⧸ compactOperator (RingHom.id 𝕜) E F)‖ := by
  unfold essentialNorm
  change _ = ‖QuotientAddGroup.mk' (compactOperator (RingHom.id 𝕜) E F).toAddSubgroup T‖
  rw [quotient_norm_mk_eq]
  congr 1
  ext r
  constructor
  · rintro ⟨S, hS, rfl⟩
    exact ⟨-S, IsCompactOperator.neg hS, by simp [sub_eq_add_neg]⟩
  · rintro ⟨S, hS, rfl⟩
    exact ⟨-S, IsCompactOperator.neg hS, by simp [sub_eq_add_neg]⟩

theorem essentialNorm_nonneg (T : E →L[𝕜] F) : 0 ≤ essentialNorm T := by
  rw [essentialNorm_eq_quotient_norm]
  exact norm_nonneg (Submodule.Quotient.mk T :
    (E →L[𝕜] F) ⧸ compactOperator (RingHom.id 𝕜) E F)

theorem essentialNorm_le_norm (T : E →L[𝕜] F) : essentialNorm T ≤ ‖T‖ := by
  rw [essentialNorm_eq_quotient_norm]
  exact Submodule.Quotient.norm_mk_le _ _

@[simp] theorem essentialNorm_zero : essentialNorm (0 : E →L[𝕜] F) = 0 := by
  rw [essentialNorm_eq_quotient_norm]
  exact @norm_zero ((E →L[𝕜] F) ⧸ compactOperator (RingHom.id 𝕜) E F) _

theorem essentialNorm_add_le (S T : E →L[𝕜] F) :
    essentialNorm (S + T) ≤ essentialNorm S + essentialNorm T := by
  simp only [essentialNorm_eq_quotient_norm]
  exact norm_add_le (Submodule.Quotient.mk S :
    (E →L[𝕜] F) ⧸ compactOperator (RingHom.id 𝕜) E F) (Submodule.Quotient.mk T)

@[simp] theorem essentialNorm_smul (a : 𝕜) (T : E →L[𝕜] F) :
    essentialNorm (a • T) = ‖a‖ * essentialNorm T := by
  letI : NormSMulClass 𝕜 ((E →L[𝕜] F) ⧸ compactOperator (RingHom.id 𝕜) E F) :=
    @NormedSpace.toNormSMulClass 𝕜
      ((E →L[𝕜] F) ⧸ compactOperator (RingHom.id 𝕜) E F) _ _ _
  simp only [essentialNorm_eq_quotient_norm]
  exact norm_smul a (Submodule.Quotient.mk T :
    (E →L[𝕜] F) ⧸ compactOperator (RingHom.id 𝕜) E F)

/-- Completeness of the range ensures that compact operators form a closed set. -/
theorem essentialNorm_eq_zero_iff [CompleteSpace F] (T : E →L[𝕜] F) :
    essentialNorm T = 0 ↔ IsCompactOperator T := by
  letI : IsClosed ((compactOperator (RingHom.id 𝕜) E F).toAddSubgroup : Set (E →L[𝕜] F)) :=
    isClosed_setOf_isCompactOperator
  rw [essentialNorm_eq_quotient_norm]
  exact QuotientAddGroup.norm_mk_eq_zero

theorem essentialNorm_pos [CompleteSpace F] {T : E →L[𝕜] F}
    (hT : ¬ IsCompactOperator T) : 0 < essentialNorm T := by
  exact lt_of_le_of_ne (essentialNorm_nonneg T)
    (Ne.symm fun h => hT ((essentialNorm_eq_zero_iff T).mp h))

/-- Every compact perturbation gives an upper bound for the essential norm. -/
theorem essentialNorm_le_norm_sub (T S : E →L[𝕜] F) (hS : IsCompactOperator S) :
    essentialNorm T ≤ ‖T - S‖ := by
  apply csInf_le
  · exact ⟨0, by rintro r ⟨R, _, rfl⟩; exact norm_nonneg _⟩
  · exact ⟨S, hS, rfl⟩

/-- Infima can be approximated by actual compact perturbations. -/
theorem exists_compact_norm_sub_lt (T : E →L[𝕜] F) {ε : ℝ} (hε : 0 < ε) :
    ∃ S : E →L[𝕜] F, IsCompactOperator S ∧ ‖T - S‖ < essentialNorm T + ε := by
  have hne : ({r : ℝ | ∃ S : E →L[𝕜] F,
      IsCompactOperator S ∧ r = ‖T - S‖} : Set ℝ).Nonempty :=
    ⟨‖T - 0‖, 0, isCompactOperator_zero, rfl⟩
  obtain ⟨r, ⟨S, hS, rfl⟩, hr⟩ := exists_lt_of_csInf_lt hne
    (show essentialNorm T < essentialNorm T + ε by linarith)
  exact ⟨S, hS, hr⟩

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- Postcomposition preserves compactness and multiplies distance by at most ‖A‖. -/
theorem essentialNorm_comp_le_left (A : F →L[𝕜] G) (T : E →L[𝕜] F) :
    essentialNorm (A.comp T) ≤ ‖A‖ * essentialNorm T := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have ha : 0 < ‖A‖ + 1 := by positivity
  obtain ⟨S, hS, happrox⟩ := exists_compact_norm_sub_lt T (div_pos hε ha)
  have hbound := essentialNorm_le_norm_sub (A.comp T) (A.comp S) (hS.clm_comp A)
  rw [← ContinuousLinearMap.comp_sub] at hbound
  have hnorm := ContinuousLinearMap.opNorm_comp_le A (T - S)
  have hmul := mul_le_mul_of_nonneg_left happrox.le (norm_nonneg A)
  have hdiv : ε / (‖A‖ + 1) * (‖A‖ + 1) = ε := div_mul_cancel₀ ε (ne_of_gt ha)
  have hsmall : 0 ≤ ε / (‖A‖ + 1) := le_of_lt (div_pos hε ha)
  nlinarith

/-- The corresponding estimate for precomposition. -/
theorem essentialNorm_comp_le_right (T : F →L[𝕜] G) (B : E →L[𝕜] F) :
    essentialNorm (T.comp B) ≤ essentialNorm T * ‖B‖ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hb : 0 < ‖B‖ + 1 := by positivity
  obtain ⟨S, hS, happrox⟩ := exists_compact_norm_sub_lt T (div_pos hε hb)
  have hbound := essentialNorm_le_norm_sub (T.comp B) (S.comp B) (hS.comp_clm B)
  rw [← ContinuousLinearMap.sub_comp] at hbound
  have hnorm := ContinuousLinearMap.opNorm_comp_le (T - S) B
  have hmul := mul_le_mul_of_nonneg_right happrox.le (norm_nonneg B)
  have hdiv : ε / (‖B‖ + 1) * (‖B‖ + 1) = ε := div_mul_cancel₀ ε (ne_of_gt hb)
  have hsmall : 0 ≤ ε / (‖B‖ + 1) := le_of_lt (div_pos hε hb)
  nlinarith

/-- The estimate used on V* T* U* in the upper-bound half of Theorem 1.7. -/
theorem essentialNorm_sandwich_le
    {H : Type*} [NormedAddCommGroup H] [NormedSpace 𝕜 H]
    (A : G →L[𝕜] H) (T : F →L[𝕜] G) (B : E →L[𝕜] F) :
    essentialNorm ((A.comp T).comp B) ≤ ‖A‖ * essentialNorm T * ‖B‖ := by
  exact (essentialNorm_comp_le_right (A.comp T) B).trans
    (mul_le_mul_of_nonneg_right (essentialNorm_comp_le_left A T) (norm_nonneg B))

/-- Isometric changes of range coordinates preserve the essential norm. -/
theorem essentialNorm_isometryEquiv_comp (e : F ≃ₗᵢ[𝕜] G) (T : E →L[𝕜] F) :
    essentialNorm (e.toLinearIsometry.toContinuousLinearMap.comp T) = essentialNorm T := by
  have hle (A : F ≃ₗᵢ[𝕜] G) (S : E →L[𝕜] F) :
      essentialNorm (A.toLinearIsometry.toContinuousLinearMap.comp S) ≤ essentialNorm S := by
    apply (essentialNorm_comp_le_left _ _).trans
    exact (mul_le_mul_of_nonneg_right A.toLinearIsometry.norm_toContinuousLinearMap_le
      (essentialNorm_nonneg S)).trans_eq (one_mul _)
  apply le_antisymm (hle e T)
  have hback := essentialNorm_comp_le_left e.symm.toLinearIsometry.toContinuousLinearMap
    (e.toLinearIsometry.toContinuousLinearMap.comp T)
  have heq : e.symm.toLinearIsometry.toContinuousLinearMap.comp
      (e.toLinearIsometry.toContinuousLinearMap.comp T) = T := by
    ext x
    exact e.symm_apply_apply _
  rw [heq] at hback
  exact hback.trans ((mul_le_mul_of_nonneg_right
    e.symm.toLinearIsometry.norm_toContinuousLinearMap_le (essentialNorm_nonneg _)).trans_eq
      (one_mul _))

end JLMS

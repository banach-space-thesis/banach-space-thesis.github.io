import JLMS.Factorization

/-!
# Balancing the norms of factor maps

This is the rescaling step of Lemma 8.2. Multiplying U by a positive real
scalar and V by its reciprocal preserves UTV and gives equal norms. A small
product therefore gives separate small bounds for both maps.
-/

noncomputable section

namespace JLMS

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

/-- Balance two nonzero maps by reciprocal scalar multiplication. The resulting
norms are equal and their squared value is the original norm product. -/
theorem exists_balanced_factor_maps (U : F →L[𝕜] Z) (V : Z →L[𝕜] E)
    (hU : 0 < ‖U‖) (hV : 0 < ‖V‖) :
    ∃ a : 𝕜, a ≠ 0 ∧ ‖a • U‖ = ‖a⁻¹ • V‖ ∧ ‖a • U‖ ^ 2 = ‖U‖ * ‖V‖ := by
  let t : ℝ := Real.sqrt (‖V‖ / ‖U‖)
  have ht : 0 < t := Real.sqrt_pos.mpr (div_pos hV hU)
  have hsq : t ^ 2 * ‖U‖ = ‖V‖ := by
    rw [show t ^ 2 = ‖V‖ / ‖U‖ from Real.sq_sqrt (div_pos hV hU).le,
      div_mul_cancel₀ _ (ne_of_gt hU)]
  let a : 𝕜 := (t : 𝕜)
  have ha : ‖a‖ = t := by
    change ‖(t : 𝕜)‖ = t
    rw [RCLike.norm_ofReal, abs_of_pos ht]
  have ha0 : a ≠ 0 := by
    intro hz
    have := ha
    rw [hz, norm_zero] at this
    linarith
  letI : NormSMulClass 𝕜 (F →L[𝕜] Z) :=
    @NormedSpace.toNormSMulClass 𝕜 (F →L[𝕜] Z) _ _ _
  letI : NormSMulClass 𝕜 (Z →L[𝕜] E) :=
    @NormedSpace.toNormSMulClass 𝕜 (Z →L[𝕜] E) _ _ _
  refine ⟨a, ha0, ?_, ?_⟩
  · rw [norm_smul, norm_smul, norm_inv, ha]
    apply (mul_left_cancel₀ (ne_of_gt ht))
    calc
      t * (t * ‖U‖) = ‖V‖ := by nlinarith [hsq]
      _ = t * (t⁻¹ * ‖V‖) := by rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt ht), one_mul]
  · rw [norm_smul, ha]
    calc
      (t * ‖U‖) ^ 2 = (t ^ 2 * ‖U‖) * ‖U‖ := by ring
      _ = ‖U‖ * ‖V‖ := by rw [hsq, mul_comm]

/-- The paper's rescaling claim, with strict bounds for both factor maps. -/
theorem exists_small_factor_maps (T : E →L[𝕜] F)
    (U : F →L[𝕜] cZero 𝕜) (V : cZero 𝕜 →L[𝕜] E)
    (hfactor : (U.comp T).comp V = ContinuousLinearMap.id 𝕜 (cZero 𝕜))
    {ρ : ℝ} (hρ : 0 < ρ) (hprod : ‖U‖ * ‖V‖ < ρ ^ 2) :
    ∃ U' : F →L[𝕜] cZero 𝕜, ∃ V' : cZero 𝕜 →L[𝕜] E,
      (U'.comp T).comp V' = ContinuousLinearMap.id 𝕜 (cZero 𝕜) ∧
      ‖U'‖ < ρ ∧ ‖V'‖ < ρ := by
  have hp := factorization_norm_product_pos T U V hfactor (essentialNorm_cZero_dual_identity 𝕜)
  have hU : 0 < ‖U‖ := by nlinarith [norm_nonneg U, norm_nonneg V]
  have hV : 0 < ‖V‖ := by nlinarith [norm_nonneg U, norm_nonneg V]
  obtain ⟨a, ha, hbalance, hnorm⟩ := exists_balanced_factor_maps U V hU hV
  have hsmall : ‖a • U‖ < ρ := by nlinarith [norm_nonneg (a • U)]
  refine ⟨a • U, a⁻¹ • V, ?_, hsmall, ?_⟩
  · have heq : (((a • U).comp T).comp (a⁻¹ • V)) = (U.comp T).comp V := by
      apply ContinuousLinearMap.ext
      intro x
      change a • U (T (a⁻¹ • V x)) = U (T (V x))
      rw [map_smul, map_smul, smul_smul, mul_inv_cancel₀ ha, one_smul]
    exact heq.trans hfactor
  · rw [← hbalance]
    exact hsmall

end JLMS

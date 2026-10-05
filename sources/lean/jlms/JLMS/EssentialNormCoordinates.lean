import JLMS.EssentialNorm

/-! # Essential norm under isometric changes of source coordinates -/

noncomputable section
namespace JLMS
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]

theorem essentialNorm_comp_isometryEquiv (e : E ≃ₗᵢ[𝕜] F) (T : F →L[𝕜] G) :
    essentialNorm (T.comp e.toLinearIsometry.toContinuousLinearMap) = essentialNorm T := by
  have hle (A : E ≃ₗᵢ[𝕜] F) (S : F →L[𝕜] G) :
      essentialNorm (S.comp A.toLinearIsometry.toContinuousLinearMap) ≤ essentialNorm S := by
    apply (essentialNorm_comp_le_right _ _).trans
    exact (mul_le_mul_of_nonneg_left A.toLinearIsometry.norm_toContinuousLinearMap_le
      (essentialNorm_nonneg S)).trans_eq (mul_one _)
  apply le_antisymm (hle e T)
  have hback := essentialNorm_comp_le_right
    (T.comp e.toLinearIsometry.toContinuousLinearMap) e.symm.toLinearIsometry.toContinuousLinearMap
  have heq : (T.comp e.toLinearIsometry.toContinuousLinearMap).comp
      e.symm.toLinearIsometry.toContinuousLinearMap = T := by
    apply ContinuousLinearMap.ext
    intro x
    simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
      LinearIsometryEquiv.coe_toLinearIsometry, e.apply_symm_apply]
  rw [heq] at hback
  exact hback.trans ((mul_le_mul_of_nonneg_left
    e.symm.toLinearIsometry.norm_toContinuousLinearMap_le (essentialNorm_nonneg _)).trans_eq (mul_one _))

end JLMS

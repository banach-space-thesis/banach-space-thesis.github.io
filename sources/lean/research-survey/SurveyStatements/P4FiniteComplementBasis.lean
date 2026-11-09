import SurveyStatements.P4FiniteComplement

/-! The complemented block product carries an actual finite basis with a
uniform prefix bound in its inherited product norm. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

open Module

namespace SurveyStatements.P4

universe u v w
variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type w} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {N : ℕ}

lemma finiteBasisPrefix_map [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
    (b : Basis (Fin N) 𝕜 E) (e : E ≃L[𝕜] F) (k : Fin (N + 1)) :
    finiteBasisPrefix (b.map e.toLinearEquiv) k =
      e.toContinuousLinearMap.comp ((finiteBasisPrefix b k).comp e.symm.toContinuousLinearMap) := by
  classical
  apply ContinuousLinearMap.ext
  intro x
  simp only [finiteBasisPrefix, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.comp_apply, LinearMap.coe_toContinuousLinearMap', Basis.coord_apply,
    Basis.map_apply, Basis.map_repr, LinearEquiv.coe_toLinearMap, map_sum, map_smul]
  rfl

namespace FiniteBasisExtension

variable [FiniteDimensional 𝕜 E] (G : FiniteBasisExtension 𝕜 E)

def complementBasis : Basis (Fin G.length) 𝕜 (E × G.Complement) :=
  G.basis.map G.splitContinuousLinearEquiv.toLinearEquiv

lemma norm_splitContinuousLinearEquiv_le :
    ‖G.splitContinuousLinearEquiv.toContinuousLinearMap‖ ≤ 3 := by
  apply G.splitContinuousLinearEquiv.toContinuousLinearMap.opNorm_le_bound (by norm_num)
  exact G.norm_splitLinearEquiv_le

lemma norm_splitContinuousLinearEquiv_symm_le :
    ‖G.splitContinuousLinearEquiv.symm.toContinuousLinearMap‖ ≤ 3 := by
  apply G.splitContinuousLinearEquiv.symm.toContinuousLinearMap.opNorm_le_bound (by norm_num)
  exact G.norm_splitLinearEquiv_symm_le

lemma norm_complementBasis_prefix_le (k : Fin (G.length + 1)) :
    ‖finiteBasisPrefix G.complementBasis k‖ ≤ 9 := by
  rw [complementBasis, finiteBasisPrefix_map]
  calc
    _ ≤ ‖G.splitContinuousLinearEquiv.toContinuousLinearMap‖ *
        ‖(finiteBasisPrefix G.basis k).comp
          G.splitContinuousLinearEquiv.symm.toContinuousLinearMap‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 3 * (‖finiteBasisPrefix G.basis k‖ *
        ‖G.splitContinuousLinearEquiv.symm.toContinuousLinearMap‖) :=
      mul_le_mul G.norm_splitContinuousLinearEquiv_le
        (ContinuousLinearMap.opNorm_comp_le _ _)
        (ContinuousLinearMap.opNorm_nonneg _) (by norm_num)
    _ ≤ 3 * (1 * 3) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact mul_le_mul (G.norm_prefix_le k) G.norm_splitContinuousLinearEquiv_symm_le
        (ContinuousLinearMap.opNorm_nonneg _) (by norm_num)
    _ = 9 := by norm_num

end FiniteBasisExtension

end SurveyStatements.P4

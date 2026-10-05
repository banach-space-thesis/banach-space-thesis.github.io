import ThesisCommon.Residuum

/-! Norm and composition laws for the shared library's existing Banach
adjoint. It is linear precomposition for both real and complex scalars. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

@[simp] theorem banachAdjoint_apply (T : X →L[𝕜] Y) (f : Y →L[𝕜] 𝕜) :
    banachAdjoint T f = f.comp T := rfl

theorem banachAdjoint_comp (S : Y →L[𝕜] Z) (T : X →L[𝕜] Y) :
    banachAdjoint (S.comp T) = (banachAdjoint T).comp (banachAdjoint S) := by
  ext f x
  rfl

theorem norm_banachAdjoint (T : X →L[𝕜] Y) : ‖banachAdjoint T‖ = ‖T‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
    intro f
    simpa only [banachAdjoint_apply, mul_comm] using ContinuousLinearMap.opNorm_comp_le f T
  · apply ContinuousLinearMap.opNorm_le_bound T (norm_nonneg (banachAdjoint T))
    intro x
    apply NormedSpace.norm_le_dual_bound 𝕜 (T x) (mul_nonneg (norm_nonneg (banachAdjoint T)) (norm_nonneg x))
    intro f
    calc
      ‖f (T x)‖ ≤ ‖banachAdjoint T f‖ * ‖x‖ := (banachAdjoint T f).le_opNorm x
      _ ≤ (‖banachAdjoint T‖ * ‖f‖) * ‖x‖ :=
        mul_le_mul_of_nonneg_right ((banachAdjoint T).le_opNorm f) (norm_nonneg x)
      _ = (‖banachAdjoint T‖ * ‖x‖) * ‖f‖ := by ring

end ThesisCommon


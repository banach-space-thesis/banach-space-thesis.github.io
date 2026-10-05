import ThesisCommon.Analysis.EllOneWeakEssentialIdentity

/-! Sharp upper bounds for the constants of actual identity factorizations.
The generic estimate is a consequence of the weakly compact operator ideal
laws; for scalar ℓ¹ the independently proved identity norm is exactly one. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

theorem weakEssentialNorm_id_le_factorization_norms
    (T : E →L[𝕜] F) (U : F →L[𝕜] Z) (V : Z →L[𝕜] E)
    (h : U.comp (T.comp V) = ContinuousLinearMap.id 𝕜 Z) :
    weakEssentialNorm (ContinuousLinearMap.id 𝕜 Z) ≤ ‖U‖ * ‖V‖ * weakEssentialNorm T := by
  calc
    weakEssentialNorm (ContinuousLinearMap.id 𝕜 Z) = weakEssentialNorm (U.comp (T.comp V)) :=
      congrArg weakEssentialNorm h.symm
    _ ≤ ‖U‖ * weakEssentialNorm (T.comp V) := weakEssentialNorm_comp_left_le U _
    _ ≤ ‖U‖ * (weakEssentialNorm T * ‖V‖) :=
      mul_le_mul_of_nonneg_left (weakEssentialNorm_comp_right_le T V) (norm_nonneg U)
    _ = ‖U‖ * ‖V‖ * weakEssentialNorm T := by ring

theorem weakEssentialNorm_id_mul_factorization_constant_le
    (T : E →L[𝕜] F) (U : F →L[𝕜] Z) (V : Z →L[𝕜] E)
    (h : U.comp (T.comp V) = ContinuousLinearMap.id 𝕜 Z) :
    weakEssentialNorm (ContinuousLinearMap.id 𝕜 Z) * (‖U‖⁻¹ * ‖V‖⁻¹) ≤ weakEssentialNorm T := by
  by_cases hU : ‖U‖ = 0
  · simp only [hU, inv_zero, zero_mul, mul_zero]
    exact weakEssentialNorm_nonneg T
  by_cases hV : ‖V‖ = 0
  · simp only [hV, inv_zero, mul_zero]
    exact weakEssentialNorm_nonneg T
  have hpos : 0 < ‖U‖ * ‖V‖ := mul_pos
    (lt_of_le_of_ne (norm_nonneg U) (Ne.symm hU))
    (lt_of_le_of_ne (norm_nonneg V) (Ne.symm hV))
  have hbound := weakEssentialNorm_id_le_factorization_norms T U V h
  have hdiv : weakEssentialNorm (ContinuousLinearMap.id 𝕜 Z) / (‖U‖ * ‖V‖) ≤
      weakEssentialNorm T := (div_le_iff₀ hpos).mpr (by
    simpa only [mul_comm (weakEssentialNorm T)] using hbound)
  simpa only [div_eq_mul_inv, mul_inv_rev, mul_comm ‖V‖⁻¹ ‖U‖⁻¹] using hdiv

theorem scalarEllOne_factorization_constant_le_weakEssentialNorm
    (T : E →L[𝕜] F) (U : F →L[𝕜] lp (fun _ : ℕ => 𝕜) 1)
    (V : lp (fun _ : ℕ => 𝕜) 1 →L[𝕜] E)
    (h : U.comp (T.comp V) = ContinuousLinearMap.id 𝕜 (lp (fun _ : ℕ => 𝕜) 1)) :
    ‖U‖⁻¹ * ‖V‖⁻¹ ≤ weakEssentialNorm T := by
  simpa only [weakEssentialNorm_id_scalarEllOne, one_mul] using
    weakEssentialNorm_id_mul_factorization_constant_le T U V h

end ThesisCommon

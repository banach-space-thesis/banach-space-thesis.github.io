import ThesisCommon.Analysis.Factorization

noncomputable section
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

/-- The rescaling step in UPFP Proposition 5.5: absorb ‖V‖ into U and
divide V by ‖V‖. The zero case is handled explicitly. -/
theorem FactorsIdentityWith.normalized {T : X →L[𝕜] Y} {C : ℝ}
    (h : FactorsIdentityWith T Z C) :
    ∃ U : Y →L[𝕜] Z, ∃ V : Z →L[𝕜] X,
      (U.comp T).comp V = ContinuousLinearMap.id 𝕜 Z ∧ ‖U‖ ≤ C ∧ ‖V‖ ≤ 1 := by
  obtain ⟨U, V, heq, hn⟩ := h
  have hC : 0 ≤ C := (mul_nonneg (norm_nonneg _) (norm_nonneg _)).trans hn
  by_cases hV : V = 0
  · refine ⟨0, 0, ?_, by simpa using hC, by simp⟩
    simpa [hV] using heq
  have hv : 0 < ‖V‖ := norm_pos_iff.mpr hV
  let a : 𝕜 := (‖V‖ : 𝕜)
  have ha : ‖a‖ = ‖V‖ := by simp [a]
  have ha0 : a ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at ha
    linarith
  letI : NormSMulClass 𝕜 (Y →L[𝕜] Z) :=
    @NormedSpace.toNormSMulClass 𝕜 (Y →L[𝕜] Z) _ _ _
  letI : NormSMulClass 𝕜 (Z →L[𝕜] X) :=
    @NormedSpace.toNormSMulClass 𝕜 (Z →L[𝕜] X) _ _ _
  refine ⟨a • U, a⁻¹ • V, ?_, ?_, ?_⟩
  · calc
      ((a • U).comp T).comp (a⁻¹ • V) = (U.comp T).comp V := by
        ext z
        change a • U (T (a⁻¹ • V z)) = U (T (V z))
        rw [map_smul, map_smul, smul_smul, mul_inv_cancel₀ ha0, one_smul]
      _ = ContinuousLinearMap.id 𝕜 Z := heq
  · simpa only [norm_smul, ha, mul_comm] using hn
  · simp only [norm_smul, norm_inv, ha, inv_mul_cancel₀ hv.ne', le_refl]

end ThesisCommon

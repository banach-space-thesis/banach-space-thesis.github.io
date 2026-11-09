import BanachIsometric.HermitianRelativeOperator

/-!
# Normalizing the actual simultaneous section similarities

An actual scalar-linear similarity for the first norm becomes an actual
linear isometry after division by its positive scaling constant. Its scaling
for the second Hermitian square is derived explicitly.
-/

namespace BanachIsometric

noncomputable section

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

def normalizedLinearSimilarity (T : E ≃ₗ[𝕜] F) (c : ℝ) (hc : 0 < c)
    (hT : ∀ x, ‖T x‖ = c * ‖x‖) : E ≃ₗᵢ[𝕜] F where
  toLinearEquiv := T.trans (LinearEquiv.smulOfNeZero 𝕜 F ((c : 𝕜)⁻¹)
    (inv_ne_zero (RCLike.ofReal_ne_zero.mpr hc.ne')))
  norm_map' x := by
    change ‖(c : 𝕜)⁻¹ • T x‖ = ‖x‖
    rw [norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_pos hc, hT]
    exact inv_mul_cancel_left₀ hc.ne' ‖x‖

@[simp]
theorem normalizedLinearSimilarity_apply (T : E ≃ₗ[𝕜] F) (c : ℝ) (hc : 0 < c)
    (hT : ∀ x, ‖T x‖ = c * ‖x‖) (x : E) :
    normalizedLinearSimilarity T c hc hT x = (c : 𝕜)⁻¹ • T x := rfl

theorem re_sesqForm_self_smul (B : E →ₗ⋆[𝕜] E →ₗ[𝕜] 𝕜) (a : 𝕜) (x : E) :
    RCLike.re (B (a • x) (a • x)) = ‖a‖ ^ 2 * RCLike.re (B x x) := by
  simp only [B.map_smulₛₗ, LinearMap.smul_apply, LinearMap.map_smul, smul_eq_mul]
  rw [← mul_assoc, RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.re_ofReal_mul]

/-- The scale of the second square after normalizing the first norm is
`(c₂/c₁)²`, obtained from the genuine simultaneous similarity. -/
theorem exists_normalized_simultaneous_hermitian_similarity
    (B : E →ₗ⋆[𝕜] E →ₗ[𝕜] 𝕜) (C : F →ₗ⋆[𝕜] F →ₗ[𝕜] 𝕜)
    (T : E ≃ₗ[𝕜] F) (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hfirst : ∀ x, ‖T x‖ = c₁ * ‖x‖)
    (hsecond : ∀ x, RCLike.re (C (T x) (T x)) = c₂ ^ 2 * RCLike.re (B x x)) :
    ∃ U : E ≃ₗᵢ[𝕜] F, ∃ c : ℝ, 0 < c ∧
      ∀ x, RCLike.re (C (U x) (U x)) = c * RCLike.re (B x x) := by
  refine ⟨normalizedLinearSimilarity T c₁ hc₁ hfirst, (c₂ / c₁) ^ 2,
    sq_pos_of_pos (div_pos hc₂ hc₁), ?_⟩
  intro x
  rw [normalizedLinearSimilarity_apply, re_sesqForm_self_smul, norm_inv,
    RCLike.norm_ofReal, abs_of_pos hc₁, hsecond]
  ring

end

end BanachIsometric

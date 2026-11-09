import SurveyStatements.P3DenseExtension

/-! Applying the constructive extraction to the inverse of the adjoint on a
subspace where it is bounded below. No closed-range theorem is needed. -/

noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 1200000

namespace SurveyStatements.P3

variable {𝕜 : Type*} [RCLike 𝕜]
variable {X Y E : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

theorem not_strictlyCosingular_of_adjoint_embedding
    [CompleteSpace X] [TopologicalSpace.SeparableSpace Y]
    (T : X →L[𝕜] Y) (j : E →ₗᵢ[𝕜] (Y →L[𝕜] 𝕜))
    (hE : ¬ FiniteDimensional 𝕜 E) (c : ℝ) (hc : 0 < c)
    (hbound : ∀ e : E, c * ‖e‖ ≤ ‖adjoint T (j e)‖) :
    ¬ IsStrictlyCosingular T := by
  let B : E →L[𝕜] (X →L[𝕜] 𝕜) := (adjoint T).comp j.toContinuousLinearMap
  have hBbound (e : E) : c * ‖e‖ ≤ ‖B e‖ := hbound e
  have hBinj : Function.Injective B := by
    intro a b hab
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    apply le_antisymm _ (norm_nonneg _)
    apply (mul_le_mul_left hc).mp
    simpa only [map_sub, hab, sub_self, norm_zero, mul_zero] using hBbound (a - b)
  let R : Submodule 𝕜 (X →L[𝕜] 𝕜) := LinearMap.range B.toLinearMap
  letI : NormedAddCommGroup R := inferInstance
  letI : NormedSpace 𝕜 R := inferInstance
  let e : E ≃ₗ[𝕜] R := LinearEquiv.ofInjective B.toLinearMap hBinj
  have he (r : R) : B (e.symm r) = r.val :=
    congrArg Subtype.val (e.apply_symm_apply r)
  let U₀ : R →ₗ[𝕜] (Y →L[𝕜] 𝕜) := j.toLinearMap.comp e.symm.toLinearMap
  have hUbound (r : R) : ‖U₀ r‖ ≤ c⁻¹ * ‖r‖ := by
    have hb := hBbound (e.symm r)
    rw [he] at hb
    calc
      ‖U₀ r‖ = ‖e.symm r‖ := j.norm_map (e.symm r)
      _ = c⁻¹ * (c * ‖e.symm r‖) := by
        rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
      _ ≤ c⁻¹ * ‖r‖ := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hc.le)
  let U : R →L[𝕜] (Y →L[𝕜] 𝕜) := U₀.mkContinuous c⁻¹ hUbound
  have hR : ¬ FiniteDimensional 𝕜 R := by
    intro hR
    letI := hR
    exact hE (FiniteDimensional.of_injective (V₂ := R) e.toLinearMap e.injective)
  let J : R →ₗᵢ[𝕜] (X →L[𝕜] 𝕜) := R.subtypeₗᵢ
  have hAdj (r : R) : adjoint T (U r) = J r := he r
  obtain ⟨v, hv, A, hA⟩ := exists_separable_extraction J U hR
  have hgv : LinearIndependent 𝕜 (fun i => J (v i)) :=
    hv.map' J.toLinearMap (LinearMap.ker_eq_bot.mpr J.injective)
  apply not_strictlyCosingular_of_generator_pairing (fun i => J (v i)) hgv T A
  intro i x
  rw [hA]
  exact congrArg (fun f : X →L[𝕜] 𝕜 => f x) (hAdj (v i))

theorem adjoint_strictlySingular_of_strictlyCosingular
    [CompleteSpace X] [TopologicalSpace.SeparableSpace Y]
    (T : X →L[𝕜] Y) (hT : IsStrictlyCosingular T) : IsStrictlySingular (adjoint T) := by
  intro Z _hclosed hZ hbelow
  obtain ⟨c, hc, hbound⟩ := hbelow
  apply not_strictlyCosingular_of_adjoint_embedding T Z.subtypeₗᵢ hZ c hc _ hT
  intro z
  exact hbound z.val z.property

end SurveyStatements.P3

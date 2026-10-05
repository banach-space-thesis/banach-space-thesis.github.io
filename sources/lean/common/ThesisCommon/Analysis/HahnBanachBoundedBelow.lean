import Mathlib.Analysis.NormedSpace.HahnBanach.Extension
import Mathlib.Algebra.Module.Submodule.Equiv

/-! Quantitative Hahn–Banach lifting along an actual bounded-below map.
No complemented-range assumption is used. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem exists_dual_extension_along_lower_bound (S : E →L[𝕜] F)
    {c : ℝ} (hc : 0 < c) (hS : ∀ x, c * ‖x‖ ≤ ‖S x‖) (φ : E →L[𝕜] 𝕜) :
    ∃ ψ : F →L[𝕜] 𝕜, ψ.comp S = φ ∧ ‖ψ‖ ≤ c⁻¹ * ‖φ‖ := by
  have hinj : Function.Injective S := by
    intro x y hxy
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    have h := hS (x - y)
    rw [map_sub, hxy, sub_self, norm_zero] at h
    nlinarith [norm_nonneg (x - y)]
  let e : E ≃ₗ[𝕜] LinearMap.range S.toLinearMap := LinearEquiv.ofInjective S.toLinearMap hinj
  have he (y : LinearMap.range S.toLinearMap) : S (e.symm y) = (y : F) :=
    LinearEquiv.ofInjective_symm_apply S.toLinearMap y
  have hnorm (y : LinearMap.range S.toLinearMap) : ‖e.symm y‖ ≤ c⁻¹ * ‖y‖ := by
    have h := hS (e.symm y)
    rw [he] at h
    have hd : ‖e.symm y‖ ≤ ‖(y : F)‖ / c := (le_div_iff₀ hc).mpr (by simpa [mul_comm] using h)
    simpa only [div_eq_mul_inv, mul_comm ‖(y : F)‖ c⁻¹] using hd
  let L : LinearMap.range S.toLinearMap →L[𝕜] 𝕜 :=
    (φ.toLinearMap.comp e.symm.toLinearMap).mkContinuous (c⁻¹ * ‖φ‖) (fun y => by
      exact (φ.le_opNorm (e.symm y)).trans ((mul_le_mul_of_nonneg_left (hnorm y)
        (norm_nonneg φ)).trans_eq (by ring)))
  obtain ⟨ψ, hψ, hψnorm⟩ := exists_extension_norm_eq (LinearMap.range S.toLinearMap) L
  refine ⟨ψ, ?_, hψnorm.le.trans ?_⟩
  · apply ContinuousLinearMap.ext
    intro x
    have h := hψ (e x)
    change ψ (S x) = φ (e.symm (e x)) at h
    simpa only [LinearEquiv.symm_apply_apply] using h
  · exact LinearMap.mkContinuous_norm_le _ (mul_nonneg (inv_nonneg.mpr hc.le) (norm_nonneg φ)) _

end ThesisCommon

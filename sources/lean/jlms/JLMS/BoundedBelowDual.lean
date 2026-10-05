import JLMS.Adjoint
import Mathlib.Topology.Bases

/-!
# Dual surjectivity for a bounded-below embedding

The inverse on the range is bounded by 1/c. Compose any functional with this
inverse and extend by Hahn–Banach. Thus the Banach adjoint of a bounded-below
embedding is surjective. In particular, separability of the ambient dual
passes to the embedded space's dual.
-/

noncomputable section

open TopologicalSpace

namespace JLMS

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]

theorem exists_dual_extension_of_bounded_below (J : E →L[𝕜] X)
    {c : ℝ} (hc : 0 < c) (hlower : ∀ a, c * ‖a‖ ≤ ‖J a‖) (φ : E →L[𝕜] 𝕜) :
    ∃ ψ : X →L[𝕜] 𝕜, ‖ψ‖ ≤ ‖φ‖ / c ∧ ∀ a, ψ (J a) = φ a := by
  have hinj : Function.Injective J := by
    intro a b hab
    have h := hlower (a - b)
    simp only [map_sub, hab, sub_self, norm_zero] at h
    have hn : ‖a - b‖ = 0 := by nlinarith [norm_nonneg (a - b)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hn)
  let e := LinearEquiv.ofInjective J.toLinearMap hinj
  have hbound (x : LinearMap.range J) : ‖e.symm x‖ ≤ (1 / c) * ‖x‖ := by
    have h := hlower (e.symm x)
    have he : J (e.symm x) = (x : X) := congrArg Subtype.val (e.apply_symm_apply x)
    rw [he] at h
    rw [one_div, mul_comm, ← div_eq_mul_inv]
    exact (le_div_iff₀ hc).mpr (by simpa [mul_comm] using h)
  let L : LinearMap.range J →L[𝕜] E := e.symm.toLinearMap.mkContinuous (1 / c) hbound
  have hφL : ‖φ.comp L‖ ≤ ‖φ‖ / c := by
    apply ContinuousLinearMap.opNorm_le_bound _ (div_nonneg (norm_nonneg _) hc.le)
    intro x
    calc
      ‖φ (L x)‖ ≤ ‖φ‖ * ‖L x‖ := φ.le_opNorm _
      _ ≤ ‖φ‖ * ((1 / c) * ‖x‖) := mul_le_mul_of_nonneg_left (hbound x) (norm_nonneg _)
      _ = (‖φ‖ / c) * ‖x‖ := by ring
  obtain ⟨ψ, hψ, hnorm⟩ := exists_extension_norm_eq (LinearMap.range J) (φ.comp L)
  refine ⟨ψ, hnorm ▸ hφL, ?_⟩
  intro a
  have h := hψ (e a)
  change ψ (J a) = φ (e.symm (e a)) at h
  simpa only [LinearEquiv.symm_apply_apply] using h

theorem banachAdjoint_surjective_of_bounded_below (J : E →L[𝕜] X)
    {c : ℝ} (hc : 0 < c) (hlower : ∀ a, c * ‖a‖ ≤ ‖J a‖) :
    Function.Surjective (banachAdjoint J) := by
  intro φ
  obtain ⟨ψ, hnorm, hψ⟩ := exists_dual_extension_of_bounded_below J hc hlower φ
  refine ⟨ψ, ?_⟩
  exact ContinuousLinearMap.ext hψ

theorem dual_separable_of_bounded_below [SeparableSpace (X →L[𝕜] 𝕜)]
    (J : E →L[𝕜] X) {c : ℝ} (hc : 0 < c) (hlower : ∀ a, c * ‖a‖ ≤ ‖J a‖) :
    SeparableSpace (E →L[𝕜] 𝕜) :=
  (banachAdjoint_surjective_of_bounded_below J hc hlower).denseRange.separableSpace
    (banachAdjoint J).continuous

end JLMS

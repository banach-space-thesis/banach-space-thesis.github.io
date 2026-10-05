import Posets.ProductQuotientCoordinates
import Posets.StrongSplitTransport

/-! Preserve the quantitative splitting data when changing algebra coordinates. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 3
open ThesisCommon
namespace Posets

variable {𝕜 Y C D : Type} [RCLike 𝕜]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  [NormedAddCommGroup C] [NormedSpace 𝕜 C] [Mul C]
  [NormedAddCommGroup D] [NormedSpace 𝕜 D] [Mul D]

theorem product_strongSplit_coordinates (c : C ≃ₗᵢ[𝕜] D)
    (hc : ∀ a b, c (a * b) = c a * c b)
    (θ : BoundedHom 𝕜 (Y →L[𝕜] Y) D) (ρ : BoundedHom 𝕜 D (Y →L[𝕜] Y))
    (hsplit : StrongSplit 𝕜 Y D θ ρ) (hρ : Isometry ρ)
    (hθ : ‖θ.toContinuousLinearMap‖ ≤ 1) :
    ∃ Θ : BoundedHom 𝕜 (Y →L[𝕜] Y) C,
    ∃ R : BoundedHom 𝕜 C (Y →L[𝕜] Y),
      StrongSplit 𝕜 Y C Θ R ∧ Isometry R ∧ ‖Θ.toContinuousLinearMap‖ ≤ 1 := by
  have hc' : ∀ a b, c.symm (a * b) = c.symm a * c.symm b := by
    intro a b
    apply c.injective
    rw [c.apply_symm_apply, hc, c.apply_symm_apply, c.apply_symm_apply]
  let e := LinearIsometryEquiv.refl 𝕜 Y
  refine ⟨transportQuotient e c.symm hc' θ, transportSection e c.symm hc' ρ,
    strongSplit_transport e c.symm hc' θ ρ hsplit,
    isometry_transportSection e c.symm hc' ρ hρ, ?_⟩
  rwa [norm_transportQuotient]

end Posets

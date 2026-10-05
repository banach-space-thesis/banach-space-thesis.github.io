import Posets.Definitions
import PosetsCommon.OperatorConjugation

/-! Strong splitting is unchanged by isometric algebra coordinates. -/
noncomputable section
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1500000
open ThesisCommon
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜] {E F C D : Type}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup C] [NormedSpace 𝕜 C] [Mul C]
  [NormedAddCommGroup D] [NormedSpace 𝕜 D] [Mul D]
  (e : E ≃ₗᵢ[𝕜] F) (c : C ≃ₗᵢ[𝕜] D)
  (hc : ∀ a b, c (a * b) = c a * c b)

def transportQuotient (θ : BoundedHom 𝕜 (E →L[𝕜] E) C) :
    BoundedHom 𝕜 (F →L[𝕜] F) D where
  toContinuousLinearMap := c.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (θ.toContinuousLinearMap.comp (operatorConjugation e).symm.toContinuousLinearMap)
  map_mul' S T := by
    change c (θ (operatorConjugation e.symm (S * T))) =
      c (θ (operatorConjugation e.symm S)) * c (θ (operatorConjugation e.symm T))
    rw [operatorConjugation_mul, θ.map_mul', hc]

def transportSection (ρ : BoundedHom 𝕜 C (E →L[𝕜] E)) :
    BoundedHom 𝕜 D (F →L[𝕜] F) where
  toContinuousLinearMap := (operatorConjugation e).toContinuousLinearMap.comp
    (ρ.toContinuousLinearMap.comp c.symm.toContinuousLinearEquiv.toContinuousLinearMap)
  map_mul' a b := by
    have hinv : c.symm (a * b) = c.symm a * c.symm b := by
      apply c.injective
      rw [c.apply_symm_apply, hc, c.apply_symm_apply, c.apply_symm_apply]
    change operatorConjugation e (ρ (c.symm (a * b))) =
      operatorConjugation e (ρ (c.symm a)) * operatorConjugation e (ρ (c.symm b))
    rw [hinv, ρ.map_mul', operatorConjugation_mul]

theorem strongSplit_transport
    (θ : BoundedHom 𝕜 (E →L[𝕜] E) C) (ρ : BoundedHom 𝕜 C (E →L[𝕜] E))
    (h : StrongSplit 𝕜 E C θ ρ) :
    StrongSplit 𝕜 F D (transportQuotient e c hc θ) (transportSection e c hc ρ) := by
  have hright : Function.RightInverse (transportSection e c hc ρ)
      (transportQuotient e c hc θ) := by
    intro a
    change c (θ ((operatorConjugation e).symm (operatorConjugation e (ρ (c.symm a))))) = a
    rw [ContinuousLinearEquiv.symm_apply_apply, h.2.2, c.apply_symm_apply]
  refine ⟨hright.surjective, ?_, hright⟩
  intro T
  change c (θ (operatorConjugation e.symm T)) = 0 ↔ _
  rw [← map_zero c, c.injective.eq_iff, h.2.1]
  exact operatorConjugation_separable_iff e.symm T

theorem isometry_transportSection (ρ : BoundedHom 𝕜 C (E →L[𝕜] E))
    (hρ : Isometry ρ) : Isometry (transportSection e c hc ρ) :=
  ((operatorConjugationIsometry e).isometry.comp hρ).comp c.symm.isometry

theorem norm_transportQuotient (θ : BoundedHom 𝕜 (E →L[𝕜] E) C) :
    ‖(transportQuotient e c hc θ).toContinuousLinearMap‖ = ‖θ.toContinuousLinearMap‖ := by
  change ‖c.toLinearIsometry.toContinuousLinearMap.comp
    (θ.toContinuousLinearMap.comp
      (operatorConjugationIsometry e).symm.toLinearIsometry.toContinuousLinearMap)‖ = _
  rw [LinearIsometry.norm_toContinuousLinearMap_comp,
    ContinuousLinearMap.opNorm_comp_linearIsometryEquiv]

end Posets

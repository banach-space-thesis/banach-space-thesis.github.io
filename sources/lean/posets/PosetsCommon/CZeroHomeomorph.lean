import PosetsCommon.CZeroRestriction

noncomputable section
open scoped ZeroAtInfty
namespace ThesisCommon
variable {𝕜 : Type} [RCLike 𝕜] {K L : Type*} [TopologicalSpace K] [TopologicalSpace L]

def cZeroHomeomorphPull (e : K ≃ₜ L) : C₀(L, 𝕜) →L[𝕜] C₀(K, 𝕜) :=
  (ZeroAtInftyContinuousMap.compLinearMap e.toCocompactMap).mkContinuous 1 (fun f => by
    simp only [one_mul]
    apply (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr
    intro k
    exact f.toBCF.norm_coe_le_norm (e k))

def cZeroHomeomorphEquiv (e : K ≃ₜ L) : C₀(L, 𝕜) ≃L[𝕜] C₀(K, 𝕜) :=
  ContinuousLinearEquiv.equivOfInverse (cZeroHomeomorphPull e) (cZeroHomeomorphPull e.symm)
    (fun f => by ext x; exact congrArg f (e.apply_symm_apply x))
    (fun f => by ext x; exact congrArg f (e.symm_apply_apply x))

@[simp] theorem cZeroHomeomorphEquiv_apply (e : K ≃ₜ L) (f : C₀(L, 𝕜)) (x : K) :
    cZeroHomeomorphEquiv e f x = f (e x) := rfl

def cZeroHomeomorphIsometryEquiv (e : K ≃ₜ L) : C₀(L, 𝕜) ≃ₗᵢ[𝕜] C₀(K, 𝕜) where
  __ := (cZeroHomeomorphEquiv e).toLinearEquiv
  norm_map' f := by
    apply le_antisymm
    · exact (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr
        (fun k => f.toBCF.norm_coe_le_norm (e k))
    · apply (BoundedContinuousFunction.norm_le (norm_nonneg (cZeroHomeomorphEquiv e f))).mpr
      intro l
      simpa using (cZeroHomeomorphEquiv e f).toBCF.norm_coe_le_norm (e.symm l)

end ThesisCommon

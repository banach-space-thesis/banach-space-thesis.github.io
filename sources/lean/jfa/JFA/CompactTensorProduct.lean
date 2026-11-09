import JFA.ContinuousTensorDensity
import Mathlib.Topology.ContinuousMap.Compact

noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

namespace JFA

variable {𝕜 K L : Type*} [RCLike 𝕜]
  [TopologicalSpace K] [CompactSpace K] [T2Space K]
  [TopologicalSpace L] [CompactSpace L] [T2Space L]

private def compactUncurry : C(K, C(L, 𝕜)) ≃ₗᵢ[𝕜] C(K × L, 𝕜) where
  toFun := ContinuousMap.uncurry
  invFun := ContinuousMap.curry
  left_inv f := by ext k l; rfl
  right_inv f := by ext p; rfl
  map_add' f g := by ext p; rfl
  map_smul' a f := by ext p; rfl
  norm_map' f := by
    apply le_antisymm
    · exact (ContinuousMap.norm_le _ (norm_nonneg f)).mpr fun p =>
        ((f p.1).norm_coe_le_norm p.2).trans (f.norm_coe_le_norm p.1)
    · refine (ContinuousMap.norm_le _ (norm_nonneg (ContinuousMap.uncurry f))).mpr fun k => ?_
      exact (ContinuousMap.norm_le _ (norm_nonneg (ContinuousMap.uncurry f))).mpr fun l =>
        (ContinuousMap.uncurry f).norm_coe_le_norm (k, l)

/-- The compact product-space identification in Proposition 2.2. -/
def compactTensorProductEquiv : InjectiveTensor 𝕜 C(K, 𝕜) C(L, 𝕜) ≃ₗᵢ[𝕜] C(K × L, 𝕜) :=
  (tensorContinuousEquiv (𝕜 := 𝕜) (M := K) (X := C(L, 𝕜))).trans compactUncurry

theorem compactTensorProductEquiv_pure (f : C(K, 𝕜)) (g : C(L, 𝕜)) (p : K × L) :
    compactTensorProductEquiv (𝕜 := 𝕜) (K := K) (L := L)
      (injectivePure 𝕜 C(K, 𝕜) C(L, 𝕜) f g) p = f p.1 * g p.2 := by
  change tensorContinuousFunction (injectivePure 𝕜 C(K, 𝕜) C(L, 𝕜) f g) p.1 p.2 = _
  rw [tensorContinuousFunction_pure]
  rfl

end JFA

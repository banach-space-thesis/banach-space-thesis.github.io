import JLMS.CZeroTools
import JLMS.OrdinalScattered

/-!
# Isometric identification of C(K) and C₀(K) for compact K

This identifies the function spaces in Section 9 with the scattered-space
function spaces used in Sections 4–8, including arbitrary ordinal intervals.
-/

noncomputable section
namespace JLMS
variable {𝕜 : Type*} [RCLike 𝕜]
variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

def compactContinuousCZeroEquiv : C(K, 𝕜) ≃ₗᵢ[𝕜] CZero 𝕜 K where
  toEquiv := ZeroAtInftyContinuousMap.ContinuousMap.liftZeroAtInfty
  map_add' f g := by ext x; rfl
  map_smul' c f := by ext x; rfl
  norm_map' f := by
    let g : CZero 𝕜 K := ZeroAtInftyContinuousMap.ContinuousMap.liftZeroAtInfty f
    change ‖g‖ = ‖f‖
    apply le_antisymm
    · apply (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr
      intro x
      change ‖f x‖ ≤ ‖f‖
      exact f.norm_coe_le_norm x
    · apply (ContinuousMap.norm_le f (norm_nonneg g)).mpr
      intro x
      exact norm_CZero_apply_le g x

@[simp] theorem compactContinuousCZeroEquiv_apply (f : C(K, 𝕜)) (x : K) :
    compactContinuousCZeroEquiv (𝕜 := 𝕜) f x = f x := rfl

def ordinalContinuousCZeroEquiv (α : Ordinal) :
    OrdinalC 𝕜 α ≃ₗᵢ[𝕜] CZero 𝕜 (OrdinalInterval α) := compactContinuousCZeroEquiv

end JLMS

import Posets.ScalarMatrixRows

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
open ThesisCommon
open scoped ZeroAtInfty
namespace Posets
variable (𝕜 : Type) [RCLike 𝕜] (P : Type) [Fintype P]

def finiteCZeroEquiv : CZeroOn 𝕜 P ≃ₗᵢ[𝕜] (P → 𝕜) where
  toFun f p := f ⟨p⟩
  invFun x := ∑ p, x p • unitVector 𝕜 p
  left_inv f := by
    ext p
    rw [czero_finset_sum_apply]
    simp [unitVector_apply]
  right_inv x := by
    funext p
    dsimp only
    rw [czero_finset_sum_apply]
    simp [unitVector_apply]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' f := by
    apply le_antisymm
    · exact (pi_norm_le_iff_of_nonneg (norm_nonneg f)).mpr
        (fun p => f.toBCF.norm_coe_le_norm ⟨p⟩)
    · exact (BoundedContinuousFunction.norm_le (norm_nonneg (fun p : P => f ⟨p⟩))).mpr
        (fun p => norm_le_pi_norm (fun q : P => f ⟨q⟩) p.val)

theorem finiteCZeroEquiv_apply (f : CZeroOn 𝕜 P) (p : P) :
    finiteCZeroEquiv 𝕜 P f p = f ⟨p⟩ := rfl

theorem finiteCZeroEquiv_unitVector (t : P) :
    finiteCZeroEquiv 𝕜 P (unitVector 𝕜 t) = Pi.single t 1 := by
  classical
  funext s
  simp [finiteCZeroEquiv_apply, unitVector_apply, Pi.single_apply]

end Posets

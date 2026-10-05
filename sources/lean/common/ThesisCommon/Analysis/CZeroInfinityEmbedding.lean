import ThesisCommon.Analysis.CZeroSingles

/-! The canonical isometric inclusion of the actual null sequences into
the actual bounded sequences. -/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

def cZeroToInfinityIsometry : CZeroSum 𝕜 →ₗᵢ[𝕜] EllInfinitySum 𝕜 where
  toFun x := ⟨fun n => x n, memℓp_infty ⟨‖x‖, by
    rintro _ ⟨n, rfl⟩
    exact BoundedContinuousFunction.norm_coe_le_norm x.toBCF n⟩⟩
  map_add' := by intro x y; ext n; rfl
  map_smul' := by intro a x; ext n; rfl
  norm_map' x := by
    apply le_antisymm
    · apply lp.norm_le_of_forall_le (norm_nonneg x)
      intro n
      exact BoundedContinuousFunction.norm_coe_le_norm x.toBCF n
    · apply (BoundedContinuousFunction.norm_le (norm_nonneg _)).2
      intro n
      let z : EllInfinitySum 𝕜 := ⟨fun j => x j, memℓp_infty ⟨‖x‖, by
        rintro _ ⟨j, rfl⟩
        exact BoundedContinuousFunction.norm_coe_le_norm x.toBCF j⟩⟩
      exact lp.norm_apply_le_norm ENNReal.top_ne_zero z n

@[simp] theorem cZeroToInfinityIsometry_apply (x : CZeroSum 𝕜) (n : ℕ) :
    cZeroToInfinityIsometry (𝕜 := 𝕜) x n = x n := rfl

theorem cZeroToInfinityIsometry_single (n : ℕ) :
    cZeroToInfinityIsometry (𝕜 := 𝕜) (cZeroSingle n 1) = lp.single ∞ n (1 : 𝕜) := by
  ext i
  simp [cZeroSingle_apply, lp.single_apply, Pi.single_apply]

end ThesisCommon

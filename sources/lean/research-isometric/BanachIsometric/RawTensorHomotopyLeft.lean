import BanachIsometric.RawTensorHomotopyMaps

/-! The left factor homotopy has its actual tensor boundary identity;
the cross term with the right differential cancels by the Koszul sign. -/

noncomputable section
namespace BanachIsometric.SingularAW
open SingularPrism
open scoped TensorProduct DirectSum

variable (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y]

theorem rawTensorLeftBoundary_leftHomotopy_identity :
    (rawTensorLeftBoundary X Y).comp (rawTensorLeftHomotopy X Y) +
      (rawTensorLeftHomotopy X Y).comp (rawTensorLeftBoundary X Y) + rawTensorLeftProjector X Y =
        (LinearMap.id : RawBigradedTensorChains X Y →ₗ[ℚ] RawBigradedTensorChains X Y) := by
  apply DirectSum.linearMap_ext
  rintro ⟨p, q⟩
  apply TensorProduct.ext
  apply LinearMap.ext
  intro c
  apply LinearMap.ext
  intro d
  change rawTensorLeftBoundary X Y
      (rawTensorLeftHomotopy X Y (rawTensorInclusion X Y p q (c ⊗ₜ[ℚ] d))) +
    rawTensorLeftHomotopy X Y
      (rawTensorLeftBoundary X Y (rawTensorInclusion X Y p q (c ⊗ₜ[ℚ] d))) +
      rawTensorLeftProjector X Y (rawTensorInclusion X Y p q (c ⊗ₜ[ℚ] d)) =
        rawTensorInclusion X Y p q (c ⊗ₜ[ℚ] d)
  rw [rawTensorLeftHomotopy_tmul, rawTensorLeftBoundary_tmul, rawTensorLeftProjector_tmul]
  cases p with
  | zero =>
      have hz : rawTensorLeftBoundary X Y (rawTensorInclusion X Y 0 q (c ⊗ₜ[ℚ] d)) = 0 := by
        simp only [rawTensorLeftBoundary_inclusion, rawTensorLeftComponent, LinearMap.zero_apply]
      rw [hz, map_zero, add_zero, rawFactorContraction_zero_identity,
        ← map_add, ← TensorProduct.add_tmul, sub_add_cancel]
  | succ p =>
      rw [rawTensorLeftBoundary_tmul, rawTensorLeftHomotopy_tmul, ← map_add,
        ← TensorProduct.add_tmul, rawFactorContraction_succ_identity,
        ← map_add, ← TensorProduct.add_tmul, sub_add_cancel]

theorem rawTensorRightBoundary_leftHomotopy_anticommute :
    (rawTensorRightBoundary X Y).comp (rawTensorLeftHomotopy X Y) +
      (rawTensorLeftHomotopy X Y).comp (rawTensorRightBoundary X Y) = 0 := by
  apply DirectSum.linearMap_ext
  rintro ⟨p, q⟩
  apply TensorProduct.ext
  apply LinearMap.ext
  intro c
  apply LinearMap.ext
  intro d
  change rawTensorRightBoundary X Y
      (rawTensorLeftHomotopy X Y (rawTensorInclusion X Y p q (c ⊗ₜ[ℚ] d))) +
    rawTensorLeftHomotopy X Y
      (rawTensorRightBoundary X Y (rawTensorInclusion X Y p q (c ⊗ₜ[ℚ] d))) = 0
  cases q with
  | zero => simp [rawTensorRightBoundary_inclusion, rawTensorRightComponent]
  | succ q =>
      rw [rawTensorLeftHomotopy_tmul, rawTensorRightBoundary_tmul,
        rawTensorRightBoundary_tmul, map_smul, rawTensorLeftHomotopy_tmul, ← add_smul]
      have hs : (-1 : ℚ) ^ (p + 1) + (-1 : ℚ) ^ p = 0 := by
        rw [pow_succ, mul_neg_one, neg_add_cancel]
      rw [hs, zero_smul]

end BanachIsometric.SingularAW

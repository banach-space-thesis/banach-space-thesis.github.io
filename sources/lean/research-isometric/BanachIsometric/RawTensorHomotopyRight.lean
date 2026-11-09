import BanachIsometric.RawTensorHomotopyMaps

/-! The projected right-factor homotopy has its actual tensor identity.
Its cross term with the left differential vanishes on both sides. -/

noncomputable section
namespace BanachIsometric.SingularAW
open SingularPrism
open scoped TensorProduct DirectSum

variable (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y]

theorem rawTensorLeftBoundary_rightHomotopy_anticommute :
    (rawTensorLeftBoundary X Y).comp (rawTensorRightHomotopy X Y) +
      (rawTensorRightHomotopy X Y).comp (rawTensorLeftBoundary X Y) = 0 := by
  apply DirectSum.linearMap_ext
  rintro ⟨p, q⟩
  apply TensorProduct.ext
  apply LinearMap.ext
  intro c
  apply LinearMap.ext
  intro d
  change rawTensorLeftBoundary X Y
      (rawTensorRightHomotopy X Y (rawTensorInclusion X Y p q (c ⊗ₜ[ℚ] d))) +
    rawTensorRightHomotopy X Y
      (rawTensorLeftBoundary X Y (rawTensorInclusion X Y p q (c ⊗ₜ[ℚ] d))) = 0
  cases p with
  | zero => simp [rawTensorLeftBoundary_inclusion, rawTensorLeftComponent]
  | succ p =>
      rw [rawTensorRightHomotopy_tmul, map_smul, rawTensorLeftBoundary_tmul,
        rawTensorLeftBoundary_tmul, rawTensorRightHomotopy_tmul,
        rawBoundary_factorProjector, rawFactorProjector_boundary,
        TensorProduct.zero_tmul, map_zero, smul_zero, smul_zero, add_zero]

theorem rawTensorRightBoundary_rightHomotopy_identity :
    (rawTensorRightBoundary X Y).comp (rawTensorRightHomotopy X Y) +
      (rawTensorRightHomotopy X Y).comp (rawTensorRightBoundary X Y) +
        rawTensorBothProjector X Y = rawTensorLeftProjector X Y := by
  apply DirectSum.linearMap_ext
  rintro ⟨p, q⟩
  apply TensorProduct.ext
  apply LinearMap.ext
  intro c
  apply LinearMap.ext
  intro d
  change rawTensorRightBoundary X Y
      (rawTensorRightHomotopy X Y (rawTensorInclusion X Y p q (c ⊗ₜ[ℚ] d))) +
    rawTensorRightHomotopy X Y
      (rawTensorRightBoundary X Y (rawTensorInclusion X Y p q (c ⊗ₜ[ℚ] d))) +
      rawTensorBothProjector X Y (rawTensorInclusion X Y p q (c ⊗ₜ[ℚ] d)) =
        rawTensorLeftProjector X Y (rawTensorInclusion X Y p q (c ⊗ₜ[ℚ] d))
  have hs : (-1 : ℚ) ^ p * (-1 : ℚ) ^ p = 1 := by
    rw [← mul_pow]
    norm_num
  rw [rawTensorLeftProjector_tmul, rawTensorBothProjector_tmul]
  cases q with
  | zero =>
      have hz : rawTensorRightBoundary X Y (rawTensorInclusion X Y p 0 (c ⊗ₜ[ℚ] d)) = 0 := by
        simp only [rawTensorRightBoundary_inclusion, rawTensorRightComponent, LinearMap.zero_apply]
      rw [rawTensorRightHomotopy_tmul, map_smul, rawTensorRightBoundary_tmul,
        smul_smul, hs, one_smul, hz, map_zero, add_zero,
        rawFactorContraction_zero_identity, ← map_add, ← TensorProduct.tmul_add, sub_add_cancel]
  | succ q =>
      rw [rawTensorRightHomotopy_tmul, map_smul, rawTensorRightBoundary_tmul,
        rawTensorRightBoundary_tmul, map_smul, rawTensorRightHomotopy_tmul,
        smul_smul, hs, one_smul, smul_smul, hs, one_smul, ← map_add,
        ← TensorProduct.tmul_add, rawFactorContraction_succ_identity,
        ← map_add, ← TensorProduct.tmul_add, sub_add_cancel]

end BanachIsometric.SingularAW

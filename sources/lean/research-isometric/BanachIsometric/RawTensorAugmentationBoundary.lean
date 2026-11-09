import BanachIsometric.RawTensorAugmentation
import BanachIsometric.RawTensorTotalDegree

/-! The actual product augmentation annihilates the actual signed tensor
boundary. Both degree-one factor contributions are checked explicitly. -/

noncomputable section
namespace BanachIsometric.SingularAW
open SingularPrism
open scoped TensorProduct

variable (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y]

theorem rawTensorZeroAugmentation_leftBoundary :
    (rawTensorZeroAugmentation X Y).comp
      (TensorProduct.map (rawBoundary (X := X) 0)
        (LinearMap.id : RawRationalChains Y 0 →ₗ[ℚ] RawRationalChains Y 0)) = 0 := by
  apply TensorProduct.ext
  apply LinearMap.ext
  intro c
  apply LinearMap.ext
  intro d
  change rawTensorZeroAugmentation X Y
    (TensorProduct.map (rawBoundary (X := X) 0) LinearMap.id (c ⊗ₜ[ℚ] d)) = 0
  rw [TensorProduct.map_tmul, LinearMap.id_apply, rawTensorZeroAugmentation_tmul]
  have h := LinearMap.congr_fun (rawAugmentation_boundary X) c
  change rawAugmentation X (rawBoundary 0 c) = 0 at h
  rw [h, zero_mul]

theorem rawTensorZeroAugmentation_rightBoundary :
    (rawTensorZeroAugmentation X Y).comp
      (TensorProduct.map (LinearMap.id : RawRationalChains X 0 →ₗ[ℚ] RawRationalChains X 0)
        (rawBoundary (X := Y) 0)) = 0 := by
  apply TensorProduct.ext
  apply LinearMap.ext
  intro c
  apply LinearMap.ext
  intro d
  change rawTensorZeroAugmentation X Y
    (TensorProduct.map LinearMap.id (rawBoundary (X := Y) 0) (c ⊗ₜ[ℚ] d)) = 0
  rw [TensorProduct.map_tmul, LinearMap.id_apply, rawTensorZeroAugmentation_tmul]
  have h := LinearMap.congr_fun (rawAugmentation_boundary Y) d
  change rawAugmentation Y (rawBoundary 0 d) = 0 at h
  rw [h, mul_zero]

theorem rawTensorAugmentation_boundary :
    (rawTensorAugmentation X Y).comp (rawTensorTotalBoundary X Y) = 0 := by
  apply LinearMap.ext
  intro c
  change rawTensorZeroAugmentation X Y
    (rawTensorComponent X Y 0 0 (rawTensorTotalBoundary X Y c)) = 0
  rw [rawTensorComponent_totalBoundary, pow_zero, one_smul, map_add]
  have hL := LinearMap.congr_fun (rawTensorZeroAugmentation_leftBoundary X Y)
    (rawTensorComponent X Y 1 0 c)
  have hR := LinearMap.congr_fun (rawTensorZeroAugmentation_rightBoundary X Y)
    (rawTensorComponent X Y 0 1 c)
  change rawTensorZeroAugmentation X Y
    (TensorProduct.map (rawBoundary (X := X) 0) LinearMap.id (rawTensorComponent X Y 1 0 c)) = 0 at hL
  change rawTensorZeroAugmentation X Y
    (TensorProduct.map LinearMap.id (rawBoundary (X := Y) 0) (rawTensorComponent X Y 0 1 c)) = 0 at hR
  rw [hL, hR, add_zero]

end BanachIsometric.SingularAW

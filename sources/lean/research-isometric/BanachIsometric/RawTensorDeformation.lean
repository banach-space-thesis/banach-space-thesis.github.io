import BanachIsometric.RawTensorHomotopyLeft
import BanachIsometric.RawTensorHomotopyRight
import Mathlib.Tactic.Abel

/-! The actual signed raw tensor homotopy satisfies d h + h d + P = id,
where P is the tensor of the actual factor homology projectors. -/

noncomputable section
namespace BanachIsometric.SingularAW
open SingularPrism
open scoped TensorProduct DirectSum

variable (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y]

theorem rawTensorTotalHomotopy_identity :
    (rawTensorTotalBoundary X Y).comp (rawTensorTotalHomotopy X Y) +
      (rawTensorTotalHomotopy X Y).comp (rawTensorTotalBoundary X Y) + rawTensorBothProjector X Y =
        (LinearMap.id : RawBigradedTensorChains X Y →ₗ[ℚ] RawBigradedTensorChains X Y) := by
  apply LinearMap.ext
  intro z
  have hA := LinearMap.congr_fun (rawTensorLeftBoundary_leftHomotopy_identity X Y) z
  have hB := LinearMap.congr_fun (rawTensorRightBoundary_leftHomotopy_anticommute X Y) z
  have hC := LinearMap.congr_fun (rawTensorLeftBoundary_rightHomotopy_anticommute X Y) z
  have hD := LinearMap.congr_fun (rawTensorRightBoundary_rightHomotopy_identity X Y) z
  change rawTensorLeftBoundary X Y (rawTensorLeftHomotopy X Y z) +
    rawTensorLeftHomotopy X Y (rawTensorLeftBoundary X Y z) + rawTensorLeftProjector X Y z = z at hA
  change rawTensorRightBoundary X Y (rawTensorLeftHomotopy X Y z) +
    rawTensorLeftHomotopy X Y (rawTensorRightBoundary X Y z) = 0 at hB
  change rawTensorLeftBoundary X Y (rawTensorRightHomotopy X Y z) +
    rawTensorRightHomotopy X Y (rawTensorLeftBoundary X Y z) = 0 at hC
  change rawTensorRightBoundary X Y (rawTensorRightHomotopy X Y z) +
    rawTensorRightHomotopy X Y (rawTensorRightBoundary X Y z) + rawTensorBothProjector X Y z =
      rawTensorLeftProjector X Y z at hD
  change (rawTensorLeftBoundary X Y + rawTensorRightBoundary X Y)
      ((rawTensorLeftHomotopy X Y + rawTensorRightHomotopy X Y) z) +
    (rawTensorLeftHomotopy X Y + rawTensorRightHomotopy X Y)
      ((rawTensorLeftBoundary X Y + rawTensorRightBoundary X Y) z) +
      rawTensorBothProjector X Y z = z
  simp only [LinearMap.add_apply, map_add]
  calc
    _ = (rawTensorLeftBoundary X Y (rawTensorLeftHomotopy X Y z) +
          rawTensorLeftHomotopy X Y (rawTensorLeftBoundary X Y z)) +
        (rawTensorRightBoundary X Y (rawTensorLeftHomotopy X Y z) +
          rawTensorLeftHomotopy X Y (rawTensorRightBoundary X Y z)) +
        (rawTensorLeftBoundary X Y (rawTensorRightHomotopy X Y z) +
          rawTensorRightHomotopy X Y (rawTensorLeftBoundary X Y z)) +
        (rawTensorRightBoundary X Y (rawTensorRightHomotopy X Y z) +
          rawTensorRightHomotopy X Y (rawTensorRightBoundary X Y z) + rawTensorBothProjector X Y z) := by abel
    _ = (rawTensorLeftBoundary X Y (rawTensorLeftHomotopy X Y z) +
          rawTensorLeftHomotopy X Y (rawTensorLeftBoundary X Y z)) + 0 + 0 +
        rawTensorLeftProjector X Y z := by rw [hB, hC, hD]
    _ = z := by simpa only [add_zero] using hA

theorem rawTensorBoundary_totalHomotopy_of_cycle
    {z : RawBigradedTensorChains X Y} (hz : rawTensorTotalBoundary X Y z = 0) :
    rawTensorTotalBoundary X Y (rawTensorTotalHomotopy X Y z) + rawTensorBothProjector X Y z = z := by
  have h := LinearMap.congr_fun (rawTensorTotalHomotopy_identity X Y) z
  change rawTensorTotalBoundary X Y (rawTensorTotalHomotopy X Y z) +
    rawTensorTotalHomotopy X Y (rawTensorTotalBoundary X Y z) + rawTensorBothProjector X Y z = z at h
  rwa [hz, map_zero, add_zero] at h

end BanachIsometric.SingularAW

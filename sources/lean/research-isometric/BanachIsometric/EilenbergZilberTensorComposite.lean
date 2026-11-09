import BanachIsometric.EilenbergZilberSymmetric
import BanachIsometric.AlexanderWhitneyAugmentation
import BanachIsometric.AlexanderWhitneyHomogeneousChainMap
import BanachIsometric.RawTensorFunctoriality

/-! Alexander--Whitney after the actual crossproduct is a natural,
augmentation-preserving endomorphism of the actual homogeneous tensor complex. -/

noncomputable section
namespace BanachIsometric.SingularEZ

open SingularPrism SingularAW

variable {X Y X' Y' : Type*}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace X'] [TopologicalSpace Y']

def rawTensorComposite (n : ℕ) :
    rawTensorTotalDegree X Y n →ₗ[ℚ] rawTensorTotalDegree X Y n :=
  (rawAlexanderWhitneyHomogeneous X Y n).comp (rawSymmetricEilenbergZilber n)

theorem rawTensorComposite_boundary (n : ℕ) (c : rawTensorTotalDegree X Y (n + 1)) :
    rawTensorBoundary X Y n (rawTensorComposite (n + 1) c) =
      rawTensorComposite n (rawTensorBoundary X Y n c) := by
  simp only [rawTensorComposite, LinearMap.comp_apply]
  rw [show rawTensorBoundary X Y n (rawAlexanderWhitneyHomogeneous X Y (n + 1)
      (rawSymmetricEilenbergZilber (n + 1) c)) =
    rawAlexanderWhitneyHomogeneous X Y n (rawBoundary n (rawSymmetricEilenbergZilber (n + 1) c)) from
      LinearMap.congr_fun (rawAlexanderWhitneyHomogeneous_boundary n) _]
  rw [show rawBoundary n (rawSymmetricEilenbergZilber (n + 1) c) =
    rawSymmetricEilenbergZilber n (rawTensorBoundary X Y n c) from
      LinearMap.congr_fun (rawSymmetricEilenbergZilber_boundary n) c]

theorem rawTensorComposite_naturality (f : C(X, X')) (g : C(Y, Y')) (n : ℕ)
    (c : rawTensorTotalDegree X Y n) :
    rawTensorComposite n (rawBigradedTensorMapHomogeneous f g n c) =
      rawBigradedTensorMapHomogeneous f g n (rawTensorComposite n c) := by
  apply Subtype.ext
  change rawAlexanderWhitney n (rawSymmetricEilenbergZilber n (rawBigradedTensorMapHomogeneous f g n c)) =
    rawBigradedTensorMap f g (rawAlexanderWhitney n (rawSymmetricEilenbergZilber n c))
  rw [show rawSymmetricEilenbergZilber n (rawBigradedTensorMapHomogeneous f g n c) =
    rawChainMap (awProductMap f g) n (rawSymmetricEilenbergZilber n c) from
      LinearMap.congr_fun (rawSymmetricEilenbergZilber_naturality f g n) c]
  exact (LinearMap.congr_fun (rawAlexanderWhitney_naturality f g n) _).symm

theorem rawTensorComposite_augmentation (c : rawTensorTotalDegree X Y 0) :
    rawTensorAugmentation X Y (rawTensorComposite 0 c).val = rawTensorAugmentation X Y c.val := by
  change rawTensorAugmentation X Y (rawAlexanderWhitney 0 (rawSymmetricEilenbergZilberTotal 0 c.val)) = _
  rw [show rawTensorAugmentation X Y (rawAlexanderWhitney 0 (rawSymmetricEilenbergZilberTotal 0 c.val)) =
    rawAugmentation (X × Y) (rawSymmetricEilenbergZilberTotal 0 c.val) from
      LinearMap.congr_fun rawAlexanderWhitney_augmentation _]
  exact LinearMap.congr_fun rawSymmetricEilenbergZilberTotal_augmentation c.val

end BanachIsometric.SingularEZ

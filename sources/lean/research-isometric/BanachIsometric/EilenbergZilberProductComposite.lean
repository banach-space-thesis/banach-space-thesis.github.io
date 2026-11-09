import BanachIsometric.EilenbergZilberSymmetric
import BanachIsometric.AlexanderWhitneyAugmentation

/-! The actual crossproduct after Alexander--Whitney is a natural,
augmentation-preserving endomorphism of product singular chains. -/

noncomputable section
namespace BanachIsometric.SingularEZ

open SingularPrism SingularAW

variable {X Y X' Y' : Type*}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace X'] [TopologicalSpace Y']

def rawProductComposite (n : ℕ) :
    RawRationalChains (X × Y) n →ₗ[ℚ] RawRationalChains (X × Y) n :=
  (rawSymmetricEilenbergZilberTotal n).comp (rawAlexanderWhitney n)

theorem rawProductComposite_boundary (n : ℕ) (c : RawRationalChains (X × Y) (n + 1)) :
    rawBoundary n (rawProductComposite (n + 1) c) = rawProductComposite n (rawBoundary n c) := by
  simp only [rawProductComposite, LinearMap.comp_apply]
  rw [show rawBoundary n (rawSymmetricEilenbergZilberTotal (n + 1) (rawAlexanderWhitney (n + 1) c)) =
    rawSymmetricEilenbergZilberTotal n (rawTensorTotalBoundary X Y (rawAlexanderWhitney (n + 1) c)) from
      LinearMap.congr_fun (rawSymmetricEilenbergZilberTotal_boundary n) _]
  rw [show rawTensorTotalBoundary X Y (rawAlexanderWhitney (n + 1) c) =
    rawAlexanderWhitney n (rawBoundary n c) from LinearMap.congr_fun (rawAlexanderWhitney_boundary n) c]

theorem rawProductComposite_naturality (f : C(X, X')) (g : C(Y, Y')) (n : ℕ)
    (c : RawRationalChains (X × Y) n) :
    rawProductComposite n (rawChainMap (awProductMap f g) n c) =
      rawChainMap (awProductMap f g) n (rawProductComposite n c) := by
  simp only [rawProductComposite, LinearMap.comp_apply]
  rw [← show rawBigradedTensorMap f g (rawAlexanderWhitney n c) =
    rawAlexanderWhitney n (rawChainMap (awProductMap f g) n c) from
      LinearMap.congr_fun (rawAlexanderWhitney_naturality f g n) c]
  exact LinearMap.congr_fun (rawSymmetricEilenbergZilberTotal_naturality f g n) _

theorem rawProductComposite_augmentation (c : RawRationalChains (X × Y) 0) :
    rawAugmentation (X × Y) (rawProductComposite 0 c) = rawAugmentation (X × Y) c := by
  change rawAugmentation (X × Y) (rawSymmetricEilenbergZilberTotal 0 (rawAlexanderWhitney 0 c)) = _
  rw [show rawAugmentation (X × Y) (rawSymmetricEilenbergZilberTotal 0 (rawAlexanderWhitney 0 c)) =
    rawTensorAugmentation X Y (rawAlexanderWhitney 0 c) from
      LinearMap.congr_fun rawSymmetricEilenbergZilberTotal_augmentation _]
  exact LinearMap.congr_fun rawAlexanderWhitney_augmentation c

end BanachIsometric.SingularEZ

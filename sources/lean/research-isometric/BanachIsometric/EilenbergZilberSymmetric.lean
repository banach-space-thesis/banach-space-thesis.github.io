import BanachIsometric.EilenbergZilberCrossproduct
import BanachIsometric.RawTensorSwapNaturality
import Mathlib.Tactic.NormNum

/-! Averaging the chosen crossproduct with its transported signed flip
gives a natural chain crossproduct with a strict graded symmetry identity.
The averaging takes place over the original rational coefficient field. -/

noncomputable section
namespace BanachIsometric.SingularEZ

open SingularPrism SingularAW

variable {X Y X' Y' : Type*}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace X'] [TopologicalSpace Y']

def rawFlippedEilenbergZilberTotal (n : ℕ) :
    RawBigradedTensorChains X Y →ₗ[ℚ] RawRationalChains (X × Y) n :=
  (rawChainMap (awProductSwap Y X) n).comp ((rawEilenbergZilberTotal n).comp (rawTensorSwap X Y))

def rawSymmetricEilenbergZilberTotal (n : ℕ) :
    RawBigradedTensorChains X Y →ₗ[ℚ] RawRationalChains (X × Y) n :=
  (1 / 2 : ℚ) • (rawEilenbergZilberTotal n + rawFlippedEilenbergZilberTotal n)

theorem rawSymmetricEilenbergZilberTotal_boundary (n : ℕ) :
    (rawBoundary (X := X × Y) n).comp (rawSymmetricEilenbergZilberTotal (n + 1)) =
      (rawSymmetricEilenbergZilberTotal n).comp (rawTensorTotalBoundary X Y) := by
  apply LinearMap.ext
  intro c
  have hd := LinearMap.congr_fun (rawEilenbergZilberTotal_boundary (X := X) (Y := Y) n) c
  have hd' := LinearMap.congr_fun (rawEilenbergZilberTotal_boundary (X := Y) (Y := X) n)
    (rawTensorSwap X Y c)
  have hf := LinearMap.congr_fun (rawChainMap_boundary (awProductSwap Y X) n)
    (rawEilenbergZilberTotal (n + 1) (rawTensorSwap X Y c))
  simp only [LinearMap.comp_apply] at hd hd' hf
  simp only [rawSymmetricEilenbergZilberTotal, rawFlippedEilenbergZilberTotal, LinearMap.comp_apply,
    LinearMap.add_apply, LinearMap.smul_apply, map_smul, map_add, hd, hd', hf, rawTensorSwap_boundary]

theorem rawSymmetricEilenbergZilberTotal_naturality (f : C(X, X')) (g : C(Y, Y')) (n : ℕ) :
    (rawSymmetricEilenbergZilberTotal (X := X') (Y := Y') n).comp (rawBigradedTensorMap f g) =
      (rawChainMap (awProductMap f g) n).comp (rawSymmetricEilenbergZilberTotal n) := by
  apply LinearMap.ext
  intro c
  have h := LinearMap.congr_fun (rawEilenbergZilberTotal_naturality f g n) c
  have h' := LinearMap.congr_fun (rawEilenbergZilberTotal_naturality g f n) (rawTensorSwap X Y c)
  have hf := LinearMap.congr_fun (rawChainMap_comp (awProductMap g f) (awProductSwap Y' X') n)
    (rawEilenbergZilberTotal n (rawTensorSwap X Y c))
  have hf' := LinearMap.congr_fun (rawChainMap_comp (awProductSwap Y X) (awProductMap f g) n)
    (rawEilenbergZilberTotal n (rawTensorSwap X Y c))
  rw [awProductMap_comp_awProductSwap] at hf'
  simp only [LinearMap.comp_apply] at h h' hf hf'
  simp only [rawSymmetricEilenbergZilberTotal, rawFlippedEilenbergZilberTotal, LinearMap.comp_apply,
    LinearMap.add_apply, LinearMap.smul_apply, map_smul, map_add, h, rawTensorSwap_naturality,
    h', ← hf, hf']

theorem rawSymmetricEilenbergZilberTotal_augmentation :
    (rawAugmentation (X × Y)).comp (rawSymmetricEilenbergZilberTotal 0) = rawTensorAugmentation X Y := by
  apply LinearMap.ext
  intro c
  have h := LinearMap.congr_fun (rawEilenbergZilberTotal_augmentation (X := X) (Y := Y)) c
  have h' := LinearMap.congr_fun (rawEilenbergZilberTotal_augmentation (X := Y) (Y := X)) (rawTensorSwap X Y c)
  have hf := LinearMap.congr_fun (rawAugmentation_natural (awProductSwap Y X))
    (rawEilenbergZilberTotal 0 (rawTensorSwap X Y c))
  simp only [LinearMap.comp_apply] at h h' hf
  simp only [rawSymmetricEilenbergZilberTotal, rawFlippedEilenbergZilberTotal, LinearMap.comp_apply,
    LinearMap.add_apply, LinearMap.smul_apply, map_smul, map_add, h, hf, h', rawTensorSwap_augmentation]
  change (1 / 2 : ℚ) * (rawTensorAugmentation X Y c + rawTensorAugmentation X Y c) = _
  rw [mul_add, ← add_mul]
  norm_num

theorem rawSymmetricEilenbergZilberTotal_swap (n : ℕ) (c : RawBigradedTensorChains X Y) :
    rawChainMap (awProductSwap X Y) n (rawSymmetricEilenbergZilberTotal n c) =
      rawSymmetricEilenbergZilberTotal n (rawTensorSwap X Y c) := by
  simp only [rawSymmetricEilenbergZilberTotal, rawFlippedEilenbergZilberTotal, LinearMap.comp_apply,
    LinearMap.add_apply, LinearMap.smul_apply, map_smul, map_add, rawTensorSwap_involutive,
    rawChainMap_awProductSwap_involutive, add_comm]

def rawSymmetricEilenbergZilber (n : ℕ) :
    rawTensorTotalDegree X Y n →ₗ[ℚ] RawRationalChains (X × Y) n :=
  (rawSymmetricEilenbergZilberTotal n).comp (rawTensorTotalDegree X Y n).subtype

theorem rawSymmetricEilenbergZilber_boundary (n : ℕ) :
    (rawBoundary (X := X × Y) n).comp (rawSymmetricEilenbergZilber (n + 1)) =
      (rawSymmetricEilenbergZilber n).comp (rawTensorBoundary X Y n) := by
  apply LinearMap.ext
  intro c
  exact LinearMap.congr_fun (rawSymmetricEilenbergZilberTotal_boundary n) c.val

theorem rawSymmetricEilenbergZilber_naturality (f : C(X, X')) (g : C(Y, Y')) (n : ℕ) :
    (rawSymmetricEilenbergZilber (X := X') (Y := Y') n).comp (rawBigradedTensorMapHomogeneous f g n) =
      (rawChainMap (awProductMap f g) n).comp (rawSymmetricEilenbergZilber n) := by
  apply LinearMap.ext
  intro c
  exact LinearMap.congr_fun (rawSymmetricEilenbergZilberTotal_naturality f g n) c.val

end BanachIsometric.SingularEZ

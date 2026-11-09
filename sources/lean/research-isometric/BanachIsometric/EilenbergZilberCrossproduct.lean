import BanachIsometric.EilenbergZilberRecursiveModels

/-! The natural chain cross product on actual unnormalized rational singular
chains, constructed by filling in products of standard simplices. -/

noncomputable section
namespace BanachIsometric.SingularEZ

open SingularPrism SingularAW
open scoped TensorProduct

variable {X Y X' Y' : Type*}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace X'] [TopologicalSpace Y']

def rawEilenbergZilberTotal (n : ℕ) :
    RawBigradedTensorChains X Y →ₗ[ℚ] RawRationalChains (X × Y) n :=
  universalCrossEvaluation (universalProductFamily n)

theorem rawEilenbergZilberTotal_boundary (n : ℕ) :
    (rawBoundary (X := X × Y) n).comp (rawEilenbergZilberTotal (n + 1)) =
      (rawEilenbergZilberTotal n).comp (rawTensorTotalBoundary X Y) :=
  universalCrossEvaluation_boundary_of_compatible (universalProductFamily_compatible n)

theorem rawEilenbergZilberTotal_naturality (f : C(X, X')) (g : C(Y, Y')) (n : ℕ) :
    (rawEilenbergZilberTotal (X := X') (Y := Y') n).comp (rawBigradedTensorMap f g) =
      (rawChainMap (awProductMap f g) n).comp (rawEilenbergZilberTotal n) :=
  universalCrossEvaluation_naturality (universalProductFamily n) f g

theorem rawEilenbergZilberTotal_augmentation :
    (rawAugmentation (X × Y)).comp (rawEilenbergZilberTotal 0) = rawTensorAugmentation X Y :=
  universalProductBase_evaluation_augmentation

def rawEilenbergZilber (n : ℕ) :
    rawTensorTotalDegree X Y n →ₗ[ℚ] RawRationalChains (X × Y) n :=
  (rawEilenbergZilberTotal n).comp (rawTensorTotalDegree X Y n).subtype

theorem rawEilenbergZilber_boundary (n : ℕ) :
    (rawBoundary (X := X × Y) n).comp (rawEilenbergZilber (n + 1)) =
      (rawEilenbergZilber n).comp (rawTensorBoundary X Y n) := by
  apply LinearMap.ext
  intro c
  exact LinearMap.congr_fun (rawEilenbergZilberTotal_boundary n) c.val

theorem rawEilenbergZilber_naturality (f : C(X, X')) (g : C(Y, Y')) (n : ℕ) :
    (rawEilenbergZilber (X := X') (Y := Y') n).comp (rawBigradedTensorMapHomogeneous f g n) =
      (rawChainMap (awProductMap f g) n).comp (rawEilenbergZilber n) := by
  apply LinearMap.ext
  intro c
  exact LinearMap.congr_fun (rawEilenbergZilberTotal_naturality f g n) c.val

theorem rawEilenbergZilberTotal_generator {n p q : ℕ} (h : p + q = n)
    (σ : RawSingularSimplex X p) (τ : RawSingularSimplex Y q) :
    rawEilenbergZilberTotal n
      (rawTensorInclusion X Y p q (Finsupp.single σ 1 ⊗ₜ[ℚ] Finsupp.single τ 1)) =
      rawChainMap (awProductMap σ τ) n (universalProductFamily n p q h) := by
  rw [rawEilenbergZilberTotal, universalCrossEvaluation_inclusion _ h,
    universalCrossBidegree_single]
  simp only [one_smul]

end BanachIsometric.SingularEZ

import BanachIsometric.SingularHomologyCrossproduct
import BanachIsometric.RawFullSingularHomologyMap

/-! The actual homology crossproduct is natural and has the expected
Koszul symmetry under the geometric interchange of the two spaces. -/

noncomputable section
universe u
namespace BanachIsometric.SingularEZ

open SingularPrism SingularAW VectorChainSplitting
open scoped TensorProduct

variable {X Y X' Y' : Type u}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace X'] [TopologicalSpace Y']

abbrev rawHomologyCycleRepresentative (X : Type*) [TopologicalSpace X] (n : ℕ) :
    RawHomology X n →ₗ[ℚ] RawHomologyCycles X n :=
  homologySection (rawFactorObjects X) (rawBoundary (X := X)) (rawBoundary_squared (X := X)) n

theorem rawFactorHomologyProjection_representative (n : ℕ) (a : RawHomology X n) :
    rawFactorHomologyProjection X n (rawHomologyCycleRepresentative X n a).val = a :=
  rawFactorHomologyProjection_inclusion X n a

theorem rawHomologyCross_naturality (f : C(X, X')) (g : C(Y, Y'))
    {n p q : ℕ} (h : p + q = n) (a : RawHomology X p) (b : RawHomology Y q) :
    rawFullHomologyMap (awProductMap f g) n (rawHomologyCross X Y h a b) =
      rawHomologyCross X' Y' h (rawFullHomologyMap f p a) (rawFullHomologyMap g q b) := by
  let c := rawHomologyCycleRepresentative X p a
  let d := rawHomologyCycleRepresentative Y q b
  have hc : rawFactorHomologyProjection X p c.val = a := rawFactorHomologyProjection_representative p a
  have hd : rawFactorHomologyProjection Y q d.val = b := rawFactorHomologyProjection_representative q b
  let w := chainCyclesMap (hd := rawTensorBoundary_squared X Y) (he := rawBoundary_squared (X := X × Y))
    (rawEilenbergZilberChainMap X Y) n (rawTensorPureCycle X Y h c d)
  have hw := rawFullHomologyMap_cycle (awProductMap f g) n w
  change rawFullHomologyMap (awProductMap f g) n
      (rawFactorHomologyProjection (X × Y) n (rawSymmetricEilenbergZilberTotal n
        (rawTensorInclusion X Y p q (c.val ⊗ₜ[ℚ] d.val)))) =
    rawFactorHomologyProjection (X' × Y') n (rawChainMap (awProductMap f g) n
      (rawSymmetricEilenbergZilberTotal n (rawTensorInclusion X Y p q (c.val ⊗ₜ[ℚ] d.val)))) at hw
  rw [← hc, ← hd, rawHomologyCross_cycle X Y h c d, hw,
    rawFullHomologyMap_cycle f p c, rawFullHomologyMap_cycle g q d]
  let c' := rawFullCyclesMap f p c
  let d' := rawFullCyclesMap g q d
  change _ = rawHomologyCross X' Y' h (rawFactorHomologyProjection X' p c'.val)
    (rawFactorHomologyProjection Y' q d'.val)
  rw [rawHomologyCross_cycle X' Y' h c' d']
  apply congrArg (rawFactorHomologyProjection (X' × Y') n)
  have hEZ := LinearMap.congr_fun (rawSymmetricEilenbergZilberTotal_naturality f g n)
    (rawTensorInclusion X Y p q (c.val ⊗ₜ[ℚ] d.val))
  simp only [LinearMap.comp_apply, rawBigradedTensorMap_inclusion, TensorProduct.map_tmul] at hEZ
  exact hEZ.symm

theorem rawHomologyCross_swap {n p q : ℕ} (h : p + q = n) (a : RawHomology X p) (b : RawHomology Y q) :
    rawFullHomologyMap (awProductSwap X Y) n (rawHomologyCross X Y h a b) =
      (-1 : ℚ) ^ (p * q) • rawHomologyCross Y X (by omega : q + p = n) b a := by
  let c := rawHomologyCycleRepresentative X p a
  let d := rawHomologyCycleRepresentative Y q b
  have hc : rawFactorHomologyProjection X p c.val = a := rawFactorHomologyProjection_representative p a
  have hd : rawFactorHomologyProjection Y q d.val = b := rawFactorHomologyProjection_representative q b
  let w := chainCyclesMap (hd := rawTensorBoundary_squared X Y) (he := rawBoundary_squared (X := X × Y))
    (rawEilenbergZilberChainMap X Y) n (rawTensorPureCycle X Y h c d)
  have hw := rawFullHomologyMap_cycle (awProductSwap X Y) n w
  change rawFullHomologyMap (awProductSwap X Y) n
      (rawFactorHomologyProjection (X × Y) n (rawSymmetricEilenbergZilberTotal n
        (rawTensorInclusion X Y p q (c.val ⊗ₜ[ℚ] d.val)))) =
    rawFactorHomologyProjection (Y × X) n (rawChainMap (awProductSwap X Y) n
      (rawSymmetricEilenbergZilberTotal n (rawTensorInclusion X Y p q (c.val ⊗ₜ[ℚ] d.val)))) at hw
  rw [← hc, ← hd, rawHomologyCross_cycle X Y h c d, hw,
    rawHomologyCross_cycle Y X (by omega : q + p = n) d c,
    rawSymmetricEilenbergZilberTotal_swap, rawTensorSwap_tmul, map_smul, map_smul]

end BanachIsometric.SingularEZ

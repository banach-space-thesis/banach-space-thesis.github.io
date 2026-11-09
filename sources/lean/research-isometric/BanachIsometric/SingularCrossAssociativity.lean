import BanachIsometric.SingularCrossTripleComponents
import BanachIsometric.TensorDirectSumComponentExt

/-! The external crossproduct is associative on actual rational
singular homology under the geometric product associator. -/

noncomputable section
universe u
namespace BanachIsometric.SingularEZ

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

open SingularAW
open scoped TensorProduct DirectSum

variable (X Y Z : Type u) [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

theorem rawHomologyCross_associativity {n p q r : ℕ} (h : p + q + r = n)
    (a : RawHomology X p) (b : RawHomology Y q) (c : RawHomology Z r) :
    rawFullHomologyMap awProductAssoc n
        (rawHomologyCross (X × Y) Z h (rawHomologyCross X Y rfl a b) c) =
      rawHomologyCross X (Y × Z) (by omega : p + (q + r) = n) a (rawHomologyCross Y Z rfl b c) := by
  let z := rawHomologyCross (X × Y) Z h (rawHomologyCross X Y rfl a b) c
  let w := rawHomologyCross X (Y × Z) (by omega : p + (q + r) = n) a (rawHomologyCross Y Z rfl b c)
  change rawFullHomologyMap awProductAssoc n z = w
  apply (rawSingularKunnethEquiv X (Y × Z) n).injective
  apply DirectSum.ext_component ℚ
  rintro ⟨⟨i, u₁⟩, hi⟩
  change rawKunnethHomologyComponent X (Y × Z) hi (rawFullHomologyMap awProductAssoc n z) =
    rawKunnethHomologyComponent X (Y × Z) hi w
  apply (TensorProduct.congr (LinearEquiv.refl ℚ (RawHomology X i))
    (rawSingularKunnethEquiv Y Z u₁)).injective
  apply tensorDirectSumRight_ext
  rintro ⟨⟨j, k⟩, hj⟩
  subst u₁
  change TensorProduct.map LinearMap.id (rawHomologyTensorComponent Y Z (rfl : j + k = j + k))
      (TensorProduct.map LinearMap.id (rawSingularKunnethEquiv Y Z (j + k)).toLinearMap
        (rawKunnethHomologyComponent X (Y × Z) hi (rawFullHomologyMap awProductAssoc n z))) =
    TensorProduct.map LinearMap.id (rawHomologyTensorComponent Y Z (rfl : j + k = j + k))
      (TensorProduct.map LinearMap.id (rawSingularKunnethEquiv Y Z (j + k)).toLinearMap
        (rawKunnethHomologyComponent X (Y × Z) hi w))
  simp only [TensorProduct.map_map, LinearMap.id_comp]
  change TensorProduct.map LinearMap.id (rawKunnethHomologyComponent Y Z (rfl : j + k = j + k))
      (rawKunnethHomologyComponent X (Y × Z) hi (rawFullHomologyMap awProductAssoc n z)) =
    TensorProduct.map LinearMap.id (rawKunnethHomologyComponent Y Z (rfl : j + k = j + k))
      (rawKunnethHomologyComponent X (Y × Z) hi w)
  rw [← rawKunnethAssociativity X Y Z (by omega : i + j + k = n) z]
  by_cases he : i = p ∧ j = q ∧ k = r
  · obtain ⟨rfl, rfl, rfl⟩ := he
    simp only [z, w, rawKunnethHomologyComponent_cross, TensorProduct.map_tmul,
      LinearMap.id_apply, TensorProduct.assoc_tmul]
  · rw [rawLeftTripleComponent_cross_of_ne X Y Z h rfl (by omega : i + j + k = n) he a b c,
      rawRightTripleComponent_cross_of_ne X Y Z (by omega : p + (q + r) = n) rfl hi he a b c,
      map_zero]

end BanachIsometric.SingularEZ

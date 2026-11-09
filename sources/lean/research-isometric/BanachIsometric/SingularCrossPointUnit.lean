import BanachIsometric.SingularKunnethFirstProjection
import BanachIsometric.SingularCrossComponents

/-! Crossing with the class of a point is the actual graph pushforward.
This supplies the left and right units for the Pontryagin product. -/

noncomputable section
universe u
namespace BanachIsometric.SingularEZ

set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000

open SingularPrism SingularAW
open scoped TensorProduct

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

def awPointGraphRight (y : Y) : C(X, X × Y) :=
  ⟨fun x => (x, y), continuous_id.prodMk continuous_const⟩

def awPointGraphLeft (x : X) : C(Y, X × Y) :=
  ⟨fun y => (x, y), continuous_const.prodMk continuous_id⟩

theorem rawHomologyCross_point_right (n : ℕ) (a : RawHomology X n) (y : Y) :
    rawHomologyCross X Y (rfl : n + 0 = n) a (rawHomologyPoint Y y) =
      rawFullHomologyMap (awPointGraphRight y) n a := by
  let z := rawHomologyCross X (PUnit : Type u) (rfl : n + 0 = n) a (rawHomologyPoint PUnit PUnit.unit)
  have hf : rawFullHomologyMap (awProductFst X (PUnit : Type u)) n z = a := by
    rw [← rawKunnethFirstProjection_homology X (PUnit : Type u) n z]
    change rawKunnethFirstProjection X (PUnit : Type u) n
      (rawKunnethHomologyComponent X (PUnit : Type u) (rfl : n + 0 = n)
        (rawHomologyCross X (PUnit : Type u) (rfl : n + 0 = n) a (rawHomologyPoint PUnit PUnit.unit))) = a
    rw [rawKunnethHomologyComponent_cross]
    simp only [rawKunnethFirstProjection, LinearMap.comp_apply, TensorProduct.map_tmul,
      LinearMap.id_apply, rawFullZeroAugmentation_point, LinearEquiv.coe_coe, TensorProduct.rid_tmul, one_smul]
  let i : C(X, X × (PUnit : Type u)) := awPointGraphRight PUnit.unit
  let j : C(X × (PUnit : Type u), X) := awProductFst X PUnit
  have hji : i.comp j = ContinuousMap.id (X × (PUnit : Type u)) := by
    apply ContinuousMap.ext
    intro x
    exact Prod.ext rfl (Subsingleton.elim _ _)
  have hGraph : rawFullHomologyMap i n a = z := by
    change rawFullHomologyMap j n z = a at hf
    rw [← hf, ← show rawFullHomologyMap (i.comp j) n z =
      rawFullHomologyMap i n (rawFullHomologyMap j n z) from
        LinearMap.congr_fun (rawFullHomologyMap_comp j i n) z,
      hji, rawFullHomologyMap_id, LinearMap.id_apply]
  let f := ContinuousMap.id X
  let g := ContinuousMap.const (PUnit : Type u) y
  have hn := rawHomologyCross_naturality f g (n := n) (p := n) (q := 0)
    (rfl : n + 0 = n) a (rawHomologyPoint PUnit PUnit.unit)
  rw [show f = ContinuousMap.id X from rfl, rawFullHomologyMap_id, LinearMap.id_apply,
    rawFullHomologyMap_point] at hn
  change rawFullHomologyMap (awProductMap f g) n z =
    rawHomologyCross X Y (rfl : n + 0 = n) a (rawHomologyPoint Y y) at hn
  rw [← hn, ← hGraph, ← show rawFullHomologyMap ((awProductMap f g).comp i) n a =
    rawFullHomologyMap (awProductMap f g) n (rawFullHomologyMap i n a) from
      LinearMap.congr_fun (rawFullHomologyMap_comp i (awProductMap f g) n) a]
  rfl

theorem rawHomologyCross_point_left (n : ℕ) (x : X) (b : RawHomology Y n) :
    rawHomologyCross X Y (Nat.zero_add n) (rawHomologyPoint X x) b =
      rawFullHomologyMap (awPointGraphLeft x) n b := by
  have hs := rawHomologyCross_swap (n := n) (p := n) (q := 0)
    (rfl : n + 0 = n) b (rawHomologyPoint X x)
  simp only [Nat.mul_zero, pow_zero, one_smul] at hs
  calc
    _ = rawFullHomologyMap (awProductSwap Y X) n
        (rawHomologyCross Y X (rfl : n + 0 = n) b (rawHomologyPoint X x)) := hs.symm
    _ = rawFullHomologyMap (awProductSwap Y X) n (rawFullHomologyMap (awPointGraphRight x) n b) :=
      congrArg (rawFullHomologyMap (awProductSwap Y X) n)
        (rawHomologyCross_point_right (X := Y) (Y := X) n b x)
    _ = _ := (LinearMap.congr_fun (rawFullHomologyMap_comp (awPointGraphRight x) (awProductSwap Y X) n) b).symm

end BanachIsometric.SingularEZ

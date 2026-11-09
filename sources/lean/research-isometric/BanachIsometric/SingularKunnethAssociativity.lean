import BanachIsometric.SingularKunnethPairing
import BanachIsometric.SingularCrossNaturality

/-! The Künneth equivalence is coherently associative on each triple
component of actual singular homology. The proof uses the strict three
Alexander--Whitney cuts and the actual tensor contraction on cycles. -/

noncomputable section
universe u
namespace BanachIsometric.SingularEZ

set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000

open SingularPrism SingularAW
open scoped TensorProduct

variable (X Y Z : Type u) [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

theorem rawKunnethAssociativity {n p q r : ℕ} (h : p + q + r = n)
    (a : RawHomology ((X × Y) × Z) n) :
    TensorProduct.assoc ℚ (RawHomology X p) (RawHomology Y q) (RawHomology Z r)
      (TensorProduct.map (rawKunnethHomologyComponent X Y (rfl : p + q = p + q)) LinearMap.id
        (rawKunnethHomologyComponent (X × Y) Z h a)) =
    TensorProduct.map LinearMap.id (rawKunnethHomologyComponent Y Z (rfl : q + r = q + r))
      (rawKunnethHomologyComponent X (Y × Z) (by omega : p + (q + r) = n)
        (rawFullHomologyMap awProductAssoc n a)) := by
  let c := rawHomologyCycleRepresentative ((X × Y) × Z) n a
  let c' := rawFullCyclesMap (awProductAssoc (X := X) (Y := Y) (Z := Z)) n c
  have hc : rawFactorHomologyProjection ((X × Y) × Z) n c.val = a :=
    rawFactorHomologyProjection_representative n a
  have hc' : rawFactorHomologyProjection (X × (Y × Z)) n c'.val = rawFullHomologyMap awProductAssoc n a := by
    have he := (rawFullHomologyMap_cycle (awProductAssoc (X := X) (Y := Y) (Z := Z)) n c).symm
    change rawFactorHomologyProjection (X × (Y × Z)) n c'.val =
      rawFullHomologyMap awProductAssoc n (rawFactorHomologyProjection ((X × Y) × Z) n c.val) at he
    exact he.trans (congrArg (rawFullHomologyMap awProductAssoc n) hc)
  have hleft := rawSingularKunneth_pairing (X × Y) Z h
    (rawKunnethChainComponent X Y (p + q) p q) (rawFactorHomologyProjection Z r)
    (rawKunnethChainComponent_boundary X Y rfl) (rawFactorHomologyProjection_boundary Z r) c
  rw [rawKunnethChainComponent_comp_inclusion X Y rfl,
    rawFactorHomologyProjection_comp_inclusion Z r, hc] at hleft
  have hright := rawSingularKunneth_pairing X (Y × Z) (by omega : p + (q + r) = n)
    (rawFactorHomologyProjection X p) (rawKunnethChainComponent Y Z (q + r) q r)
    (rawFactorHomologyProjection_boundary X p) (rawKunnethChainComponent_boundary Y Z rfl) c'
  rw [rawFactorHomologyProjection_comp_inclusion X p, rawKunnethChainComponent_comp_inclusion Y Z rfl,
    hc'] at hright
  rw [← hleft, ← hright]
  have hcut := LinearMap.congr_fun (rawAlexanderWhitney_coassociativity (X := X) (Y := Y) (Z := Z) h) c.val
  have he := congrArg
    (TensorProduct.map (rawFactorHomologyProjection X p)
      (TensorProduct.map (rawFactorHomologyProjection Y q) (rawFactorHomologyProjection Z r))) hcut
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.map_map_assoc, TensorProduct.map_map,
    LinearMap.comp_id] at he
  exact he

end BanachIsometric.SingularEZ

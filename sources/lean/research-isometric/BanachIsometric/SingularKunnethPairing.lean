import BanachIsometric.RawTensorCyclePairing

/-! Projecting Alexander--Whitney on a cycle commutes with every
boundary-killing tensor pairing. -/

noncomputable section
universe u
namespace BanachIsometric.SingularEZ

open SingularPrism SingularAW VectorChainSplitting
open scoped TensorProduct

variable (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y]

def rawKunnethHomologyComponent {n p q : ℕ} (h : p + q = n) :
    RawHomology (X × Y) n →ₗ[ℚ] (RawHomology X p ⊗[ℚ] RawHomology Y q) :=
  (rawHomologyTensorComponent X Y h).comp (rawSingularKunnethEquiv X Y n).toLinearMap

theorem rawKunnethChainComponent_comp_inclusion {n p q : ℕ} (h : p + q = n) :
    (rawKunnethChainComponent X Y n p q).comp (rawFactorHomologyInclusion (X × Y) n) =
      rawKunnethHomologyComponent X Y h := by
  apply LinearMap.ext
  intro a
  let c := homologySection (rawFactorObjects (X × Y)) (rawBoundary (X := X × Y))
    (rawBoundary_squared (X := X × Y)) n a
  have hc : rawFactorHomologyProjection (X × Y) n c.val = a :=
    rawFactorHomologyProjection_inclusion (X × Y) n a
  have he := rawKunnethChainComponent_cycle X Y h c
  rw [hc] at he
  exact he.symm

theorem rawFactorHomologyProjection_comp_inclusion (X : Type*) [TopologicalSpace X] (n : ℕ) :
    (rawFactorHomologyProjection X n).comp (rawFactorHomologyInclusion X n) = LinearMap.id := by
  apply LinearMap.ext
  intro a
  exact rawFactorHomologyProjection_inclusion X n a

theorem rawSingularKunneth_pairing {n p q : ℕ} (h : p + q = n)
    {A B : Type*} [AddCommMonoid A] [Module ℚ A] [AddCommMonoid B] [Module ℚ B]
    (f : RawRationalChains X p →ₗ[ℚ] A) (g : RawRationalChains Y q →ₗ[ℚ] B)
    (hf : ∀ a, f (rawBoundary p a) = 0) (hg : ∀ b, g (rawBoundary q b) = 0)
    (c : RawHomologyCycles (X × Y) n) :
    TensorProduct.map f g (rawAWComponent X Y n p q c.val) =
      TensorProduct.map (f.comp (rawFactorHomologyInclusion X p))
        (g.comp (rawFactorHomologyInclusion Y q))
        (rawKunnethHomologyComponent X Y h (rawFactorHomologyProjection (X × Y) n c.val)) := by
  rw [rawKunnethHomologyComponent, LinearMap.comp_apply, LinearEquiv.coe_coe, rawSingularKunnethEquiv_cycle]
  exact rawTensorCycle_pairing X Y h f g hf hg
    (chainCyclesMap (hd := rawBoundary_squared (X := X × Y)) (he := rawTensorBoundary_squared X Y)
      (rawAlexanderWhitneyChainMap X Y) n c)

end BanachIsometric.SingularEZ

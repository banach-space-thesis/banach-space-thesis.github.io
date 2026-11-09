import BanachIsometric.AlexanderWhitneyTripleCuts
import BanachIsometric.RawTensorComponents
import Mathlib.LinearAlgebra.TensorProduct.Associator

/-! Strict coassociativity of Alexander--Whitney, at every actual triple
component. The comparison uses the literal product and tensor associators. -/

noncomputable section
namespace BanachIsometric.SingularAW

open SingularPrism
open scoped TensorProduct

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

def rawAWComponent (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y] (n p q : ℕ) :
    RawRationalChains (X × Y) n →ₗ[ℚ] RawTensorChains X Y p q :=
  (rawTensorComponent X Y p q).comp (rawAlexanderWhitney n)

theorem rawAWComponent_single {n p q : ℕ} (h : p + q = n)
    (σ : RawSingularSimplex (X × Y) n) (a : ℚ) :
    rawAWComponent X Y n p q (Finsupp.single σ a) = a • awPureTerm σ p q h :=
  rawAlexanderWhitney_component_single X Y h σ a

theorem rawAWComponent_single_of_ne {n p q : ℕ} (h : p + q ≠ n)
    (σ : RawSingularSimplex (X × Y) n) (a : ℚ) :
    rawAWComponent X Y n p q (Finsupp.single σ a) = 0 :=
  rawAlexanderWhitney_component_single_of_ne X Y h σ a

theorem rawAlexanderWhitney_coassociativity {n p q r : ℕ} (h : p + q + r = n) :
    ((TensorProduct.assoc ℚ (RawRationalChains X p) (RawRationalChains Y q)
      (RawRationalChains Z r)).toLinearMap.comp
        (TensorProduct.map (rawAWComponent X Y (p + q) p q) LinearMap.id)).comp
          (rawAWComponent (X × Y) Z n (p + q) r) =
      (TensorProduct.map LinearMap.id (rawAWComponent Y Z (q + r) q r)).comp
        ((rawAWComponent X (Y × Z) n p (q + r)).comp
          (rawChainMap (awProductAssoc (X := X) (Y := Y) (Z := Z)) n)) := by
  apply Finsupp.lhom_ext'
  intro σ
  apply LinearMap.ext_ring
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
  have h' : p + (q + r) = n := by omega
  have hpush : rawChainMap (awProductAssoc (X := X) (Y := Y) (Z := Z)) n (Finsupp.single σ 1) =
      Finsupp.single (awProductAssoc.comp σ) 1 := by simp [rawChainMap]
  rw [hpush, rawAWComponent_single h, rawAWComponent_single h']
  simp only [one_smul, awPureTerm, TensorProduct.map_tmul, LinearMap.id_apply]
  rw [rawAWComponent_single (show p + q = p + q from rfl),
    rawAWComponent_single (show q + r = q + r from rfl)]
  simp only [one_smul, awPureTerm, LinearEquiv.coe_coe, TensorProduct.assoc_tmul]
  rw [awTripleFront h, awTripleMiddle h, awTripleBack h]

end BanachIsometric.SingularAW

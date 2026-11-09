import BanachIsometric.RawTensorSwap
import BanachIsometric.RawTensorAugmentation

/-! Strict naturality of the signed tensor swap and its compatibility
with the actual degree-zero augmentation. -/

noncomputable section
namespace BanachIsometric.SingularAW

open SingularPrism
open scoped TensorProduct

variable {X Y X' Y' : Type*}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace X'] [TopologicalSpace Y']

def awProductSwap (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y] : C(X × Y, Y × X) :=
  ⟨Prod.swap, continuous_snd.prodMk continuous_fst⟩

theorem awProductSwap_comp_awProductSwap :
    (awProductSwap Y X).comp (awProductSwap X Y) = ContinuousMap.id (X × Y) := rfl

theorem awProductMap_comp_awProductSwap (f : C(X, X')) (g : C(Y, Y')) :
    (awProductMap g f).comp (awProductSwap X Y) = (awProductSwap X' Y').comp (awProductMap f g) := rfl

theorem rawChainMap_awProductSwap_involutive (n : ℕ) (c : RawRationalChains (X × Y) n) :
    rawChainMap (awProductSwap Y X) n (rawChainMap (awProductSwap X Y) n c) = c := by
  have h := LinearMap.congr_fun (rawChainMap_comp (awProductSwap X Y) (awProductSwap Y X) n) c
  rw [awProductSwap_comp_awProductSwap, rawChainMap_id] at h
  exact h.symm

theorem rawTensorSwap_naturality (f : C(X, X')) (g : C(Y, Y'))
    (c : RawBigradedTensorChains X Y) :
    rawTensorSwap X' Y' (rawBigradedTensorMap f g c) =
      rawBigradedTensorMap g f (rawTensorSwap X Y c) := by
  have h : (rawTensorSwap X' Y').comp (rawBigradedTensorMap f g) =
      (rawBigradedTensorMap g f).comp (rawTensorSwap X Y) := by
    apply DirectSum.linearMap_ext
    rintro ⟨p, q⟩
    apply TensorProduct.ext
    apply LinearMap.ext
    intro a
    apply LinearMap.ext
    intro b
    change rawTensorSwap X' Y'
      (rawBigradedTensorMap f g (rawTensorInclusion X Y p q (a ⊗ₜ[ℚ] b))) =
        rawBigradedTensorMap g f (rawTensorSwap X Y (rawTensorInclusion X Y p q (a ⊗ₜ[ℚ] b)))
    simp only [rawTensorSwap_tmul, rawBigradedTensorMap_inclusion, TensorProduct.map_tmul, map_smul]
  exact LinearMap.congr_fun h c

theorem rawTensorSwap_augmentation (c : RawBigradedTensorChains X Y) :
    rawTensorAugmentation Y X (rawTensorSwap X Y c) = rawTensorAugmentation X Y c := by
  have h : (rawTensorAugmentation Y X).comp (rawTensorSwap X Y) = rawTensorAugmentation X Y := by
    apply DirectSum.linearMap_ext
    rintro ⟨p, q⟩
    apply TensorProduct.ext
    apply LinearMap.ext
    intro a
    apply LinearMap.ext
    intro b
    change rawTensorAugmentation Y X (rawTensorSwap X Y (rawTensorInclusion X Y p q (a ⊗ₜ[ℚ] b))) =
      rawTensorAugmentation X Y (rawTensorInclusion X Y p q (a ⊗ₜ[ℚ] b))
    rw [rawTensorSwap_tmul, map_smul]
    simp only [rawTensorAugmentation, LinearMap.comp_apply]
    by_cases hpq : (p, q) = (0, 0)
    · have hp : p = 0 := congrArg Prod.fst hpq
      have hq : q = 0 := congrArg Prod.snd hpq
      subst p
      subst q
      simp only [rawTensorComponent_inclusion, rawTensorZeroAugmentation_tmul, zero_mul, pow_zero,
        one_smul, mul_comm]
    · have hqp : (q, p) ≠ (0, 0) := fun he => hpq (congrArg Prod.swap he)
      rw [rawTensorComponent_inclusion_of_ne Y X hqp, rawTensorComponent_inclusion_of_ne X Y hpq,
        map_zero, map_zero, smul_zero]
  exact LinearMap.congr_fun h c

end BanachIsometric.SingularAW

import Mathlib.LinearAlgebra.DirectSum.TensorProduct

/-! The literal direct-sum component maps separate tensors in a
tensor product with a direct sum on the right. -/

noncomputable section
namespace BanachIsometric

open scoped TensorProduct DirectSum

variable {K ι A : Type*} [CommSemiring K] [DecidableEq ι]
  [AddCommMonoid A] [Module K A] {M : ι → Type*}
  [∀ i, AddCommMonoid (M i)] [∀ i, Module K (M i)]

theorem tensorDirectSumRight_component (i : ι) (z : A ⊗[K] (⨁ j, M j)) :
    DirectSum.component K ι (fun j => A ⊗[K] M j) i (TensorProduct.directSumRight K A M z) =
      TensorProduct.map LinearMap.id (DirectSum.component K ι M i) z := by
  have h : (DirectSum.component K ι (fun j => A ⊗[K] M j) i).comp
      (TensorProduct.directSumRight K A M).toLinearMap =
      TensorProduct.map LinearMap.id (DirectSum.component K ι M i) := by
    apply TensorProduct.ext
    apply LinearMap.ext
    intro a
    apply DirectSum.linearMap_ext
    intro j
    apply LinearMap.ext
    intro b
    change DirectSum.component K ι (fun j => A ⊗[K] M j) i
      (TensorProduct.directSumRight K A M (a ⊗ₜ[K] DirectSum.lof K ι M j b)) =
      TensorProduct.map LinearMap.id (DirectSum.component K ι M i)
        (a ⊗ₜ[K] DirectSum.lof K ι M j b)
    rw [TensorProduct.directSumRight_tmul_lof, TensorProduct.map_tmul, LinearMap.id_apply]
    by_cases hji : j = i
    · subst j
      simp only [DirectSum.component.lof_self]
    · simp only [DirectSum.component.of, hji, dite_false, TensorProduct.tmul_zero]
  exact LinearMap.congr_fun h z

theorem tensorDirectSumRight_ext {z w : A ⊗[K] (⨁ j, M j)}
    (h : ∀ i, TensorProduct.map LinearMap.id (DirectSum.component K ι M i) z =
      TensorProduct.map LinearMap.id (DirectSum.component K ι M i) w) : z = w := by
  apply (TensorProduct.directSumRight K A M).injective
  apply DirectSum.ext_component K
  intro i
  rw [tensorDirectSumRight_component, tensorDirectSumRight_component]
  exact h i

end BanachIsometric

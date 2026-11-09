import BanachIsometric.KoszulTensorAlgebra

/-! An actual algebra homomorphism to the separately tagged Koszul tensor
algebra supplies the correct unit and multiplicativity identities. The
bounded-grading even-primitive obstruction therefore needs no separately
postulated multiplicativity formula. No homology instance is asserted here. -/

noncomputable section
namespace BanachIsometric

open scoped TensorProduct

variable {K A : Type*} [CommRing K] [Ring A] [Algebra K A]
  (𝒜 : ℕ → Submodule K A) [GradedAlgebra 𝒜]

def koszulCoproductUnderlying (Δ : A →ₐ[K] KoszulTensor 𝒜) : A →ₗ[K] A ⊗[K] A :=
  (KoszulTensor.tensorLinearEquiv 𝒜).toLinearMap.comp Δ.toLinearMap

@[simp] theorem koszulCoproductUnderlying_apply (Δ : A →ₐ[K] KoszulTensor 𝒜) (a : A) :
    koszulCoproductUnderlying 𝒜 Δ a = (Δ a).val := rfl

theorem koszulCoproductUnderlying_one (Δ : A →ₐ[K] KoszulTensor 𝒜) :
    koszulCoproductUnderlying 𝒜 Δ 1 = 1 := by
  change (Δ 1).val = (1 : A ⊗[K] A)
  rw [map_one, KoszulTensor.val_one]
  rfl

theorem koszulCoproductUnderlying_mul (Δ : A →ₐ[K] KoszulTensor 𝒜) (a b : A) :
    koszulCoproductUnderlying 𝒜 Δ (a * b) =
      koszulTensorMul 𝒜 (koszulCoproductUnderlying 𝒜 Δ a)
        (koszulCoproductUnderlying 𝒜 Δ b) := by
  change (Δ (a * b)).val = koszulTensorMul 𝒜 (Δ a).val (Δ b).val
  rw [map_mul, KoszulTensor.val_mul]

theorem even_primitive_eq_zero_of_bounded_koszul_algHom
    {K A : Type*} [Field K] [CharZero K] [Ring A] [Algebra K A] [Nontrivial A]
    (𝒜 : ℕ → Submodule K A) [GradedAlgebra 𝒜]
    (N : ℕ) (hbound : ∀ d : ℕ, N < d → 𝒜 d = ⊥)
    (Δ : A →ₐ[K] KoszulTensor 𝒜)
    {j : ℕ} (hj : 0 < j) (heven : Even j) {x : A} (hx : x ∈ 𝒜 j)
    (hprimitive : Δ x = KoszulTensor.tmul 𝒜 x 1 + KoszulTensor.tmul 𝒜 1 x) : x = 0 := by
  apply even_primitive_eq_zero_of_bounded_koszul_coproduct 𝒜 N hbound
    (koszulCoproductUnderlying 𝒜 Δ) (koszulCoproductUnderlying_one 𝒜 Δ)
    (koszulCoproductUnderlying_mul 𝒜 Δ) hj heven hx
  exact congrArg KoszulTensor.val hprimitive

end BanachIsometric

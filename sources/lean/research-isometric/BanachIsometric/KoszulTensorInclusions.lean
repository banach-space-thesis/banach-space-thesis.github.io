import BanachIsometric.KoszulTensorAlgebra

/-! The two genuine algebra inclusions into the tagged Koszul tensor ring.
Their products recover pure tensors; switching their order has the actual
homogeneous Koszul sign, rather than ordinary tensor commutation. -/

noncomputable section
namespace BanachIsometric.KoszulTensor

open scoped TensorProduct

variable {K A : Type*} [CommRing K] [Ring A] [Algebra K A]
  (𝒜 : ℕ → Submodule K A) [GradedAlgebra 𝒜]

def leftLinearMap : A →ₗ[K] KoszulTensor 𝒜 :=
  (tensorLinearEquiv 𝒜).symm.toLinearMap.comp ((TensorProduct.mk K A A).flip 1)

def rightLinearMap : A →ₗ[K] KoszulTensor 𝒜 :=
  (tensorLinearEquiv 𝒜).symm.toLinearMap.comp (TensorProduct.mk K A A 1)

def leftAlgHom : A →ₐ[K] KoszulTensor 𝒜 :=
  AlgHom.ofLinearMap (leftLinearMap 𝒜)
    (by apply val_injective 𝒜; rfl)
    (fun a b => by
      apply val_injective 𝒜
      change (a * b) ⊗ₜ[K] 1 = koszulTensorMul 𝒜 (a ⊗ₜ[K] 1) (b ⊗ₜ[K] 1)
      rw [koszulTensorMul_tmul_of_mem 𝒜 a b 1 (SetLike.one_mem_graded 𝒜), gradedSignTwist_zero]
      simp only [LinearMap.id_apply, one_mul])

def rightAlgHom : A →ₐ[K] KoszulTensor 𝒜 :=
  AlgHom.ofLinearMap (rightLinearMap 𝒜)
    (by apply val_injective 𝒜; rfl)
    (fun a b => by
      apply val_injective 𝒜
      have h : ((koszulTensorMul 𝒜).flip (1 ⊗ₜ[K] b)).comp (TensorProduct.mk K A A 1) =
          (TensorProduct.mk K A A 1).comp ((LinearMap.mul K A).flip b) := by
        apply DirectSum.decompose_lhom_ext 𝒜
        intro j
        apply LinearMap.ext
        intro v
        change koszulTensorMul 𝒜 (1 ⊗ₜ[K] v.val) (1 ⊗ₜ[K] b) = 1 ⊗ₜ[K] (v.val * b)
        rw [koszulTensorMul_tmul_of_mem 𝒜 1 1 b v.property, gradedSignTwist_one, one_mul]
      exact (congrArg (fun L : A →ₗ[K] A ⊗[K] A => L a) h).symm)

@[simp] theorem leftAlgHom_apply (a : A) : leftAlgHom 𝒜 a = tmul 𝒜 a 1 := rfl
@[simp] theorem rightAlgHom_apply (a : A) : rightAlgHom 𝒜 a = tmul 𝒜 1 a := rfl

theorem left_mul_right (a b : A) : leftAlgHom 𝒜 a * rightAlgHom 𝒜 b = tmul 𝒜 a b := by
  apply val_injective 𝒜
  change koszulTensorMul 𝒜 (a ⊗ₜ[K] 1) (1 ⊗ₜ[K] b) = a ⊗ₜ[K] b
  rw [koszulTensorMul_tmul_of_mem 𝒜 a 1 b (SetLike.one_mem_graded 𝒜), gradedSignTwist_one]
  simp only [mul_one, one_mul]

theorem right_mul_left_of_mem {i j : ℕ} {a b : A}
    (ha : a ∈ 𝒜 i) (hb : b ∈ 𝒜 j) :
    rightAlgHom 𝒜 b * leftAlgHom 𝒜 a =
      (-1 : K) ^ (j * i) • (leftAlgHom 𝒜 a * rightAlgHom 𝒜 b) := by
  rw [left_mul_right]
  apply val_injective 𝒜
  change koszulTensorMul 𝒜 (1 ⊗ₜ[K] b) (a ⊗ₜ[K] 1) =
    (-1 : K) ^ (j * i) • (a ⊗ₜ[K] b)
  rw [koszulTensorMul_homogeneous_tmul 𝒜 1 1 hb ha, one_mul, mul_one]

end BanachIsometric.KoszulTensor

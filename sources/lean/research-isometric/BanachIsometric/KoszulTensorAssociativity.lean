import BanachIsometric.KoszulTensorMultiplication
import BanachIsometric.GradedSignTwistAlgebra

/-! Associativity and the genuine tensor unit for the actual Koszul
bilinear product. These are identities of the constructed bilinear map;
the ordinary tensor ring instance is left unchanged. -/

noncomputable section
namespace BanachIsometric

open scoped TensorProduct

variable {K A : Type*} [CommRing K] [Ring A] [Algebra K A]
  (𝒜 : ℕ → Submodule K A) [GradedAlgebra 𝒜]

theorem koszulTensorMul_tmul_assoc (a b c d e f : A) :
    koszulTensorMul 𝒜 (koszulTensorMul 𝒜 (a ⊗ₜ[K] b) (c ⊗ₜ[K] d)) (e ⊗ₜ[K] f) =
      koszulTensorMul 𝒜 (a ⊗ₜ[K] b) (koszulTensorMul 𝒜 (c ⊗ₜ[K] d) (e ⊗ₜ[K] f)) := by
  let μ := koszulTensorMul 𝒜
  let L := μ.flip (e ⊗ₜ[K] f)
  have h : (μ.compr₂ L).compl₁₂ (TensorProduct.mk K A A a) (TensorProduct.mk K A A c) =
      (μ.compl₂ L).compl₁₂ (TensorProduct.mk K A A a) (TensorProduct.mk K A A c) := by
    apply DirectSum.decompose_lhom_ext 𝒜
    intro i
    apply LinearMap.ext
    intro u
    apply DirectSum.decompose_lhom_ext 𝒜
    intro j
    apply LinearMap.ext
    intro v
    change koszulTensorMul 𝒜 (koszulTensorMul 𝒜 (a ⊗ₜ[K] u.val) (c ⊗ₜ[K] v.val))
        (e ⊗ₜ[K] f) =
      koszulTensorMul 𝒜 (a ⊗ₜ[K] u.val)
        (koszulTensorMul 𝒜 (c ⊗ₜ[K] v.val) (e ⊗ₜ[K] f))
    rw [koszulTensorMul_tmul_of_mem 𝒜 a c v.val u.property,
      koszulTensorMul_tmul_of_mem 𝒜 _ e f (SetLike.mul_mem_graded u.property v.property),
      koszulTensorMul_tmul_of_mem 𝒜 c e f v.property,
      koszulTensorMul_tmul_of_mem 𝒜 a _ _ u.property, gradedSignTwist_mul]
    have hcomp : gradedSignTwist 𝒜 i (gradedSignTwist 𝒜 j e) =
        gradedSignTwist 𝒜 (i + j) e :=
      congrArg (fun L : A →ₗ[K] A => L e) (gradedSignTwist_comp 𝒜 i j)
    rw [hcomp, mul_assoc, mul_assoc]
  exact congrArg (fun B : A →ₗ[K] A →ₗ[K] A ⊗[K] A => B b d) h

theorem koszulTensorMul_assoc (x y z : A ⊗[K] A) :
    koszulTensorMul 𝒜 (koszulTensorMul 𝒜 x y) z =
      koszulTensorMul 𝒜 x (koszulTensorMul 𝒜 y z) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | tmul a b =>
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero, LinearMap.zero_apply]
    | tmul c d =>
      induction z using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul e f => exact koszulTensorMul_tmul_assoc 𝒜 a b c d e f
      | add z₁ z₂ h₁ h₂ => simp only [map_add, h₁, h₂]
    | add y₁ y₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂]
  | add x₁ x₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂]

theorem koszulTensorMul_one_left (x : A ⊗[K] A) :
    koszulTensorMul 𝒜 (1 ⊗ₜ[K] 1) x = x := by
  have h : koszulTensorMul 𝒜 (1 ⊗ₜ[K] 1) = LinearMap.id := by
    apply TensorProduct.ext
    ext a b
    change koszulTensorMul 𝒜 (1 ⊗ₜ[K] 1) (a ⊗ₜ[K] b) = a ⊗ₜ[K] b
    rw [koszulTensorMul_tmul_of_mem 𝒜 1 a b (SetLike.one_mem_graded 𝒜), gradedSignTwist_zero]
    simp only [LinearMap.id_apply, one_mul]
  exact congrArg (fun L : A ⊗[K] A →ₗ[K] A ⊗[K] A => L x) h

theorem koszulTensorMul_one_right (x : A ⊗[K] A) :
    koszulTensorMul 𝒜 x (1 ⊗ₜ[K] 1) = x := by
  have h : (koszulTensorMul 𝒜).flip (1 ⊗ₜ[K] 1) = LinearMap.id := by
    apply TensorProduct.ext
    ext a b
    have h' : ((koszulTensorMul 𝒜).flip (1 ⊗ₜ[K] 1)).comp (TensorProduct.mk K A A a) =
        TensorProduct.mk K A A a := by
      apply DirectSum.decompose_lhom_ext 𝒜
      intro j
      apply LinearMap.ext
      intro v
      change koszulTensorMul 𝒜 (a ⊗ₜ[K] v.val) (1 ⊗ₜ[K] 1) = a ⊗ₜ[K] v.val
      rw [koszulTensorMul_tmul_of_mem 𝒜 a 1 1 v.property, gradedSignTwist_one]
      simp only [mul_one]
    exact congrArg (fun L : A →ₗ[K] A ⊗[K] A => L b) h'
  exact congrArg (fun L : A ⊗[K] A →ₗ[K] A ⊗[K] A => L x) h

end BanachIsometric

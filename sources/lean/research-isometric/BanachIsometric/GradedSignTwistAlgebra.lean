import BanachIsometric.GradedSignTwist

/-! The actual graded sign operators are algebra endomorphisms and compose
by addition of their sign parameters. These statements concern the genuine
internal grading, and do not change the original algebra multiplication. -/

noncomputable section
namespace BanachIsometric

variable {K A : Type*} [CommRing K] [Ring A] [Algebra K A]
  (𝒜 : ℕ → Submodule K A) [GradedAlgebra 𝒜]

theorem gradedSignTwist_mul (k : ℕ) (x y : A) :
    gradedSignTwist 𝒜 k (x * y) = gradedSignTwist 𝒜 k x * gradedSignTwist 𝒜 k y := by
  have h : (LinearMap.mul K A).compr₂ (gradedSignTwist 𝒜 k) =
      (LinearMap.mul K A).compl₁₂ (gradedSignTwist 𝒜 k) (gradedSignTwist 𝒜 k) := by
    apply DirectSum.decompose_lhom_ext 𝒜
    intro i
    apply LinearMap.ext
    intro a
    apply DirectSum.decompose_lhom_ext 𝒜
    intro j
    apply LinearMap.ext
    intro b
    change gradedSignTwist 𝒜 k (a.val * b.val) =
      gradedSignTwist 𝒜 k a.val * gradedSignTwist 𝒜 k b.val
    rw [gradedSignTwist_of_mem 𝒜 k (SetLike.mul_mem_graded a.property b.property),
      gradedSignTwist_of_mem 𝒜 k a.property, gradedSignTwist_of_mem 𝒜 k b.property,
      Nat.mul_add, pow_add, smul_mul_smul_comm]
  exact congrArg (fun L : A →ₗ[K] A →ₗ[K] A => L x y) h

theorem gradedSignTwist_comp (k l : ℕ) :
    (gradedSignTwist 𝒜 k).comp (gradedSignTwist 𝒜 l) = gradedSignTwist 𝒜 (k + l) := by
  apply DirectSum.decompose_lhom_ext 𝒜
  intro j
  apply LinearMap.ext
  intro x
  change gradedSignTwist 𝒜 k (gradedSignTwist 𝒜 l x.val) =
    gradedSignTwist 𝒜 (k + l) x.val
  rw [gradedSignTwist_of_mem 𝒜 l x.property, map_smul,
    gradedSignTwist_of_mem 𝒜 k x.property, gradedSignTwist_of_mem 𝒜 (k + l) x.property,
    smul_smul, Nat.add_mul, pow_add, mul_comm]

theorem gradedSignTwist_zero : gradedSignTwist 𝒜 0 = LinearMap.id :=
  gradedSignTwist_eq_id_of_even 𝒜 (by simp)

def gradedSignTwistAlgHom (k : ℕ) : A →ₐ[K] A :=
  AlgHom.ofLinearMap (gradedSignTwist 𝒜 k) (gradedSignTwist_one 𝒜 k)
    (gradedSignTwist_mul 𝒜 k)

@[simp] theorem gradedSignTwistAlgHom_apply (k : ℕ) (x : A) :
    gradedSignTwistAlgHom 𝒜 k x = gradedSignTwist 𝒜 k x := rfl

theorem gradedSignTwist_involutive (k : ℕ) :
    Function.Involutive (gradedSignTwist 𝒜 k) := by
  intro x
  have h := congrArg (fun L : A →ₗ[K] A => L x) (gradedSignTwist_comp 𝒜 k k)
  rw [gradedSignTwist_eq_id_of_even 𝒜 (show Even (k + k) from ⟨k, rfl⟩)] at h
  exact h

end BanachIsometric

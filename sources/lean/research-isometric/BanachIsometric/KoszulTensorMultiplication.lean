import BanachIsometric.GradedSignTwist
import BanachIsometric.BinomialCoproduct

/-!
# Actual Koszul tensor multiplication and the positive even primitive obstruction

The product is constructed from the actual graded decomposition and the sign
operators. Its pure homogeneous tensor formula is proved, including the sign
(-1)^(degree b * degree c). A positive even primitive in an actually bounded
graded algebra is zero when the supplied coproduct is multiplicative for THIS
product. Neither singular homology nor rational Hurewicz comparison is assumed
or asserted to have been constructed here.
-/

noncomputable section
namespace BanachIsometric

open scoped TensorProduct

variable {K A : Type*} [CommRing K] [Ring A] [Algebra K A]
  (𝒜 : ℕ → Submodule K A) [GradedAlgebra 𝒜]

def koszulGradeAction (j : ℕ) :
    A →ₗ[K] (𝒜 j) →ₗ[K] (A ⊗[K] A →ₗ[K] A ⊗[K] A) :=
  (TensorProduct.mapBilinear K A A A A).compl₁₂
    ((LinearMap.mul K A).compl₂ (gradedSignTwist 𝒜 j))
    ((LinearMap.mul K A).comp (𝒜 j).subtype)

def koszulLeftAction (a : A) : A →ₗ[K] (A ⊗[K] A →ₗ[K] A ⊗[K] A) :=
  (DirectSum.toModule K ℕ (A ⊗[K] A →ₗ[K] A ⊗[K] A)
    (fun j => koszulGradeAction 𝒜 j a)).comp (DirectSum.decomposeLinearEquiv 𝒜).toLinearMap

theorem koszulLeftAction_of_mem (a : A) {j : ℕ} {b : A} (hb : b ∈ 𝒜 j) :
    koszulLeftAction 𝒜 a b = koszulGradeAction 𝒜 j a ⟨b, hb⟩ := by
  change DirectSum.toModule K ℕ (A ⊗[K] A →ₗ[K] A ⊗[K] A) _
    (DirectSum.decompose 𝒜 b) = _
  rw [DirectSum.decompose_of_mem 𝒜 hb]
  change DirectSum.toModule K ℕ (A ⊗[K] A →ₗ[K] A ⊗[K] A) _
    (DirectSum.lof K ℕ (fun i => 𝒜 i) j ⟨b, hb⟩) = _
  rw [DirectSum.toModule_lof]

def koszulPureAction : A →ₗ[K] A →ₗ[K] (A ⊗[K] A →ₗ[K] A ⊗[K] A) where
  toFun := koszulLeftAction 𝒜
  map_add' a c := by
    apply DirectSum.decompose_lhom_ext 𝒜
    intro j
    apply LinearMap.ext
    intro b
    change koszulLeftAction 𝒜 (a + c) b.val =
      koszulLeftAction 𝒜 a b.val + koszulLeftAction 𝒜 c b.val
    rw [koszulLeftAction_of_mem 𝒜 (a + c) b.property,
      koszulLeftAction_of_mem 𝒜 a b.property, koszulLeftAction_of_mem 𝒜 c b.property]
    exact congrArg (fun q => q b) ((koszulGradeAction 𝒜 j).map_add a c)
  map_smul' r a := by
    apply DirectSum.decompose_lhom_ext 𝒜
    intro j
    apply LinearMap.ext
    intro b
    change koszulLeftAction 𝒜 (r • a) b.val = r • koszulLeftAction 𝒜 a b.val
    rw [koszulLeftAction_of_mem 𝒜 (r • a) b.property, koszulLeftAction_of_mem 𝒜 a b.property]
    exact congrArg (fun q => q b) ((koszulGradeAction 𝒜 j).map_smul r a)

def koszulTensorMul : (A ⊗[K] A) →ₗ[K] (A ⊗[K] A) →ₗ[K] (A ⊗[K] A) :=
  TensorProduct.lift (koszulPureAction 𝒜)

theorem koszulTensorMul_tmul_of_mem (a c d : A) {j : ℕ} {b : A} (hb : b ∈ 𝒜 j) :
    koszulTensorMul 𝒜 (a ⊗ₜ[K] b) (c ⊗ₜ[K] d) =
      (a * gradedSignTwist 𝒜 j c) ⊗ₜ[K] (b * d) := by
  rw [koszulTensorMul, TensorProduct.lift.tmul]
  change koszulLeftAction 𝒜 a b (c ⊗ₜ[K] d) = _
  rw [koszulLeftAction_of_mem 𝒜 a hb]
  simp only [koszulGradeAction, LinearMap.compl₁₂_apply, LinearMap.compl₂_apply,
    LinearMap.comp_apply, TensorProduct.mapBilinear_apply, TensorProduct.map_tmul,
    LinearMap.mul_apply', Submodule.subtype_apply]

theorem koszulTensorMul_homogeneous_tmul (a d : A) {j k : ℕ} {b c : A}
    (hb : b ∈ 𝒜 j) (hc : c ∈ 𝒜 k) :
    koszulTensorMul 𝒜 (a ⊗ₜ[K] b) (c ⊗ₜ[K] d) =
      (-1 : K) ^ (j * k) • ((a * c) ⊗ₜ[K] (b * d)) := by
  rw [koszulTensorMul_tmul_of_mem 𝒜 a c d hb, gradedSignTwist_of_mem 𝒜 j hc,
    mul_smul_comm, ← TensorProduct.smul_tmul']

theorem koszulTensorMul_left_even (a : A) {j : ℕ} {b : A}
    (hb : b ∈ 𝒜 j) (hj : Even j) :
    koszulTensorMul 𝒜 (a ⊗ₜ[K] b) = LinearMap.mul K (A ⊗[K] A) (a ⊗ₜ[K] b) := by
  apply TensorProduct.ext
  ext c d
  change koszulTensorMul 𝒜 (a ⊗ₜ[K] b) (c ⊗ₜ[K] d) =
    LinearMap.mul K (A ⊗[K] A) (a ⊗ₜ[K] b) (c ⊗ₜ[K] d)
  rw [koszulTensorMul_tmul_of_mem 𝒜 a c d hb, gradedSignTwist_eq_id_of_even 𝒜 hj]
  simp only [LinearMap.id_apply, LinearMap.mul_apply', Algebra.TensorProduct.tmul_mul_tmul]

theorem koszulTensorMul_primitive_even {j : ℕ} {x : A} (hx : x ∈ 𝒜 j) (hj : Even j) :
    koszulTensorMul 𝒜 (x ⊗ₜ[K] 1 + 1 ⊗ₜ[K] x) =
      LinearMap.mul K (A ⊗[K] A) (x ⊗ₜ[K] 1 + 1 ⊗ₜ[K] x) := by
  rw [map_add, koszulTensorMul_left_even 𝒜 x (SetLike.one_mem_graded 𝒜) (by simp),
    koszulTensorMul_left_even 𝒜 1 hx hj]
  exact ((LinearMap.mul K (A ⊗[K] A)).map_add _ _).symm

theorem even_primitive_eq_zero_of_bounded_koszul_coproduct
    {K A : Type*} [Field K] [CharZero K] [Ring A] [Algebra K A] [Nontrivial A]
    (𝒜 : ℕ → Submodule K A) [GradedAlgebra 𝒜]
    (N : ℕ) (hbound : ∀ d : ℕ, N < d → 𝒜 d = ⊥)
    (Δ : A →ₗ[K] A ⊗[K] A) (hunit : Δ 1 = 1)
    (hmul : ∀ a b, Δ (a * b) = koszulTensorMul 𝒜 (Δ a) (Δ b))
    {j : ℕ} (hj : 0 < j) (heven : Even j) {x : A} (hx : x ∈ 𝒜 j)
    (hprimitive : Δ x = x ⊗ₜ[K] 1 + 1 ⊗ₜ[K] x) : x = 0 := by
  apply eq_zero_of_bounded_grading_coproduct_step 𝒜 N hbound Δ hunit hj hx
  intro y
  rw [hmul, hprimitive, koszulTensorMul_primitive_even 𝒜 hx heven]
  rfl

end BanachIsometric

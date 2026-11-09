import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.Algebra.Ring.Parity

/-!
# Actual sign operators from the actual internal graded decomposition

The operator multiplies the degree-j component by (-1)^(k*j). Its action on
homogeneous elements and its identity for even k are proved from the genuine
direct-sum decomposition. These signs will define Koszul multiplication;
ordinary and graded tensor multiplications are not identified.
-/

noncomputable section
namespace BanachIsometric

variable {K A : Type*} [CommRing K] [Ring A] [Algebra K A]
  (𝒜 : ℕ → Submodule K A) [GradedAlgebra 𝒜]

def gradedSignTwist (k : ℕ) : A →ₗ[K] A :=
  (DirectSum.toModule K ℕ A (fun j => ((-1 : K) ^ (k * j)) • (𝒜 j).subtype)).comp
    (DirectSum.decomposeLinearEquiv 𝒜).toLinearMap

theorem gradedSignTwist_of_mem (k : ℕ) {j : ℕ} {x : A} (hx : x ∈ 𝒜 j) :
    gradedSignTwist 𝒜 k x = (-1 : K) ^ (k * j) • x := by
  change DirectSum.toModule K ℕ A _ (DirectSum.decompose 𝒜 x) = _
  rw [DirectSum.decompose_of_mem 𝒜 hx]
  change DirectSum.toModule K ℕ A _
    (DirectSum.lof K ℕ (fun i => 𝒜 i) j ⟨x, hx⟩) = _
  rw [DirectSum.toModule_lof]
  rfl

theorem gradedSignTwist_eq_id_of_even {k : ℕ} (hk : Even k) :
    gradedSignTwist 𝒜 k = LinearMap.id := by
  apply DirectSum.decompose_lhom_ext 𝒜
  intro j
  apply LinearMap.ext
  intro x
  change gradedSignTwist 𝒜 k x.val = x.val
  rw [gradedSignTwist_of_mem 𝒜 k x.property, (hk.mul_right j).neg_one_pow, one_smul]

theorem gradedSignTwist_of_even_degree (k : ℕ) {j : ℕ} (hj : Even j)
    {x : A} (hx : x ∈ 𝒜 j) : gradedSignTwist 𝒜 k x = x := by
  rw [gradedSignTwist_of_mem 𝒜 k hx, (hj.mul_left k).neg_one_pow, one_smul]

theorem gradedSignTwist_one (k : ℕ) : gradedSignTwist 𝒜 k 1 = 1 := by
  rw [gradedSignTwist_of_mem 𝒜 k (SetLike.one_mem_graded 𝒜)]
  simp only [mul_zero, pow_zero, one_smul]

end BanachIsometric

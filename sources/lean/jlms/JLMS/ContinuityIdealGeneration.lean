import JLMS.ContinuityIdeal

/-!
# Ogden Theorem 6.18: a codimension-one subspace generates the ideal

Ogden first puts M₀ = {T ∈ M : Tκκ = 0} in the continuity ideal. This
subspace is not closed under multiplication. A product with nonzero κκ
coordinate therefore supplies its missing one-dimensional direction.
The following algebraic lemma proves that argument explicitly.
-/

noncomputable section
namespace JLMS
variable {𝕜 : Type*} [RCLike 𝕜]
variable {B : Type*} [NonUnitalNormedRing B] [NormedSpace 𝕜 B]
  [IsScalarTower 𝕜 B B] [SMulCommClass 𝕜 B B]
variable {A : Type*} [NonUnitalNormedRing A] [NormedSpace 𝕜 A]

theorem continuityIdeal_contains_of_kernel_and_product
    (θ : B →ₙₐ[𝕜] A) (I : Submodule 𝕜 B) (χ : B →ₗ[𝕜] 𝕜)
    (hI : ∀ a ∈ I, ∀ b ∈ I, a * b ∈ I)
    (hzero : ∀ x ∈ I, χ x = 0 → x ∈ continuityIdeal θ)
    (a b : B) (ha : a ∈ I) (hb : b ∈ I)
    (hχa : χ a = 0) (hχab : χ (a * b) ≠ 0) : I ≤ continuityIdeal θ := by
  have habI := hI a ha b hb
  have habJ := continuityIdeal_mul_right θ b (hzero a ha hχa)
  intro x hx
  let c : 𝕜 := χ x / χ (a * b)
  let y : B := x - c • (a * b)
  have hyI : y ∈ I := I.sub_mem hx (I.smul_mem c habI)
  have hχy : χ y = 0 := by
    simp only [y, c, map_sub, map_smul, smul_eq_mul]
    rw [div_mul_cancel₀ _ hχab, sub_self]
  have hyJ := hzero y hyI hχy
  have he : y + c • (a * b) = x := sub_add_cancel _ _
  rw [← he]
  exact (continuityIdeal θ).add_mem hyJ ((continuityIdeal θ).smul_mem c habJ)

end JLMS

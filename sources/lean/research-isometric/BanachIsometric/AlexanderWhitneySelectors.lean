import BanachIsometric.AlexanderWhitneyMap

/-! Evaluating the actual Alexander--Whitney sum against linear selectors
of a literal bidegree. These lemmas are used for the differential identity. -/

noncomputable section
namespace BanachIsometric.SingularAW

open SingularPrism
open scoped TensorProduct DirectSum

variable {X Y M : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [AddCommMonoid M] [Module ℚ M]

theorem rawAlexanderWhitney_selecting_single
    (F : RawBigradedTensorChains X Y →ₗ[ℚ] M)
    {n p q : ℕ} (h : p + q = n)
    (hzero : ∀ r s : ℕ, (r, s) ≠ (p, q) → ∀ c : RawTensorChains X Y r s,
      F (rawTensorInclusion X Y r s c) = 0)
    (σ : RawSingularSimplex (X × Y) n) (a : ℚ) :
    F (rawAlexanderWhitney n (Finsupp.single σ a)) =
      a • F (rawTensorInclusion X Y p q (awPureTerm σ p q h)) := by
  classical
  rw [rawAlexanderWhitney_single, map_sum]
  simp only [map_smul]
  let z : {ij : ℕ × ℕ // ij ∈ Finset.antidiagonal n} :=
    ⟨(p, q), Finset.mem_antidiagonal.mpr h⟩
  rw [Finset.sum_eq_single z]
  · intro ij _ hne
    have hv : ij.val ≠ (p, q) := by
      intro he
      exact hne (Subtype.ext he)
    rw [hzero _ _ hv, smul_zero]
  · intro hz
    exact (hz (Finset.mem_attach _ z)).elim

theorem rawAlexanderWhitney_zero_of_summands
    (F : RawBigradedTensorChains X Y →ₗ[ℚ] M) (n : ℕ)
    (hzero : ∀ r s : ℕ, r + s = n → ∀ c : RawTensorChains X Y r s,
      F (rawTensorInclusion X Y r s c) = 0)
    (σ : RawSingularSimplex (X × Y) n) (a : ℚ) :
    F (rawAlexanderWhitney n (Finsupp.single σ a)) = 0 := by
  classical
  rw [rawAlexanderWhitney_single, map_sum]
  apply Finset.sum_eq_zero
  intro ij _
  rw [map_smul, hzero _ _ (Finset.mem_antidiagonal.mp ij.property), smul_zero]

end BanachIsometric.SingularAW

import Posets.MatrixNorm

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
open Filter Topology
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜]

theorem rowSum_le_matrixNorm (M : ScalarMatrix 𝕜) (hM : HasBoundedRows 𝕜 M) (k : ℕ) :
    (∑' n, ‖M k n‖) ≤ matrixNorm 𝕜 M := by
  apply le_ciSup _ k
  obtain ⟨C, hC⟩ := hM.2
  exact ⟨C, by rintro _ ⟨j, rfl⟩; exact hC j⟩

theorem boundedRows_of_domination {M N : ScalarMatrix 𝕜} (hN : HasBoundedRows 𝕜 N)
    (h : ∀ k n, ‖M k n‖ ≤ ‖N k n‖) : HasBoundedRows 𝕜 M := by
  have hs (k : ℕ) : Summable (fun n => ‖M k n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) (h k) (hN.1 k)
  obtain ⟨C, hC⟩ := hN.2
  exact ⟨hs, C, fun k => ((hs k).tsum_le_tsum (h k) (hN.1 k)).trans (hC k)⟩

theorem matrixNorm_le_of_domination {M N : ScalarMatrix 𝕜} (hN : HasBoundedRows 𝕜 N)
    (h : ∀ k n, ‖M k n‖ ≤ ‖N k n‖) : matrixNorm 𝕜 M ≤ matrixNorm 𝕜 N := by
  apply ciSup_le
  intro k
  exact (((boundedRows_of_domination hN h).1 k).tsum_le_tsum (h k) (hN.1 k)).trans
    (rowSum_le_matrixNorm N hN k)

theorem norm_matrixRestriction_le (M : ScalarMatrix 𝕜) (A B : Set ℕ) (k n : ℕ) :
    ‖matrixRestriction 𝕜 M A B k n‖ ≤ ‖M k n‖ := by
  by_cases h : k ∈ B ∧ n ∈ A <;> simp [matrixRestriction, h]

theorem boundedRows_matrixRestriction (M : ScalarMatrix 𝕜) (hM : HasBoundedRows 𝕜 M)
    (A B : Set ℕ) : HasBoundedRows 𝕜 (matrixRestriction 𝕜 M A B) :=
  boundedRows_of_domination hM (norm_matrixRestriction_le M A B)

theorem norm_matrixTail_le (M : ScalarMatrix 𝕜) (j k n : ℕ) :
    ‖matrixTail 𝕜 M j k n‖ ≤ ‖M k n‖ := by
  by_cases h : j < n <;> simp [matrixTail, h]

theorem boundedRows_matrixTail (M : ScalarMatrix 𝕜) (hM : HasBoundedRows 𝕜 M) (j : ℕ) :
    HasBoundedRows 𝕜 (matrixTail 𝕜 M j) :=
  boundedRows_of_domination hM (norm_matrixTail_le M j)

/-- The row norm of a matrix dominated by finitely many absolute matrices. -/
theorem matrixNorm_le_finset_sum {I : Type*} (F : Finset I) (N : I → ScalarMatrix 𝕜)
    (hN : ∀ i ∈ F, HasBoundedRows 𝕜 (N i)) (M : ScalarMatrix 𝕜) (hM : HasBoundedRows 𝕜 M)
    (h : ∀ k n, ‖M k n‖ ≤ ∑ i ∈ F, ‖N i k n‖) :
    matrixNorm 𝕜 M ≤ ∑ i ∈ F, matrixNorm 𝕜 (N i) := by
  apply ciSup_le
  intro k
  have hs : ∀ i ∈ F, Summable (fun n => ‖N i k n‖) := fun i hi => (hN i hi).1 k
  calc
    (∑' n, ‖M k n‖) ≤ ∑' n, ∑ i ∈ F, ‖N i k n‖ :=
      (hM.1 k).tsum_le_tsum (h k) (summable_sum hs)
    _ = ∑ i ∈ F, ∑' n, ‖N i k n‖ := Summable.tsum_finsetSum hs
    _ ≤ ∑ i ∈ F, matrixNorm 𝕜 (N i) :=
      Finset.sum_le_sum (fun i hi => rowSum_le_matrixNorm (N i) (hN i hi) k)

end Posets

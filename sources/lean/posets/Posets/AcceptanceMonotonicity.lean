import Posets.MatrixDomination
import Posets.SupportingStatements

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
open Filter Topology
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜] {M : ScalarMatrix 𝕜} {𝒜 ℬ : Set (Set ℕ)}

theorem acceptsPair_of_accepts (h : Accepts 𝕜 𝒜 ℬ M) {A B : Set ℕ}
    (hA : A ∈ 𝒜) (hB : B ∈ ℬ) : AcceptsPair 𝕜 A B M := by
  simpa only [Set.union_self] using h A hA A hA B hB B hB

/-- Finite unions dominate the absolute restricted matrix entry by entry. -/
theorem restrictedTail_finite_cover_bound (hM : HasBoundedRows 𝕜 M)
    (F G : Finset (Set ℕ)) (C D : Set ℕ)
    (hC : C ⊆ ⋃ A ∈ F, A) (hD : D ⊆ ⋃ B ∈ G, B) (j : ℕ) :
    matrixNorm 𝕜 (matrixTail 𝕜 (matrixRestriction 𝕜 M C D) j) ≤
      ∑ p ∈ F ×ˢ G, matrixNorm 𝕜 (matrixTail 𝕜 (matrixRestriction 𝕜 M p.1 p.2) j) := by
  apply matrixNorm_le_finset_sum (F ×ˢ G)
    (fun p => matrixTail 𝕜 (matrixRestriction 𝕜 M p.1 p.2) j)
    (fun p _ => boundedRows_matrixTail _ (boundedRows_matrixRestriction M hM p.1 p.2) j)
    _ (boundedRows_matrixTail _ (boundedRows_matrixRestriction M hM C D) j)
  intro k n
  by_cases hkn : k ∈ D ∧ n ∈ C
  · obtain ⟨A, hAF, hnA⟩ := Set.mem_iUnion₂.mp (hC hkn.2)
    obtain ⟨B, hBG, hkB⟩ := Set.mem_iUnion₂.mp (hD hkn.1)
    have heq : matrixTail 𝕜 (matrixRestriction 𝕜 M C D) j k n =
        matrixTail 𝕜 (matrixRestriction 𝕜 M A B) j k n := by
      simp [matrixTail, matrixRestriction, hkn.1, hkn.2, hkB, hnA]
    rw [heq]
    exact Finset.single_le_sum (f := fun p : Set ℕ × Set ℕ =>
      ‖matrixTail 𝕜 (matrixRestriction 𝕜 M p.1 p.2) j k n‖) (fun p _ => norm_nonneg _)
      (show (A, B) ∈ F ×ˢ G from Finset.mem_product.mpr ⟨hAF, hBG⟩)
  · have hz : matrixTail 𝕜 (matrixRestriction 𝕜 M C D) j k n = 0 := by
      simp [matrixTail, matrixRestriction, hkn]
    rw [hz, norm_zero]
    exact Finset.sum_nonneg (fun _ _ => norm_nonneg _)

theorem acceptsPair_of_finite_covers (hM : HasBoundedRows 𝕜 M) (hacc : Accepts 𝕜 𝒜 ℬ M)
    (F G : Finset (Set ℕ)) (hF : ∀ A ∈ F, A ∈ 𝒜) (hG : ∀ B ∈ G, B ∈ ℬ)
    (C D : Set ℕ) (hC : C ⊆ ⋃ A ∈ F, A) (hD : D ⊆ ⋃ B ∈ G, B) :
    AcceptsPair 𝕜 C D M := by
  refine ⟨boundedRows_matrixRestriction M hM C D, ?_⟩
  have hlim : Tendsto (fun j => ∑ p ∈ F ×ˢ G,
      matrixNorm 𝕜 (matrixTail 𝕜 (matrixRestriction 𝕜 M p.1 p.2) j)) atTop (𝓝 0) := by
    simpa using tendsto_finset_sum (F ×ˢ G) (fun p hp =>
      (acceptsPair_of_accepts hacc (hF p.1 (Finset.mem_product.mp hp).1)
        (hG p.2 (Finset.mem_product.mp hp).2)).2)
  exact squeeze_zero (fun j => matrixNorm_nonneg _
    (boundedRows_matrixTail _ (boundedRows_matrixRestriction M hM C D) j))
    (restrictedTail_finite_cover_bound hM F G C D hC hD) hlim

end Posets

import Posets.AcceptanceDichotomyDiagonal

/-! Amalgamation of the scalars attached to pairwise unions, a matrix input
to the acceptance/rejection dichotomy. Every member is explicitly infinite. -/

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
open Filter Topology
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜] {M : ScalarMatrix 𝕜} {𝒜 ℬ : Set (Set ℕ)}

theorem acceptsPair_mono {A B C D : Set ℕ} (h : AcceptsPair 𝕜 A B M)
    (hC : C ⊆ A) (hD : D ⊆ B) : AcceptsPair 𝕜 C D M := by
  apply compactMatrix_of_domination h
  intro k n
  by_cases hp : k ∈ D ∧ n ∈ C
  · simp [matrixRestriction, hp.1, hp.2, hD hp.1, hC hp.2]
  · simp [matrixRestriction, hp]

/-- Pairwise compact restrictions imply compactness after finite coverings. -/
theorem acceptsPair_of_pairwise_finite_covers (hM : HasBoundedRows 𝕜 M)
    (hacc : ∀ A ∈ 𝒜, ∀ B ∈ ℬ, AcceptsPair 𝕜 A B M)
    (F G : Finset (Set ℕ)) (hF : ∀ A ∈ F, A ∈ 𝒜) (hG : ∀ B ∈ G, B ∈ ℬ)
    (C D : Set ℕ) (hC : C ⊆ ⋃ A ∈ F, A) (hD : D ⊆ ⋃ B ∈ G, B) :
    AcceptsPair 𝕜 C D M := by
  refine ⟨boundedRows_matrixRestriction M hM C D, ?_⟩
  have hlim : Tendsto (fun j => ∑ p ∈ F ×ˢ G,
      matrixNorm 𝕜 (matrixTail 𝕜 (matrixRestriction 𝕜 M p.1 p.2) j)) atTop (𝓝 0) := by
    simpa using tendsto_finset_sum (F ×ˢ G) (fun p hp =>
      (hacc p.1 (hF p.1 (Finset.mem_product.mp hp).1)
        p.2 (hG p.2 (Finset.mem_product.mp hp).2)).2)
  exact squeeze_zero (fun j => matrixNorm_nonneg _
    (boundedRows_matrixTail _ (boundedRows_matrixRestriction M hM C D) j))
    (restrictedTail_finite_cover_bound hM F G C D hC hD) hlim

theorem accepts_of_pairwise_acceptsPair (hM : HasBoundedRows 𝕜 M)
    (hacc : ∀ A ∈ 𝒜, ∀ B ∈ ℬ, AcceptsPair 𝕜 A B M) : Accepts 𝕜 𝒜 ℬ M := by
  intro A hA A' hA' B hB B' hB'
  apply acceptsPair_of_pairwise_finite_covers hM hacc {A, A'} {B, B'}
  · intro C hC
    simp only [Finset.mem_insert, Finset.mem_singleton] at hC
    rcases hC with rfl | rfl <;> assumption
  · intro D hD
    simp only [Finset.mem_insert, Finset.mem_singleton] at hD
    rcases hD with rfl | rfl <;> assumption
  · simp
  · simp

/-- The scalar chosen on each pairwise union is the same throughout an infinite-set family. -/
theorem accepts_scalarShift_amalgamation (hM : HasBoundedRows 𝕜 M)
    (hinf : ∀ A ∈ 𝒜, A.Infinite)
    (hpair : ∀ A ∈ 𝒜, ∀ B ∈ 𝒜, ∃ a : 𝕜,
      AcceptsPair 𝕜 (A ∪ B) (A ∪ B) (M - a • identityMatrix 𝕜)) :
    ∃ a : 𝕜, Accepts 𝕜 𝒜 𝒜 (M - a • identityMatrix 𝕜) := by
  rcases 𝒜.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, fun A hA => False.elim hA⟩
  obtain ⟨A₀, hA₀⟩ := hne
  obtain ⟨a, ha⟩ := hpair A₀ hA₀ A₀ hA₀
  have ha₀ : AcceptsPair 𝕜 A₀ A₀ (M - a • identityMatrix 𝕜) := by simpa only [Set.union_self] using ha
  have hself (A : Set ℕ) (hA : A ∈ 𝒜) : AcceptsPair 𝕜 A A (M - a • identityMatrix 𝕜) := by
    obtain ⟨b, hb⟩ := hpair A₀ hA₀ A hA
    have hb₀ := acceptsPair_mono hb Set.subset_union_left Set.subset_union_left
    have hab : a = b := acceptsPair_scalarShift_unique hM (hinf A₀ hA₀) ha₀ hb₀
    subst b
    exact acceptsPair_mono hb Set.subset_union_right Set.subset_union_right
  have hunion (A : Set ℕ) (hA : A ∈ 𝒜) (B : Set ℕ) (hB : B ∈ 𝒜) :
      AcceptsPair 𝕜 (A ∪ B) (A ∪ B) (M - a • identityMatrix 𝕜) := by
    obtain ⟨b, hb⟩ := hpair A hA B hB
    have hbA := acceptsPair_mono hb Set.subset_union_left Set.subset_union_left
    have hab : a = b := acceptsPair_scalarShift_unique hM (hinf A hA) (hself A hA) hbA
    exact hab ▸ hb
  refine ⟨a, accepts_of_pairwise_acceptsPair (boundedRows_scalarShift hM a) ?_⟩
  intro A hA B hB
  exact acceptsPair_mono (hunion A hA B hB) Set.subset_union_left Set.subset_union_right

end Posets

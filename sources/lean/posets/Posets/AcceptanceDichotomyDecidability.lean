import Posets.AcceptanceDichotomyCenteredRows
import Posets.AcceptanceDichotomyNoncompactRows
import Posets.AcceptanceDichotomyAssembly

/-! Full single-set decidability and the paper's Lemma 5.2. -/

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
open Filter Topology
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜]

theorem exists_rejecting_subset_of_noncompact_offDiagonal (M : ScalarMatrix 𝕜)
    (hM : HasBoundedRows 𝕜 M) (A : Set ℕ)
    (hoff : ¬ AcceptsPair 𝕜 A A (matrixOffDiagonal M)) :
    ∃ B : Set ℕ, B ⊆ A ∧ B.Infinite ∧ Rejects 𝕜 B B M := by
  let N := matrixRestriction 𝕜 (matrixOffDiagonal M) A A
  have hN : HasBoundedRows 𝕜 N :=
    boundedRows_matrixRestriction _ (boundedRows_matrixOffDiagonal hM) A A
  obtain ⟨k, hk, b, hb, hcol, δ, hδ, hmass, hnonzero⟩ :=
    noncompactMatrix_exists_separated_row_limit N hN hoff
  have hkA (n : ℕ) : k n ∈ A := by
    obtain ⟨i, hi⟩ := hnonzero n
    by_contra hn
    exact hi (by simp [N, matrixRestriction, hn])
  have hsupport (l i : ℕ) (hi : i ∉ A) : N l i = 0 := by
    simp [N, matrixRestriction, hi]
  have hdiag : Tendsto (fun n => N (k n) (k n)) atTop (𝓝 0) := by
    simp [N, matrixRestriction, matrixOffDiagonal]
  obtain ⟨B, D, hB, hD, hBD, hrej⟩ := exists_disjoint_rejection_of_centered_rows
    N hN A hsupport k hk hkA b hb hcol hdiag hδ hmass
  have hrejM : Rejects 𝕜 B D M := by
    rintro ⟨a, ha⟩
    apply hrej
    refine ⟨a, ha.congr' ?_⟩
    filter_upwards [eventually_mem_along D] with l hl
    apply tsum_congr
    intro i
    by_cases hi : i ∈ B
    · have hli : l ≠ i := by
        rintro rfl
        exact Set.disjoint_left.mp hBD hi hl
      simp [N, matrixRestriction, matrixOffDiagonal, indicator, hi, hB hi, hD hl, hli]
    · simp [indicator, hi]
  exact exists_self_rejecting_subset_of_disjoint_rejection M hM hB hD hBD hrejM

/-- Failure of all scalar-shift acceptances yields an infinite self-rejecting
subset. This is the cited single-set decidability input to Lemma 5.2. -/
theorem exists_rejecting_subset_of_no_scalarShift (M : ScalarMatrix 𝕜)
    (hM : HasBoundedRows 𝕜 M) (A : Set ℕ)
    (hno : ¬ ∃ a : 𝕜, AcceptsPair 𝕜 A A (M - a • identityMatrix 𝕜)) :
    ∃ B : Set ℕ, B ⊆ A ∧ B.Infinite ∧ Rejects 𝕜 B B M := by
  by_cases hoff : AcceptsPair 𝕜 A A (matrixOffDiagonal M)
  · exact exists_rejecting_subset_of_compact_offDiagonal M hM A hoff hno
  · exact exists_rejecting_subset_of_noncompact_offDiagonal M hM A hoff

/-- Lemma 5.2, including both the common-scalar acceptance alternative and
continuum many pairwise disjoint pairs with infinite rejecting witnesses. -/
theorem lemma_5_2_proof (𝒜 : Set (Set ℕ)) (M : ScalarMatrix 𝕜) : Lemma_5_2 𝕜 𝒜 M := by
  intro hAD hunc hborel hM
  exact acceptance_rejection_dichotomy_of_decidability 𝒜 M
    (exists_rejecting_subset_of_no_scalarShift M hM) hAD hunc hborel hM

end Posets

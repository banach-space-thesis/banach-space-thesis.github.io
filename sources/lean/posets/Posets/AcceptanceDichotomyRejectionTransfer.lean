import Posets.AcceptanceDichotomyRejection

/-! A rejecting rectangular restriction yields a self-rejecting set. -/

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
open Filter Topology
open scoped BoundedContinuousFunction
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜]

theorem matrixAction_indicator_disjoint_union (M : ScalarMatrix 𝕜)
    (hM : HasBoundedRows 𝕜 M) {B D : Set ℕ} (hBD : Disjoint B D) (k : ℕ) :
    matrixAction 𝕜 M (indicator 𝕜 (B ∪ D)) k =
      matrixAction 𝕜 M (indicator 𝕜 B) k + matrixAction 𝕜 M (indicator 𝕜 D) k := by
  let f (A : Set ℕ) : ℕ →ᵇ 𝕜 := BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (indicator 𝕜 A) 1 (fun n => by by_cases hn : n ∈ A <;> simp [indicator, hn])
  have hpoint (n : ℕ) : indicator 𝕜 (B ∪ D) n = indicator 𝕜 B n + indicator 𝕜 D n := by
    by_cases hnB : n ∈ B <;> by_cases hnD : n ∈ D
    · exact (Set.disjoint_left.mp hBD hnB hnD).elim
    all_goals simp [indicator, hnB, hnD]
  unfold matrixAction
  simp_rw [hpoint, mul_add]
  exact (summable_matrix_row M hM (f B) k).tsum_add (summable_matrix_row M hM (f D) k)

/-- If an indicator has no limit on a disjoint output set, then either the
output set or the union of the two sets rejects the matrix on itself. -/
theorem self_rejection_of_disjoint_rejection (M : ScalarMatrix 𝕜)
    (hM : HasBoundedRows 𝕜 M) {B D : Set ℕ} (hBD : Disjoint B D)
    (hbad : Rejects 𝕜 B D M) :
    Rejects 𝕜 D D M ∨ Rejects 𝕜 (B ∪ D) (B ∪ D) M := by
  by_cases hD : Rejects 𝕜 D D M
  · exact Or.inl hD
  · right
    intro hU
    obtain ⟨a, ha⟩ := not_not.mp hD
    obtain ⟨b, hb⟩ := hU
    have hDU : Along D ≤ Along (B ∪ D) :=
      inf_le_inf_left _ (Filter.principal_mono.mpr Set.subset_union_right)
    apply hbad
    refine ⟨b - a, ((hb.mono_left hDU).sub ha).congr (fun k => ?_)⟩
    rw [matrixAction_indicator_disjoint_union M hM hBD, add_sub_cancel_right]

theorem exists_self_rejecting_subset_of_disjoint_rejection (M : ScalarMatrix 𝕜)
    (hM : HasBoundedRows 𝕜 M) {A B D : Set ℕ} (hB : B ⊆ A) (hD : D ⊆ A)
    (hBD : Disjoint B D) (hbad : Rejects 𝕜 B D M) :
    ∃ E : Set ℕ, E ⊆ A ∧ E.Infinite ∧ Rejects 𝕜 E E M := by
  rcases self_rejection_of_disjoint_rejection M hM hBD hbad with h | h
  · exact ⟨D, hD, infinite_of_not_exists_tendsto_along _ _ h, h⟩
  · exact ⟨B ∪ D, Set.union_subset hB hD,
      infinite_of_not_exists_tendsto_along _ _ h, h⟩

end Posets

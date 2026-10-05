import JFA.AmplifiedCompactMinimality
import JFA.AmplifiedXIdeal
import JFA.MainStatements

/-! The full closed-ideal classification on Y, and the kernel-checked proof
of the numbered Theorem 1.6. The fourth ideal is the actual norm closure of
factorisations through C₀(K_A); the c₀ factorisation ideal is algebraic. -/

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 8000
open TopologicalSpace Topology Set
namespace JFA
variable {𝕜 : Type*} [RCLike 𝕜] {𝒜 : Set (Set ℕ)}

theorem amplified_closedIdeal_classification (h𝒜 : IsAlmostDisjoint 𝒜)
    (hc : HasContinuumSize 𝒜) (hfew : HasFewOperators 𝕜 (MrowkaCZero 𝕜 𝒜))
    (I : Set (AmplifiedMrowka 𝕜 𝒜 →L[𝕜] AmplifiedMrowka 𝕜 𝒜)) :
    IsClosedOperatorIdeal 𝕜 (AmplifiedMrowka 𝕜 𝒜) I ↔
      I = {0} ∨ I = compactOperators 𝕜 (AmplifiedMrowka 𝕜 𝒜) ∨
      I = separableOperators 𝕜 (AmplifiedMrowka 𝕜 𝒜) ∨
      I = amplifiedCompactPreimage h𝒜 hc hfew ∨ I = Set.univ := by
  classical
  constructor
  · intro hI
    by_cases hI0 : I = {0}
    · exact Or.inl hI0
    right
    by_cases hIK : I ⊆ compactOperators 𝕜 (AmplifiedMrowka 𝕜 𝒜)
    · exact Or.inl (subset_antisymm hIK (amplified_compactOperators_minimal h𝒜 hI hI0))
    right
    have hsep : separableOperators 𝕜 (AmplifiedMrowka 𝕜 𝒜) ⊆ I := by
      rw [← amplified_factorizationOperators_eq_separableOperators h𝒜]
      exact amplified_ideal_contains_cZero_factorizations_of_not_subset_compact h𝒜 hI hIK
    exact (amplified_closedIdeal_classification_above_separable h𝒜 hc hfew I).mp ⟨hI, hsep⟩
  · rintro (rfl | rfl | rfl | rfl | rfl)
    · exact zeroOperators_closedIdeal
    · exact compactOperators_closedIdeal
    · exact separableOperators_closedIdeal
    · exact amplifiedCompactPreimage_closedIdeal h𝒜 hc hfew
    · exact allOperators_closedIdeal

theorem theorem_1_6 : Theorem_1_6 𝕜 𝒜 := by
  unfold Theorem_1_6
  intro h𝒜 hc hfew
  dsimp only
  rw [amplified_factorizationOperators_eq_separableOperators h𝒜,
    amplified_closure_X_factorizations_eq_compactPreimage h𝒜 hc hfew]
  obtain ⟨hsepK, hKU⟩ := amplified_upper_ideals_strict (𝕜 := 𝕜) h𝒜 hc hfew
  exact ⟨amplified_zero_strictly_below_compact h𝒜,
    amplified_compact_strictly_below_separable h𝒜, rfl, hsepK, hKU,
    amplified_closedIdeal_classification h𝒜 hc hfew⟩

end JFA

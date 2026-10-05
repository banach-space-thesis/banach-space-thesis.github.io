import Posets.CombinedSpaces
import PosetsCommon.CZeroSumReindex
import PosetsCommon.CountableCZero
import Mathlib.Logic.Denumerable

/-! Countable reindexing of Lemma 4.5 and the separable empty-family padding
used for zero quotient factors. -/

noncomputable section
namespace Posets
open ThesisCommon
variable {𝕜 : Type} [RCLike 𝕜]

theorem space_separable_of_countable {𝒜 : Set (Set ℕ)}
    (h𝒜 : IsAlmostDisjoint 𝒜) (hc : 𝒜.Countable) :
    TopologicalSpace.SeparableSpace (Space 𝕜 𝒜) := by
  letI : Countable 𝒜 := hc.to_subtype
  letI : Countable (Mrowka 𝒜) := inferInstanceAs (Countable (ℕ ⊕ 𝒜))
  letI := mrowka_t2 𝒜 h𝒜
  letI := mrowka_locallyCompact 𝒜 h𝒜
  exact countable_cZero_separable (Mrowka 𝒜)

theorem emptyFamily_almostDisjoint : IsAlmostDisjoint (∅ : Set (Set ℕ)) :=
  ⟨fun _ h => h.elim, fun _ h => h.elim⟩

theorem space_empty_separable : TopologicalSpace.SeparableSpace (Space 𝕜 ∅) :=
  space_separable_of_countable emptyFamily_almostDisjoint Set.countable_empty

/-- Reindex the countable topological-sum construction while retaining its
literal c₀-sum norm and the concrete almost disjoint combined family. -/
theorem exists_combined_countableSpace {I : Type} [Countable I] [Infinite I]
    (𝒜 : I → Set (Set ℕ)) (h𝒜 : ∀ i, IsAlmostDisjoint (𝒜 i)) :
    ∃ ℬ : Set (Set ℕ), IsAlmostDisjoint ℬ ∧
      Nonempty (DependentCZeroSum 𝕜 (fun i => Space 𝕜 (𝒜 i)) ≃ₗᵢ[𝕜] Space 𝕜 ℬ) := by
  let e : ℕ ≃ I := Classical.choice (inferInstance : Nonempty (ℕ ≃ I))
  obtain ⟨ℬ, hℬ, _, ⟨e₁⟩, ⟨e₂⟩⟩ := lemma_4_5_proof 𝕜 (fun n => 𝒜 (e n))
    (fun n => h𝒜 (e n))
  exact ⟨ℬ, hℬ, ⟨(cZeroSumReindexEquiv e (fun i => Space 𝕜 (𝒜 i))).symm.trans
    (e₂.symm.trans e₁.symm)⟩⟩

end Posets

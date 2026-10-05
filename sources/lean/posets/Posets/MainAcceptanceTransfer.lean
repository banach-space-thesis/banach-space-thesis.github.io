import Posets.MainWitnessFamilies
import Posets.MainOperatorScalar

/-! Transfer acceptance from the original family to its disjoint finite-cover
witnesses, with the countable exclusions needed in Section 5. -/

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜]

def FiniteFamilyCover (𝒜 : Set (Set ℕ)) (B : Set ℕ) : Prop :=
  ∃ F : Finset (Set ℕ), (∀ A ∈ F, A ∈ 𝒜) ∧ B ⊆ ⋃ A ∈ F, A

theorem FiniteFamilyCover.union {𝒜 : Set (Set ℕ)} {B C : Set ℕ}
    (hB : FiniteFamilyCover 𝒜 B) (hC : FiniteFamilyCover 𝒜 C) :
    FiniteFamilyCover 𝒜 (B ∪ C) := by
  obtain ⟨F, hF, hB⟩ := hB
  obtain ⟨G, hG, hC⟩ := hC
  refine ⟨F ∪ G, ?_, ?_⟩
  · intro A hA
    exact (Finset.mem_union.mp hA).elim (hF A) (hG A)
  · intro n hn
    rcases hn with hn | hn
    · obtain ⟨A, hA, hnA⟩ := Set.mem_iUnion₂.mp (hB hn)
      exact Set.mem_iUnion₂.mpr ⟨A, Finset.mem_union_left G hA, hnA⟩
    · obtain ⟨A, hA, hnA⟩ := Set.mem_iUnion₂.mp (hC hn)
      exact Set.mem_iUnion₂.mpr ⟨A, Finset.mem_union_right F hA, hnA⟩

theorem accepts_of_finiteFamilyCover {𝒜 ℬ 𝒞 𝒟 : Set (Set ℕ)}
    {M : ScalarMatrix 𝕜} (hM : HasBoundedRows 𝕜 M) (hacc : Accepts 𝕜 𝒜 ℬ M)
    (hC : ∀ C ∈ 𝒞, FiniteFamilyCover 𝒜 C)
    (hD : ∀ D ∈ 𝒟, FiniteFamilyCover ℬ D) : Accepts 𝕜 𝒞 𝒟 M := by
  intro C hC₁ C' hC₂ D hD₁ D' hD₂
  obtain ⟨F, hF, hCF⟩ := (hC C hC₁).union (hC C' hC₂)
  obtain ⟨G, hG, hDG⟩ := (hD D hD₁).union (hD D' hD₂)
  exact acceptsPair_of_finite_covers hM hacc F G hF hG _ _ hCF hDG

/-- The pairwise disjoint finite witnesses lose only countably many members
when a countable part of the original family is removed. -/
theorem witnessFamily_countable_cover_exclusion {ι : Type*} {𝒜 : Set (Set ℕ)}
    (F : ι → Finset (Set ℕ)) (hF : ∀ i A, A ∈ F i → A ∈ 𝒜)
    (hd : Pairwise fun i j => Disjoint (F i) (F j))
    (B : ι → Set ℕ) (hc : ∀ i, B i ⊆ ⋃ A ∈ F i, A)
    (C : Set (Set ℕ)) (hC : C.Countable) :
    ∃ D : Set (Set ℕ), D.Countable ∧
      ∀ X ∈ Set.range B \ D, FiniteFamilyCover (𝒜 \ C) X := by
  let E := {i | ∃ A ∈ F i, A ∈ C}
  refine ⟨B '' E, (disjointWitness_countable_exclusion F hd C hC).image B, ?_⟩
  rintro X ⟨⟨i, rfl⟩, hX⟩
  refine ⟨F i, ?_, hc i⟩
  intro A hA
  exact ⟨hF i A hA, fun hAC => hX ⟨i, ⟨A, hA, hAC⟩, rfl⟩⟩

/-- Acceptance outside a countable family gives both self-admission and
cross-admission outside countable families for a reduced operator matrix. -/
theorem reducedMatrix_admission_of_finite_covers {𝒜 ℬ 𝒞 : Set (Set ℕ)}
    (hbig : IsAlmostDisjoint (𝒜 ∪ ℬ))
    (T : Space 𝕜 𝒜 →L[𝕜] Space 𝕜 ℬ) (a : 𝕜)
    (hacc : Accepts 𝕜 𝒞 𝒞 (reducedMatrix 𝕜 T - a • identityMatrix 𝕜))
    (D : Set (Set ℕ)) (hD : D.Countable)
    (hcover : ∀ B ∈ (𝒜 ∪ ℬ) \ D, FiniteFamilyCover 𝒞 B) :
    ∃ E : Set (Set ℕ), E.Countable ∧
      Admits 𝕜 (𝒜 \ E) (𝒜 \ E) (reducedMatrix 𝕜 T - a • identityMatrix 𝕜) ∧
      Admits 𝕜 (𝒜 \ E) (ℬ \ E) (reducedMatrix 𝕜 T - a • identityMatrix 𝕜) := by
  let U := {B ∈ 𝒜 ∪ ℬ | Undermines 𝕜 B (reducedMatrix 𝕜 T)}
  have hU : U.Countable := reducedMatrix_undermining_countable T
    (by simpa only [Set.union_assoc, Set.union_self] using hbig)
  let E := D ∪ U
  have hM : HasBoundedRows 𝕜 (reducedMatrix 𝕜 T) :=
    ⟨reducedMatrix_row_summable T, ‖T‖, reducedMatrix_row_bound T⟩
  have hA : ∀ B ∈ 𝒜 \ E, FiniteFamilyCover 𝒞 B := by
    intro B hB
    exact hcover B ⟨Or.inl hB.1, fun h => hB.2 (Or.inl h)⟩
  have hB : ∀ B ∈ ℬ \ E, FiniteFamilyCover 𝒞 B := by
    intro B hB
    exact hcover B ⟨Or.inr hB.1, fun h => hB.2 (Or.inl h)⟩
  have hu : ∀ B ∈ (𝒜 ∪ ℬ) \ E,
      ¬ Undermines 𝕜 B (reducedMatrix 𝕜 T - a • identityMatrix 𝕜) := by
    intro B hB hu
    exact hB.2 (Or.inr ⟨hB.1, (undermines_sub_scalar_identity_iff _ a B).mp hu⟩)
  refine ⟨E, hD.union hU, ?_, ?_⟩
  · exact admits_of_accepts_not_undermines
      (accepts_of_finiteFamilyCover (boundedRows_scalarShift hM a) hacc hA hA)
      (fun B hB => hu B ⟨Or.inl hB.1, hB.2⟩)
  · exact admits_of_accepts_not_undermines
      (accepts_of_finiteFamilyCover (boundedRows_scalarShift hM a) hacc hA hB)
      (fun B hB => hu B ⟨Or.inr hB.1, hB.2⟩)

end Posets

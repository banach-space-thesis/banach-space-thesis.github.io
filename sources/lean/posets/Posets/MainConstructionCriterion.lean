import Posets.MainAcceptanceTransfer
import Posets.MainMatrixSelection
import Posets.MainStatements

/-! Complete analytic verification of the families in Section 5, conditional
on the finite-cover witnesses and their common rejection property. Existence
of those witnesses is still the separate transfinite-construction obligation. -/

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜]

theorem almostDisjoint_of_subset {𝒜 ℬ : Set (Set ℕ)}
    (h : IsAlmostDisjoint ℬ) (hs : 𝒜 ⊆ ℬ) : IsAlmostDisjoint 𝒜 :=
  ⟨fun A hA => h.1 A (hs hA), fun A hA B hB hAB => h.2 A (hs hA) B (hs hB) hAB⟩

theorem main_operator_admission_of_witnesses {ι : Type*} {𝒞 𝒜 ℬ : Set (Set ℕ)}
    (h𝒞 : IsAlmostDisjoint 𝒞) (F : ι → Finset (Set ℕ))
    (hF : ∀ i A, A ∈ F i → A ∈ 𝒞)
    (hd : Pairwise fun i j => Disjoint (F i) (F j))
    (B : ι → Set ℕ) (hB : ∀ i, (B i).Infinite) (hc : ∀ i, B i ⊆ ⋃ A ∈ F i, A)
    (hA : 𝒜 ⊆ Set.range B) (hBt : ℬ ⊆ Set.range B)
    (hreject : ∀ M : ScalarMatrix 𝕜, HasBoundedRows 𝕜 M →
      ¬ ScalarShiftAcceptedOffCountable 𝒞 M →
      ¬ {A ∈ 𝒜 ∩ ℬ | Rejects 𝕜 A A M}.Countable)
    (T : Space 𝕜 𝒜 →L[𝕜] Space 𝕜 ℬ) :
    ∃ a : 𝕜, ∃ E : Set (Set ℕ), E.Countable ∧
      Admits 𝕜 (𝒜 \ E) (𝒜 \ E) (reducedMatrix 𝕜 T - a • identityMatrix 𝕜) ∧
      Admits 𝕜 (𝒜 \ E) (ℬ \ E) (reducedMatrix 𝕜 T - a • identityMatrix 𝕜) := by
  have hg := witnessFamily_almostDisjoint h𝒞 F hF hd B hB hc
  have h𝒜 := almostDisjoint_of_subset hg hA
  have hab : 𝒜 ∪ ℬ ⊆ Set.range B := Set.union_subset hA hBt
  obtain ⟨C, hC, a, ha⟩ := reducedMatrix_scalarShiftAcceptedOffCountable h𝒜 hreject T
  obtain ⟨D, hD, hcover⟩ := witnessFamily_countable_cover_exclusion F hF hd B hc C hC
  obtain ⟨E, hE, hself, hcross⟩ := reducedMatrix_admission_of_finite_covers
    (almostDisjoint_of_subset hg hab) T a ha D hD
    (fun X hX => hcover X ⟨hab hX.1, hX.2⟩)
  exact ⟨a, E, hE, hself, hcross⟩

/-- Section 5's final operator argument, including all canonical-map laws.
This is a conditional reduction, not an existence proof for Theorem 1.1. -/
theorem theorem_1_1_of_rejection_witnesses {P : Type*} [PartialOrder P]
    {ι : Type*} {𝒞 : Set (Set ℕ)} (h𝒞 : IsAlmostDisjoint 𝒞)
    (F : ι → Finset (Set ℕ)) (hF : ∀ i A, A ∈ F i → A ∈ 𝒞)
    (hd : Pairwise fun i j => Disjoint (F i) (F j))
    (B : ι → Set ℕ) (hB : ∀ i, (B i).Infinite) (hc : ∀ i, B i ⊆ ⋃ A ∈ F i, A)
    (𝒜 : P → Set (Set ℕ)) (hA : ∀ t, 𝒜 t ⊆ Set.range B)
    (huncount : ∀ t, ¬ (𝒜 t).Countable)
    (horder : ∀ s t, s ≤ t → 𝒜 s ⊆ 𝒜 t)
    (hdiff : ∀ s t, ¬ s ≤ t → ¬ (𝒜 s \ 𝒜 t).Countable)
    (hreject : ∀ s t, ∀ M : ScalarMatrix 𝕜, HasBoundedRows 𝕜 M →
      ¬ ScalarShiftAcceptedOffCountable 𝒞 M →
      ¬ {A ∈ 𝒜 s ∩ 𝒜 t | Rejects 𝕜 A A M}.Countable) : Theorem_1_1 𝕜 P := by
  intro _
  have hg := witnessFamily_almostDisjoint h𝒞 F hF hd B hB hc
  have had (t : P) : IsAlmostDisjoint (𝒜 t) := almostDisjoint_of_subset hg (hA t)
  let j := fun s t (h : s ≤ t) => canonicalEmbedding (𝕜 := 𝕜) (horder s t h) (had t)
  refine ⟨𝒜, fun t => ⟨had t, huncount t⟩, j, ?_, ?_, ?_, ?_, ?_⟩
  · intro s t h
    exact canonicalEmbedding_isometry (horder s t h) (had t)
  · intro s
    exact canonicalEmbedding_self (had s)
  · intro r s t hrs hst
    exact canonicalEmbedding_comp (horder r s hrs) (horder s t hst) (had s) (had t)
  · intro s t h T
    obtain ⟨a, E, hE, _, hcross⟩ := main_operator_admission_of_witnesses
      h𝒞 F hF hd B hB hc (hA s) (hA t) (hreject s t) T
    obtain ⟨S, hS, heq⟩ := operator_decomposition_of_admission
      (had s) (had t) (horder s t h) T a E E hE hE hcross
    exact ⟨a, S, hS, heq⟩
  · intro s t h T
    obtain ⟨a, E, hE, hself, hcross⟩ := main_operator_admission_of_witnesses
      h𝒞 F hF hd B hB hc (hA s) (hA t) (hreject s t) T
    exact offOrder_factorization_of_admission (had s) (had t)
      (almostDisjoint_of_subset hg (Set.union_subset (hA s) (hA t))) (hdiff s t h)
      T a E E hE hE hself hcross

end Posets

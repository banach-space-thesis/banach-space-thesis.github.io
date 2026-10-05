import Posets.MainWitnessPools
import Posets.MainFamilyPartition
import Posets.MainConstructionCriterion

/-! Theorem 1.1 reduced solely to the exact acceptance/rejection dichotomy,
Lemma 5.2. All transfinite choices and operator conclusions are proved here. -/

noncomputable section
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜]

theorem theorem_1_1_of_lemma_5_2
    (hdich : ∀ M : ScalarMatrix 𝕜, Lemma_5_2 𝕜 closedTreeFamily M)
    (P : Type*) [PartialOrder P] : Theorem_1_1 𝕜 P := by
  rintro ⟨e⟩
  obtain ⟨F, B, H, C, hm, hd, hi, hs, hH, hC, hinj, hprivate, hr⟩ :=
    exists_main_rejection_witnesses hdich
  let 𝒜 := orderedPartitionFamily e H C
  have hA (t : P) : 𝒜 t ⊆ Set.range B :=
    partitionFamily_subset hH hC (commonCoordinateEmbedding e t)
  have huncount (t : P) : ¬ (𝒜 t).Countable :=
    uncountable_of_card_continuum (orderedPartitionFamily_card e H hinj t)
  have horder (s t : P) (h : s ≤ t) : 𝒜 s ⊆ 𝒜 t :=
    orderedPartitionFamily_mono e H C h
  have hdiff (s t : P) (h : ¬ s ≤ t) : ¬ (𝒜 s \ 𝒜 t).Countable :=
    uncountable_of_card_continuum (orderedPartitionFamily_diff_card e hinj hprivate h)
  have hreject (s t : P) (M : ScalarMatrix 𝕜) (hM : HasBoundedRows 𝕜 M)
      (hbad : ¬ ScalarShiftAcceptedOffCountable closedTreeFamily M) :
      ¬ {A ∈ 𝒜 s ∩ 𝒜 t | Rejects 𝕜 A A M}.Countable := by
    intro hcount
    apply hr M hM hbad
    apply hcount.mono
    intro A hA
    exact ⟨⟨Or.inl hA.1, Or.inl hA.1⟩, hA.2⟩
  exact theorem_1_1_of_rejection_witnesses closedTreeFamily_almostDisjoint
    F hm hd B hi hs 𝒜 hA huncount horder hdiff hreject ⟨e⟩

end Posets

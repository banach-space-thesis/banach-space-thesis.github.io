import Posets.MainTheoremConstruction
import Posets.ConstructionToFewOperators

/-! The main construction with its exact family cardinality retained, for
the quotient-algebra and nonisomorphism applications. -/

noncomputable section
attribute [local instance] Classical.propDecidable
namespace Posets
open Cardinal
variable {𝕜 : Type} [RCLike 𝕜]

theorem continuum_fewOperators_of_lemma_5_2
    (hdich : ∀ M : ScalarMatrix 𝕜, Lemma_5_2 𝕜 closedTreeFamily M)
    {P : Type*} [PartialOrder P] (e : P ↪o Set (Set ℕ)) :
    ∃ 𝒜 : P → Set (Set ℕ),
      (∀ t, IsAlmostDisjoint (𝒜 t) ∧ JFA.HasContinuumSize (𝒜 t)) ∧
      ∃ j : ∀ s t, Space 𝕜 (𝒜 s) →L[𝕜] Space 𝕜 (𝒜 t),
        FewOperators 𝕜 (fun t => Space 𝕜 (𝒜 t)) j := by
  obtain ⟨F, B, H, C, hm, hd, hi, hs, hH, hC, hinj, hprivate, hr⟩ :=
    exists_main_rejection_witnesses hdich
  let 𝒜 := orderedPartitionFamily e H C
  have hA (t : P) : 𝒜 t ⊆ Set.range B :=
    partitionFamily_subset hH hC (commonCoordinateEmbedding e t)
  have hglobal := witnessFamily_almostDisjoint closedTreeFamily_almostDisjoint F hm hd B hi hs
  have had (t : P) : IsAlmostDisjoint (𝒜 t) := almostDisjoint_of_subset hglobal (hA t)
  have hcard (t : P) : #(𝒜 t) = 𝔠 := orderedPartitionFamily_card e H hinj t
  have huncount (t : P) : ¬ (𝒜 t).Countable := uncountable_of_card_continuum (hcard t)
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
    intro A h
    exact ⟨⟨Or.inl h.1, Or.inl h.1⟩, h.2⟩
  let j : ∀ s t, Space 𝕜 (𝒜 s) →L[𝕜] Space 𝕜 (𝒜 t) := fun s t =>
    if h : s ≤ t then (canonicalEmbedding (𝕜 := 𝕜) (horder s t h) (had t)).toContinuousLinearMap
    else 0
  refine ⟨𝒜, fun t => ⟨had t, Cardinal.eq.mp ((hcard t).trans Cardinal.mk_set_nat.symm)⟩,
    j, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t
    exact mrowkaCZero_not_separable 𝕜 (𝒜 t) (had t) (huncount t)
  · intro s t h
    simpa only [j, dif_pos h] using canonicalEmbedding_isometry (𝕜 := 𝕜) (horder s t h) (had t)
  · intro r s t hrs hst
    simpa only [j, dif_pos hrs, dif_pos hst, dif_pos (hrs.trans hst)] using
      canonicalEmbedding_comp (𝕜 := 𝕜) (horder r s hrs) (horder s t hst) (had s) (had t)
  · intro s t h
    simp only [j, dif_neg h]
  · intro s t h T
    obtain ⟨a, E, hE, _, hcross⟩ := main_operator_admission_of_witnesses
      closedTreeFamily_almostDisjoint F hm hd B hi hs (hA s) (hA t) (hreject s t) T
    obtain ⟨S, hS, heq⟩ := operator_decomposition_of_admission
      (had s) (had t) (horder s t h) T a E E hE hE hcross
    exact ⟨a, S, hS.hasSeparableRange, by simpa only [j, dif_pos h] using heq⟩
  · intro s t h T
    obtain ⟨a, E, hE, hself, hcross⟩ := main_operator_admission_of_witnesses
      closedTreeFamily_almostDisjoint F hm hd B hi hs (hA s) (hA t) (hreject s t) T
    exact (offOrder_factorization_of_admission (had s) (had t)
      (almostDisjoint_of_subset hglobal (Set.union_subset (hA s) (hA t))) (hdiff s t h)
      T a E E hE hE hself hcross).hasSeparableRange

theorem fewOperators_nonisomorphic {P : Type*} [PartialOrder P]
    {X : P → Type*} [∀ t, NormedAddCommGroup (X t)] [∀ t, NormedSpace 𝕜 (X t)]
    {j : ∀ s t, X s →L[𝕜] X t} (h : FewOperators 𝕜 X j)
    {s t : P} (hne : s ≠ t) : ¬ Nonempty (X s ≃L[𝕜] X t) := by
  have hnot (u v : P) (huv : ¬ u ≤ v) : ¬ Nonempty (X u ≃L[𝕜] X v) := by
    rintro ⟨e⟩
    have hsep := h.2.2.2.2.2 u v huv e.toContinuousLinearMap
    change TopologicalSpace.IsSeparable (Set.range e) at hsep
    rw [e.surjective.range_eq] at hsep
    exact h.1 v (TopologicalSpace.isSeparable_univ_iff.mp hsep)
  by_cases hst : s ≤ t
  · intro he
    exact hnot t s (fun hts => hne (le_antisymm hst hts)) (he.map fun e => e.symm)
  · exact hnot s t hst

theorem corollary_1_2_of_lemma_5_2
    (hdich : ∀ M : ScalarMatrix 𝕜, Lemma_5_2 𝕜 closedTreeFamily M) : Corollary_1_2 𝕜 := by
  obtain ⟨𝒜, h𝒜, j, hj⟩ := continuum_fewOperators_of_lemma_5_2 hdich
    (OrderIso.refl (Set (Set ℕ))).toOrderEmbedding
  exact ⟨𝒜, h𝒜, fun _ _ h => fewOperators_nonisomorphic hj h⟩

end Posets

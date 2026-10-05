import Posets.SupportingStatements

/-! The natural inclusions of the actual generated Mrówka topologies.
These results do not require almost disjointness. -/
noncomputable section
open Filter Topology
namespace Posets

theorem naturalSubset_open (𝒜 : Set (Set ℕ)) (S : Set ℕ) :
    IsOpen (((Sum.inl : ℕ → Mrowka 𝒜) '' S) : Set (Mrowka 𝒜)) := by
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨n, hn, rfl⟩
  apply Filter.mem_of_superset ((isolated_open 𝒜 n).mem_nhds (Set.mem_singleton _))
  rintro p rfl
  exact ⟨n, hn, rfl⟩

theorem pointInclusion_injective {𝒜 ℬ : Set (Set ℕ)} (h : 𝒜 ⊆ ℬ) :
    Function.Injective (pointInclusion h) := by
  intro p q hpq
  cases p <;> cases q <;> simp_all [pointInclusion, JFA.Mrowka, Subtype.ext_iff]

theorem pointInclusion_image_neighborhood {𝒜 ℬ : Set (Set ℕ)} (h : 𝒜 ⊆ ℬ)
    (A : 𝒜) (F : Finset ℕ) :
    pointInclusion h '' JFA.mrowkaNeighborhood 𝒜 A F =
      JFA.mrowkaNeighborhood ℬ ⟨A.val, h A.property⟩ F := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    rcases hq with rfl | ⟨n, hn, hnF, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨n, hn, hnF, rfl⟩
  · rintro (rfl | ⟨n, hn, hnF, rfl⟩)
    · exact ⟨Sum.inr A, Or.inl rfl, rfl⟩
    · exact ⟨Sum.inl n, Or.inr ⟨n, hn, hnF, rfl⟩, rfl⟩

theorem pointInclusion_preimage_singleton {𝒜 ℬ : Set (Set ℕ)} (h : 𝒜 ⊆ ℬ)
    (n : ℕ) : pointInclusion h ⁻¹' {Sum.inl n} = {Sum.inl n} := by
  ext p
  cases p <;> simp [pointInclusion, JFA.Mrowka]

theorem pointInclusion_preimage_neighborhood_mem {𝒜 ℬ : Set (Set ℕ)} (h : 𝒜 ⊆ ℬ)
    (B : ℬ) (F : Finset ℕ) (hB : B.val ∈ 𝒜) :
    pointInclusion h ⁻¹' JFA.mrowkaNeighborhood ℬ B F =
      JFA.mrowkaNeighborhood 𝒜 ⟨B.val, hB⟩ F := by
  ext p
  cases p <;> simp [pointInclusion, JFA.Mrowka, JFA.mrowkaNeighborhood, Subtype.ext_iff]

theorem pointInclusion_preimage_neighborhood_notMem {𝒜 ℬ : Set (Set ℕ)} (h : 𝒜 ⊆ ℬ)
    (B : ℬ) (F : Finset ℕ) (hB : B.val ∉ 𝒜) :
    pointInclusion h ⁻¹' JFA.mrowkaNeighborhood ℬ B F =
      (Sum.inl : ℕ → Mrowka 𝒜) '' (B.val \ (F : Set ℕ)) := by
  ext p
  cases p with
  | inl n => simp [pointInclusion, JFA.Mrowka, JFA.mrowkaNeighborhood]
  | inr A =>
    have hne : A.val ≠ B.val := fun heq => hB (heq ▸ A.property)
    simp [pointInclusion, JFA.Mrowka, JFA.mrowkaNeighborhood, Subtype.ext_iff, hne]

theorem pointInclusion_continuous {𝒜 ℬ : Set (Set ℕ)} (h : 𝒜 ⊆ ℬ) :
    Continuous (pointInclusion h) := by
  apply continuous_generateFrom_iff.mpr
  rintro U (⟨n, rfl⟩ | ⟨B, F, rfl⟩)
  · rw [pointInclusion_preimage_singleton]
    exact isolated_open 𝒜 n
  · by_cases hB : B.val ∈ 𝒜
    · rw [pointInclusion_preimage_neighborhood_mem h B F hB]
      exact neighborhood_open 𝒜 _ F
    · rw [pointInclusion_preimage_neighborhood_notMem h B F hB]
      exact naturalSubset_open 𝒜 _

theorem pointInclusion_range_open {𝒜 ℬ : Set (Set ℕ)} (h : 𝒜 ⊆ ℬ) :
    IsOpen (Set.range (pointInclusion h)) := by
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨p, rfl⟩
  cases p with
  | inl n =>
    apply Filter.mem_of_superset ((isolated_open ℬ n).mem_nhds (Set.mem_singleton _))
    rintro q rfl
    exact ⟨Sum.inl n, rfl⟩
  | inr A =>
    apply Filter.mem_of_superset
      ((neighborhood_open ℬ ⟨A.val, h A.property⟩ ∅).mem_nhds (Or.inl rfl))
    rintro q (rfl | ⟨n, _, _, rfl⟩)
    · exact ⟨Sum.inr A, rfl⟩
    · exact ⟨Sum.inl n, rfl⟩

theorem pointInclusion_isOpenMap {𝒜 ℬ : Set (Set ℕ)} (h : 𝒜 ⊆ ℬ) :
    IsOpenMap (pointInclusion h) := by
  intro U hU
  induction hU with
  | basic U hU =>
    rcases hU with ⟨n, rfl⟩ | ⟨A, F, rfl⟩
    · simpa only [Set.image_singleton, pointInclusion] using isolated_open ℬ n
    · rw [pointInclusion_image_neighborhood]
      exact neighborhood_open ℬ _ F
  | univ => simpa only [Set.image_univ] using pointInclusion_range_open h
  | inter U V _ _ hU hV =>
    rw [Set.image_inter (pointInclusion_injective h)]
    exact hU.inter hV
  | sUnion S _ hS =>
    rw [Set.image_sUnion]
    apply isOpen_sUnion
    rintro _ ⟨U, hU, rfl⟩
    exact hS U hU

theorem pointInclusion_isOpenEmbedding {𝒜 ℬ : Set (Set ℕ)} (h : 𝒜 ⊆ ℬ) :
    IsOpenEmbedding (pointInclusion h) :=
  IsOpenEmbedding.of_continuous_injective_isOpenMap
    (pointInclusion_continuous h) (pointInclusion_injective h) (pointInclusion_isOpenMap h)

/-- Lemma 4.8, with the natural point map from the source. -/
theorem lemma_4_8_proof (𝒜 ℬ : Set (Set ℕ)) : Lemma_4_8 𝒜 ℬ := by
  intro _ _ h
  exact pointInclusion_isOpenEmbedding h

end Posets

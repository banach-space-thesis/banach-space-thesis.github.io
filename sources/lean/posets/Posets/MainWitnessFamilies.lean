import Posets.AcceptanceAdmission

/-! Disjoint finite witness families in the transfinite construction preserve
almost disjointness, and countable exclusions affect only countably many witnesses. -/

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
namespace Posets
variable {𝒜 : Set (Set ℕ)}

theorem finiteCover_inter_finite (h𝒜 : IsAlmostDisjoint 𝒜) (F G : Finset (Set ℕ))
    (hF : ∀ A ∈ F, A ∈ 𝒜) (hG : ∀ A ∈ G, A ∈ 𝒜) (hd : Disjoint F G)
    {B C : Set ℕ} (hB : B ⊆ ⋃ A ∈ F, A) (hC : C ⊆ ⋃ A ∈ G, A) : (B ∩ C).Finite := by
  have hf : (⋃ A : F, ⋃ D : G, (A.val ∩ D.val)).Finite := by
    apply Set.finite_iUnion
    intro A
    apply Set.finite_iUnion
    intro D
    exact h𝒜.2 A.val (hF A.val A.property) D.val (hG D.val D.property)
      (fun h => Finset.disjoint_left.mp hd A.property (h ▸ D.property))
  apply hf.subset
  intro n hn
  obtain ⟨A, hAF, hnA⟩ := Set.mem_iUnion₂.mp (hB hn.1)
  obtain ⟨D, hDG, hnD⟩ := Set.mem_iUnion₂.mp (hC hn.2)
  exact Set.mem_iUnion.mpr ⟨⟨A, hAF⟩, Set.mem_iUnion.mpr ⟨⟨D, hDG⟩, hnA, hnD⟩⟩

variable {ι : Type*}

theorem witnessFamily_injective (h𝒜 : IsAlmostDisjoint 𝒜) (F : ι → Finset (Set ℕ))
    (hF : ∀ i A, A ∈ F i → A ∈ 𝒜) (hd : Pairwise fun i j => Disjoint (F i) (F j))
    (B : ι → Set ℕ) (hB : ∀ i, (B i).Infinite) (hc : ∀ i, B i ⊆ ⋃ A ∈ F i, A) :
    Function.Injective B := by
  intro i j he
  by_contra hij
  have hf := finiteCover_inter_finite h𝒜 (F i) (F j) (hF i) (hF j) (hd hij) (hc i) (hc j)
  exact hB i (by simpa only [← he, Set.inter_self] using hf)

theorem witnessFamily_almostDisjoint (h𝒜 : IsAlmostDisjoint 𝒜) (F : ι → Finset (Set ℕ))
    (hF : ∀ i A, A ∈ F i → A ∈ 𝒜) (hd : Pairwise fun i j => Disjoint (F i) (F j))
    (B : ι → Set ℕ) (hB : ∀ i, (B i).Infinite) (hc : ∀ i, B i ⊆ ⋃ A ∈ F i, A) :
    IsAlmostDisjoint (Set.range B) := by
  constructor
  · rintro _ ⟨i, rfl⟩
    exact hB i
  · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hne
    have hij : i ≠ j := fun h => hne (h ▸ rfl)
    exact finiteCover_inter_finite h𝒜 (F i) (F j) (hF i) (hF j) (hd hij) (hc i) (hc j)

/-- A countable source exclusion spoils only countably many disjoint witnesses. -/
theorem disjointWitness_countable_exclusion {α : Type*} (F : ι → Finset α)
    (hd : Pairwise fun i j => Disjoint (F i) (F j)) (C : Set α) (hC : C.Countable) :
    {i | ∃ a ∈ F i, a ∈ C}.Countable := by
  letI : Countable C := hC.to_subtype
  have hf (a : C) : {i | a.val ∈ F i}.Subsingleton := by
    intro i hi j hj
    by_contra hij
    exact Finset.disjoint_left.mp (hd hij) hi hj
  apply (Set.countable_iUnion (fun a : C => (hf a).countable)).mono
  rintro i ⟨a, ha, hAC⟩
  exact Set.mem_iUnion.mpr ⟨⟨a, hAC⟩, ha⟩

end Posets

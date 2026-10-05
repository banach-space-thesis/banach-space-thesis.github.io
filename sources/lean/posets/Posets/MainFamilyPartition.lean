import Posets.PosetEmbedding
import Mathlib.SetTheory.Cardinal.Continuum

/-! The common and private parts of the families in Section 5. A private
coordinate has continuum many members. This makes every missing coordinate
give an uncountable difference, with no restriction on the size of the poset. -/

noncomputable section
namespace Posets
open Cardinal

def partitionFamily (H : Set (Set ℕ)) (C : Set ℕ × Set ℕ → Set ℕ)
    (S : Set (Set ℕ)) : Set (Set ℕ) :=
  H ∪ {A | ∃ α ∈ S, ∃ β, C (α, β) = A}

theorem common_subset_partitionFamily (H : Set (Set ℕ)) (C : Set ℕ × Set ℕ → Set ℕ)
    (S : Set (Set ℕ)) : H ⊆ partitionFamily H C S := Set.subset_union_left

theorem partitionFamily_mono (H : Set (Set ℕ)) (C : Set ℕ × Set ℕ → Set ℕ)
    {S T : Set (Set ℕ)} (h : S ⊆ T) : partitionFamily H C S ⊆ partitionFamily H C T := by
  rintro A (hA | ⟨α, hα, β, rfl⟩)
  · exact Or.inl hA
  · exact Or.inr ⟨α, h hα, β, rfl⟩

theorem partitionFamily_subset {H W : Set (Set ℕ)} {C : Set ℕ × Set ℕ → Set ℕ}
    (hH : H ⊆ W) (hC : Set.range C ⊆ W) (S : Set (Set ℕ)) :
    partitionFamily H C S ⊆ W := by
  rintro A (hA | ⟨α, _, β, rfl⟩)
  · exact hH hA
  · exact hC ⟨(α, β), rfl⟩

theorem continuum_le_of_private_fiber {W : Set (Set ℕ)}
    {C : Set ℕ × Set ℕ → Set ℕ} (hinj : Function.Injective C) (α : Set ℕ)
    (h : ∀ β, C (α, β) ∈ W) : 𝔠 ≤ #W := by
  rw [← Cardinal.mk_set_nat]
  exact Cardinal.mk_le_of_injective (f := fun β => (⟨C (α, β), h β⟩ : W))
    (fun β γ heq => (Prod.mk.inj (hinj (congrArg Subtype.val heq))).2)

theorem partitionFamily_card {H : Set (Set ℕ)} {C : Set ℕ × Set ℕ → Set ℕ}
    (hinj : Function.Injective C) {S : Set (Set ℕ)} (hne : S.Nonempty) :
    #(partitionFamily H C S) = 𝔠 := by
  apply le_antisymm
  · simpa only [Cardinal.mk_set_nat] using Cardinal.mk_set_le (partitionFamily H C S)
  · obtain ⟨α, hα⟩ := hne
    exact continuum_le_of_private_fiber hinj α (fun β => Or.inr ⟨α, hα, β, rfl⟩)

theorem partitionFamily_diff_card {H : Set (Set ℕ)} {C : Set ℕ × Set ℕ → Set ℕ}
    (hinj : Function.Injective C) (hprivate : ∀ α β, C (α, β) ∉ H)
    {S T : Set (Set ℕ)} (h : ¬ S ⊆ T) :
    #↥(partitionFamily H C S \ partitionFamily H C T) = 𝔠 := by
  classical
  obtain ⟨α, hα, hαT⟩ := Set.not_subset.mp h
  apply le_antisymm
  · simpa only [Cardinal.mk_set_nat] using
      Cardinal.mk_set_le (partitionFamily H C S \ partitionFamily H C T)
  · apply continuum_le_of_private_fiber hinj α
    intro β
    refine ⟨Or.inr ⟨α, hα, β, rfl⟩, ?_⟩
    rintro (hH | ⟨γ, hγ, δ, heq⟩)
    · exact hprivate α β hH
    · exact hαT ((Prod.mk.inj (hinj heq)).1 ▸ hγ)

theorem uncountable_of_card_continuum {W : Set (Set ℕ)} (h : #W = 𝔠) :
    ¬ W.Countable := by
  intro hW
  exact Cardinal.aleph0_lt_continuum.not_ge (h ▸ hW.le_aleph0)

def orderedPartitionFamily {P : Type*} [PartialOrder P]
    (e : P ↪o Set (Set ℕ)) (H : Set (Set ℕ)) (C : Set ℕ × Set ℕ → Set ℕ)
    (t : P) : Set (Set ℕ) := partitionFamily H C (commonCoordinateEmbedding e t)

theorem orderedPartitionFamily_mono {P : Type*} [PartialOrder P]
    (e : P ↪o Set (Set ℕ)) (H : Set (Set ℕ)) (C : Set ℕ × Set ℕ → Set ℕ)
    {s t : P} (h : s ≤ t) : orderedPartitionFamily e H C s ⊆ orderedPartitionFamily e H C t :=
  partitionFamily_mono H C ((commonCoordinateEmbedding e).monotone h)

theorem orderedPartitionFamily_card {P : Type*} [PartialOrder P]
    (e : P ↪o Set (Set ℕ)) (H : Set (Set ℕ)) {C : Set ℕ × Set ℕ → Set ℕ}
    (hinj : Function.Injective C) (t : P) : #(orderedPartitionFamily e H C t) = 𝔠 :=
  partitionFamily_card hinj ⟨∅, commonCoordinateEmbedding_mem e t⟩

theorem orderedPartitionFamily_diff_card {P : Type*} [PartialOrder P]
    (e : P ↪o Set (Set ℕ)) {H : Set (Set ℕ)} {C : Set ℕ × Set ℕ → Set ℕ}
    (hinj : Function.Injective C) (hprivate : ∀ α β, C (α, β) ∉ H)
    {s t : P} (h : ¬ s ≤ t) :
    #↥(orderedPartitionFamily e H C s \ orderedPartitionFamily e H C t) = 𝔠 := by
  apply partitionFamily_diff_card hinj hprivate
  exact fun hst => h ((commonCoordinateEmbedding e).le_iff_le.mp hst)

end Posets

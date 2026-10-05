import ThesisCommon.Analysis.BooleanAdjoin

/-! Boolean extensions whose new freedom is confined to one supporting set. -/
noncomputable section
open Set
namespace ThesisCommon

/-- Outside C, every member agrees with a member of the old algebra. Inside C
there is no restriction. This larger algebra controls both pieces of a split. -/
def localizedAlgebra {α : Type*} (B : BooleanSubalgebra (Set α)) (C : Set α) :
    BooleanSubalgebra (Set α) where
  carrier := {s | ∃ A : Set α, ∃ D ∈ B, s = (A ∩ C) ∪ (D \ C)}
  supClosed' := by
    rintro _ ⟨A, D, hD, rfl⟩ _ ⟨A', D', hD', rfl⟩
    refine ⟨A ∪ A', D ∪ D', B.sup_mem hD hD', ?_⟩
    ext x
    simp only [Set.sup_eq_union, Set.mem_union, Set.mem_inter_iff, Set.mem_diff]
    tauto
  infClosed' := by
    rintro _ ⟨A, D, hD, rfl⟩ _ ⟨A', D', hD', rfl⟩
    refine ⟨A ∩ A', D ∩ D', B.inf_mem hD hD', ?_⟩
    ext x
    simp only [Set.inf_eq_inter, Set.mem_union, Set.mem_inter_iff, Set.mem_diff]
    tauto
  compl_mem' := by
    rintro _ ⟨A, D, hD, rfl⟩
    refine ⟨Aᶜ, Dᶜ, B.compl_mem hD, ?_⟩
    ext x
    simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_inter_iff, Set.mem_diff]
    tauto
  bot_mem' := ⟨∅, ∅, B.bot_mem, by simp⟩

theorem le_localizedAlgebra {α : Type*} (B : BooleanSubalgebra (Set α)) (C : Set α) :
    B ≤ localizedAlgebra B C := by
  intro D hD
  refine ⟨D, D, hD, ?_⟩
  ext x
  simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_diff]
  tauto

theorem subset_mem_localizedAlgebra {α : Type*} (B : BooleanSubalgebra (Set α))
    {A C : Set α} (hA : A ⊆ C) : A ∈ localizedAlgebra B C := by
  exact ⟨A, ∅, B.bot_mem, by simp [Set.inter_eq_left.mpr hA]⟩

theorem adjoin_le_of_mem {α : Type*} {B D : BooleanSubalgebra (Set α)} {Z : Set α}
    (hB : B ≤ D) (hZ : Z ∈ D) : adjoinSet B Z ≤ D := by
  apply BooleanSubalgebra.closure_le.mpr
  rintro A (hA | rfl)
  · exact hB hA
  · exact hZ

/-- Both halves, and therefore their supporting cylinder, are included. -/
theorem adjoin_split_le_localized {α : Type*} (B : BooleanSubalgebra (Set α))
    {Z C : Set α} (hZ : Z ⊆ C) :
    adjoinSet (adjoinSet B Z) (C \ Z) ≤ localizedAlgebra B C :=
  adjoin_le_of_mem
    (adjoin_le_of_mem (le_localizedAlgebra B C) (subset_mem_localizedAlgebra B hZ))
    (subset_mem_localizedAlgebra B Set.diff_subset)

end ThesisCommon

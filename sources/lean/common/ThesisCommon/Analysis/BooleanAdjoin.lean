import Mathlib.Order.BooleanSubalgebra
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.Tactic

/-! Normal form after adjoining one set to a Boolean algebra. -/
noncomputable section
open Set Cardinal
namespace ThesisCommon

def adjoinSet {α : Type*} (B : BooleanSubalgebra (Set α)) (Z : Set α) :
    BooleanSubalgebra (Set α) := BooleanSubalgebra.closure ((B : Set (Set α)) ∪ {Z})

def splitFormAlgebra {α : Type*} (B : BooleanSubalgebra (Set α)) (Z : Set α) :
    BooleanSubalgebra (Set α) where
  carrier := {s | ∃ A ∈ B, ∃ D ∈ B, s = (A ∩ Z) ∪ (D \ Z)}
  supClosed' := by
    rintro _ ⟨A, hA, D, hD, rfl⟩ _ ⟨A', hA', D', hD', rfl⟩
    refine ⟨A ∪ A', B.sup_mem hA hA', D ∪ D', B.sup_mem hD hD', ?_⟩
    ext x
    simp only [Set.sup_eq_union, Set.mem_union, Set.mem_inter_iff, Set.mem_diff]
    tauto
  infClosed' := by
    rintro _ ⟨A, hA, D, hD, rfl⟩ _ ⟨A', hA', D', hD', rfl⟩
    refine ⟨A ∩ A', B.inf_mem hA hA', D ∩ D', B.inf_mem hD hD', ?_⟩
    ext x
    simp only [Set.inf_eq_inter, Set.mem_union, Set.mem_inter_iff, Set.mem_diff]
    tauto
  compl_mem' := by
    rintro _ ⟨A, hA, D, hD, rfl⟩
    refine ⟨Aᶜ, B.compl_mem hA, Dᶜ, B.compl_mem hD, ?_⟩
    ext x
    simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_inter_iff, Set.mem_diff]
    tauto
  bot_mem' := ⟨∅, B.bot_mem, ∅, B.bot_mem, by simp⟩

theorem mem_adjoinSet_iff {α : Type*} (B : BooleanSubalgebra (Set α)) (Z s : Set α) :
    s ∈ adjoinSet B Z ↔ ∃ A ∈ B, ∃ D ∈ B, s = (A ∩ Z) ∪ (D \ Z) := by
  have hB : B ≤ adjoinSet B Z := fun A hA => BooleanSubalgebra.subset_closure (Or.inl hA)
  have hZ : Z ∈ adjoinSet B Z := BooleanSubalgebra.subset_closure (Or.inr rfl)
  constructor
  · apply (show adjoinSet B Z ≤ splitFormAlgebra B Z from ?_)
    apply BooleanSubalgebra.closure_le.mpr
    rintro A (hA | hA)
    · refine ⟨A, hA, A, hA, ?_⟩
      ext x
      simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_diff]
      tauto
    · rcases hA with rfl
      exact ⟨Set.univ, B.top_mem, ∅, B.bot_mem, by simp⟩
  · rintro ⟨A, hA, D, hD, rfl⟩
    exact (adjoinSet B Z).sup_mem ((adjoinSet B Z).inf_mem (hB hA) hZ)
      ((adjoinSet B Z).sdiff_mem (hB hD) hZ)

theorem adjoinSet_cardinal_le {α : Type*} (B : BooleanSubalgebra (Set α)) (Z : Set α) :
    #(adjoinSet B Z) ≤ #B * #B := by
  let f : B × B → adjoinSet B Z := fun p =>
    ⟨(p.1.val ∩ Z) ∪ (p.2.val \ Z),
      (mem_adjoinSet_iff B Z _).mpr ⟨_, p.1.property, _, p.2.property, rfl⟩⟩
  have hf : Function.Surjective f := by
    intro s
    obtain ⟨A, hA, D, hD, heq⟩ := (mem_adjoinSet_iff B Z s.val).mp s.property
    exact ⟨(⟨A, hA⟩, ⟨D, hD⟩), Subtype.ext heq.symm⟩
  simpa using Cardinal.mk_le_of_surjective hf

end ThesisCommon

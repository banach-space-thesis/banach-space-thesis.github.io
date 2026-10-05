import ThesisCommon.Analysis.FiniteSeparation
import Mathlib.Order.Directed

/-! Uniform finite-test separation is detected at a stage of a directed union. -/
noncomputable section
namespace ThesisCommon

theorem finite_subset_directed_union {α I : Type*} [Nonempty I]
    (S : I → Set α) (hdir : Directed (· ⊆ ·) S) (F : Finset α)
    (hF : (↑F : Set α) ⊆ ⋃ i, S i) : ∃ i, (↑F : Set α) ⊆ S i := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨Classical.arbitrary I, by simp⟩
  | @insert a F ha ih =>
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hF (Finset.mem_insert_self a F))
    obtain ⟨j, hj⟩ := ih (fun x hx => hF (by simp [hx]))
    obtain ⟨k, hik, hjk⟩ := hdir i j
    refine ⟨k, ?_⟩
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hik hi
    · exact hjk (hj hx)

theorem finitelySeparated_directed_union_iff {D T I : Type*} [Nonempty I]
    (ev : D → T → ℝ) (S : I → Set T) (hdir : Directed (· ⊆ ·) S) (M N : Set D) :
    FinitelySeparated ev (⋃ i, S i) M N ↔ ∃ i, FinitelySeparated ev (S i) M N := by
  constructor
  · rintro ⟨ε, hε, F, hF, hgap⟩
    obtain ⟨i, hi⟩ := finite_subset_directed_union S hdir F hF
    exact ⟨i, ε, hε, F, hi, hgap⟩
  · rintro ⟨i, hi⟩
    exact finitelySeparated_mono_tests (Set.subset_iUnion S i) hi

end ThesisCommon

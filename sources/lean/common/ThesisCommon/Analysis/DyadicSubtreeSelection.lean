import ThesisCommon.Analysis.DyadicSubtreeEmbeddings
import Mathlib.Data.Finset.Basic

/-! Genuine monochromatic dyadic subtree selection, including finite covers.
The construction chooses nodes beyond each split when a colour is cofinal;
otherwise an entire cone has the opposite colour. -/
noncomputable section
namespace ThesisCommon

theorem exists_dyadic_subtree_of_cofinal (A : Set DyadicTreeNode)
    (hA : ∀ u : DyadicTreeNode, ∃ v, u.IsPrefix v ∧ v ∈ A) :
    ∃ e : DyadicSubtreeEmbedding, ∀ s, e s ∈ A := by
  classical
  let chooseNode (u : DyadicTreeNode) := Classical.choose (hA u)
  have hc (u) : u.IsPrefix (chooseNode u) ∧ chooseNode u ∈ A := Classical.choose_spec (hA u)
  let step (u : DyadicTreeNode) (b : Bool) := chooseNode (u ++ [b])
  let e := dyadicExpansionEmbedding step id (fun u b => (hc (u ++ [b])).1) (chooseNode [])
  refine ⟨e, ?_⟩
  intro s
  change s.foldl step (chooseNode []) ∈ A
  have hfold : ∀ s : DyadicTreeNode, ∀ u ∈ A, s.foldl step u ∈ A := by
    intro s
    induction s with
    | nil => exact fun _ hu => hu
    | cons b s ih => exact fun u _ => ih (step u b) (hc (u ++ [b])).2
  exact hfold s _ (hc []).2

theorem exists_monochromatic_dyadic_subtree (A : Set DyadicTreeNode) :
    ∃ e : DyadicSubtreeEmbedding, (∀ s, e s ∈ A) ∨ (∀ s, e s ∉ A) := by
  classical
  by_cases hA : ∀ u : DyadicTreeNode, ∃ v, u.IsPrefix v ∧ v ∈ A
  · obtain ⟨e, he⟩ := exists_dyadic_subtree_of_cofinal A hA
    exact ⟨e, Or.inl he⟩
  · push_neg at hA
    obtain ⟨u, hu⟩ := hA
    refine ⟨DyadicSubtreeEmbedding.cone u, Or.inr ?_⟩
    intro s
    exact hu _ (List.prefix_append u s)

theorem exists_dyadic_subtree_in_finite_cover {ι : Type*} (s : Finset ι)
    (P : ι → DyadicTreeNode → Prop) (hcover : ∀ t, ∃ i ∈ s, P i t) :
    ∃ i ∈ s, ∃ e : DyadicSubtreeEmbedding, ∀ t, P i (e t) := by
  classical
  induction s using Finset.induction_on generalizing P with
  | empty => simpa using hcover []
  | @insert i s hi ih =>
    obtain ⟨e, he | he⟩ := exists_monochromatic_dyadic_subtree {t | P i t}
    · exact ⟨i, Finset.mem_insert_self _ _, e, he⟩
    · have hc : ∀ t, ∃ j ∈ s, P j (e t) := by
        intro t
        obtain ⟨j, hj, hP⟩ := hcover (e t)
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact (he t hP).elim
        · exact ⟨j, hj, hP⟩
      obtain ⟨j, hj, g, hg⟩ := ih (fun j t => P j (e t)) hc
      exact ⟨j, Finset.mem_insert_of_mem hj, e.comp g, hg⟩

end ThesisCommon

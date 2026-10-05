import ThesisCommon.Analysis.DyadicTreeFrontiers

/-! Explicit membership and cardinality facts for the finite frontier
updates used by a node-by-node operator construction. -/
noncomputable section
namespace ThesisCommon

theorem dyadicTreeFrontier_survivor_mem (n : ℕ) {t : DyadicTreeNode}
    (ht : t ∈ dyadicTreeFrontier n) (hne : t ≠ dyadicTreeEnumeration n) :
    t ∈ dyadicTreeFrontier (n + 1) := by
  rw [dyadicTreeFrontier_succ]
  exact Finset.mem_union.mpr (Or.inl (Finset.mem_erase.mpr ⟨hne,ht⟩))

theorem dyadicTreeFrontier_child_mem (n : ℕ) (b : Bool) :
    dyadicTreeEnumeration n ++ [b] ∈ dyadicTreeFrontier (n + 1) := by
  rw [dyadicTreeFrontier_succ]
  apply Finset.mem_union.mpr
  right
  cases b <;> simp

theorem dyadicTreeFrontier_child_not_mem (n : ℕ) (b : Bool) :
    dyadicTreeEnumeration n ++ [b] ∉ dyadicTreeFrontier n := by
  intro ht
  have hne : dyadicTreeEnumeration n ≠ dyadicTreeEnumeration n ++ [b] := by
    intro h
    have hh := congrArg List.length h
    simp only [List.length_append,List.length_singleton] at hh
    omega
  exact dyadicTreeFrontier_antichain n (dyadicTreeEnumeration_mem_frontier n) ht hne
    (List.prefix_append _ _)

theorem mem_dyadicTreeFrontier_succ_iff (n : ℕ) (t : DyadicTreeNode) :
    t ∈ dyadicTreeFrontier (n + 1) ↔
      (t ∈ dyadicTreeFrontier n ∧ t ≠ dyadicTreeEnumeration n) ∨
      ∃ b : Bool, t = dyadicTreeEnumeration n ++ [b] := by
  rw [dyadicTreeFrontier_succ,Finset.mem_union,Finset.mem_erase]
  constructor
  · rintro (⟨hne,ht⟩ | ht)
    · exact Or.inl ⟨ht,hne⟩
    · rcases Finset.mem_insert.mp ht with h | h
      · exact Or.inr ⟨false,h⟩
      · exact Or.inr ⟨true,Finset.mem_singleton.mp h⟩
  · rintro (⟨ht,hne⟩ | ⟨b,rfl⟩)
    · exact Or.inl ⟨hne,ht⟩
    · right
      cases b <;> simp

theorem card_dyadicTreeFrontier (n : ℕ) : (dyadicTreeFrontier n).card = n + 1 := by
  induction n with
  | zero => simp only [dyadicTreeFrontier_zero,Finset.card_singleton]
  | succ n ih =>
    have hne : dyadicTreeEnumeration n ++ [false] ≠ dyadicTreeEnumeration n ++ [true] := by
      intro h
      have hh := List.append_cancel_left h
      simp only [List.cons.injEq,Bool.false_eq_true,false_and] at hh
    have hd : Disjoint ((dyadicTreeFrontier n).erase (dyadicTreeEnumeration n))
        {dyadicTreeEnumeration n ++ [false],dyadicTreeEnumeration n ++ [true]} := by
      apply Finset.disjoint_left.mpr
      intro t ht hu
      have htold := (Finset.mem_erase.mp ht).2
      rcases Finset.mem_insert.mp hu with rfl | h
      · exact dyadicTreeFrontier_child_not_mem n false htold
      · have h := Finset.mem_singleton.mp h
        exact dyadicTreeFrontier_child_not_mem n true (h ▸ htold)
    rw [dyadicTreeFrontier_succ,Finset.card_union_of_disjoint hd,
      Finset.card_erase_of_mem (dyadicTreeEnumeration_mem_frontier n),ih,Finset.card_pair hne]
    omega

end ThesisCommon

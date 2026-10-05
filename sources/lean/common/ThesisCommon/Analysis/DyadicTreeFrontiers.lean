import ThesisCommon.Analysis.DyadicTreeFrontierOrder

/-! Genuine finite frontiers for breadth-first processing of the binary
tree. Each update removes the current node and adds its two children. The
membership theorem identifies these finite sets intrinsically as the
unprocessed nodes all of whose proper prefixes have been processed. -/
noncomputable section
namespace ThesisCommon

def dyadicTreeFrontier : ℕ → Finset DyadicTreeNode
  | 0 => {[]}
  | n + 1 => (dyadicTreeFrontier n).erase (dyadicTreeEnumeration n) ∪
      {dyadicTreeEnumeration n ++ [false], dyadicTreeEnumeration n ++ [true]}

@[simp] theorem dyadicTreeFrontier_zero : dyadicTreeFrontier 0 = {[]} := rfl

theorem dyadicTreeFrontier_succ (n : ℕ) :
    dyadicTreeFrontier (n + 1) =
      (dyadicTreeFrontier n).erase (dyadicTreeEnumeration n) ∪
      {dyadicTreeEnumeration n ++ [false], dyadicTreeEnumeration n ++ [true]} := rfl

theorem mem_dyadicTreeFrontier (n : ℕ) (t : DyadicTreeNode) :
    t ∈ dyadicTreeFrontier n ↔ n ≤ dyadicTreeEnumeration.symm t ∧
      ∀ s, s.IsPrefix t → s ≠ t → dyadicTreeEnumeration.symm s < n := by
  induction n generalizing t with
  | zero =>
    constructor
    · intro ht
      have ht0 : t = [] := by simpa only [dyadicTreeFrontier_zero,Finset.mem_singleton] using ht
      subst t
      refine ⟨Nat.zero_le _,?_⟩
      intro s hs hne
      exact (hne (List.eq_nil_of_prefix_nil hs)).elim
    · intro ht
      have ht0 : t = [] := by
        by_contra hne
        have hh := ht.2 [] List.nil_prefix (Ne.symm hne)
        omega
      simp only [ht0,dyadicTreeFrontier_zero,Finset.mem_singleton]
  | succ n ih =>
    rw [dyadicTreeFrontier_succ,Finset.mem_union,Finset.mem_erase,Finset.mem_insert,Finset.mem_singleton]
    constructor
    · rintro (⟨hne,ht⟩ | hchild)
      · obtain ⟨hidx,hproper⟩ := (ih t).mp ht
        have hidxne : dyadicTreeEnumeration.symm t ≠ n := by
          intro he
          apply hne
          simpa only [Equiv.apply_symm_apply] using congrArg dyadicTreeEnumeration he
        exact ⟨by omega,fun s hs hst => (hproper s hs hst).trans_le (Nat.le_succ n)⟩
      · have hb : ∃ b : Bool, t = dyadicTreeEnumeration n ++ [b] := by
          rcases hchild with h | h
          · exact ⟨false,h⟩
          · exact ⟨true,h⟩
        obtain ⟨b,rfl⟩ := hb
        have hidx := dyadicTreeEnumeration_child_index (dyadicTreeEnumeration n) b
        simp only [Equiv.symm_apply_apply] at hidx
        refine ⟨hidx,?_⟩
        intro s hs hne
        have hh := dyadicTreeEnumeration_prefix_index (dyadic_proper_prefix_of_child hs hne)
        simpa only [Equiv.symm_apply_apply] using Nat.lt_succ_of_le hh
    · rintro ⟨hidx,hproper⟩
      by_cases hnt : (dyadicTreeEnumeration n).IsPrefix t
      · have hne : dyadicTreeEnumeration n ≠ t := by
          intro h
          rw [←h,Equiv.symm_apply_apply] at hidx
          omega
        obtain ⟨b,hb⟩ := exists_dyadic_child_prefix_of_strict_prefix hnt hne
        have hbt : dyadicTreeEnumeration n ++ [b] = t := by
          by_contra hbne
          have hh := hproper _ hb hbne
          have hlt := dyadicTreeEnumeration_child_index (dyadicTreeEnumeration n) b
          simp only [Equiv.symm_apply_apply] at hlt
          omega
        right
        cases b
        · exact Or.inl hbt.symm
        · exact Or.inr hbt.symm
      · left
        refine ⟨fun h => hnt (h ▸ List.prefix_rfl), (ih t).mpr ⟨by omega,?_⟩⟩
        intro s hs hne
        have hh := hproper s hs hne
        have hsn : dyadicTreeEnumeration.symm s ≠ n := by
          intro he
          have hse : s = dyadicTreeEnumeration n := by
            simpa only [Equiv.apply_symm_apply] using congrArg dyadicTreeEnumeration he
          exact hnt (hse ▸ hs)
        omega

theorem dyadicTreeEnumeration_mem_frontier (n : ℕ) :
    dyadicTreeEnumeration n ∈ dyadicTreeFrontier n := by
  apply (mem_dyadicTreeFrontier n _).mpr
  refine ⟨by simp only [Equiv.symm_apply_apply,le_refl],?_⟩
  intro s hs hne
  simpa only [Equiv.symm_apply_apply] using dyadicTreeEnumeration_strict_prefix_index hs hne

theorem dyadicTreeFrontier_antichain (n : ℕ) {s t : DyadicTreeNode}
    (hs : s ∈ dyadicTreeFrontier n) (ht : t ∈ dyadicTreeFrontier n) (hne : s ≠ t) :
    ¬ s.IsPrefix t := by
  intro hst
  exact (not_lt_of_ge ((mem_dyadicTreeFrontier n s).mp hs).1)
    (((mem_dyadicTreeFrontier n t).mp ht).2 s hst hne)

theorem exists_dyadicTreeFrontier_prefix (n : ℕ) (t : DyadicTreeNode)
    (ht : n ≤ dyadicTreeEnumeration.symm t) :
    ∃ s, s ∈ dyadicTreeFrontier n ∧ s.IsPrefix t := by
  induction t using List.reverseRecOn with
  | nil =>
    have hn : n = 0 := by simpa only [dyadicTreeEnumeration_index_nil,Nat.le_zero] using ht
    subst n
    exact ⟨[],by simp only [dyadicTreeFrontier_zero,Finset.mem_singleton],List.prefix_rfl⟩
  | append_singleton t b ih =>
    by_cases hparent : n ≤ dyadicTreeEnumeration.symm t
    · obtain ⟨s,hs,hst⟩ := ih hparent
      exact ⟨s,hs,hst.trans (List.prefix_append t [b])⟩
    · refine ⟨t ++ [b], (mem_dyadicTreeFrontier n _).mpr ⟨ht,?_⟩,List.prefix_rfl⟩
      intro s hs hne
      exact (dyadicTreeEnumeration_prefix_index (dyadic_proper_prefix_of_child hs hne)).trans_lt
        (Nat.lt_of_not_ge hparent)

theorem existsUnique_dyadicTreeFrontier_prefix (n : ℕ) (t : DyadicTreeNode)
    (ht : n ≤ dyadicTreeEnumeration.symm t) :
    ∃! s, s ∈ dyadicTreeFrontier n ∧ s.IsPrefix t := by
  obtain ⟨s,hs,hst⟩ := exists_dyadicTreeFrontier_prefix n t ht
  refine ⟨s,⟨hs,hst⟩,?_⟩
  rintro r ⟨hr,hrt⟩
  by_contra hne
  exact (List.prefix_or_prefix_of_prefix hrt hst).elim
    (dyadicTreeFrontier_antichain n hr hs hne)
    (dyadicTreeFrontier_antichain n hs hr (Ne.symm hne))

end ThesisCommon

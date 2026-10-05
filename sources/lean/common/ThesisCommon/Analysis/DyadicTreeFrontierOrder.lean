import ThesisCommon.Analysis.JamesTreeEnumeration

/-! Strict prefix order and immediate-child facts for the actual
breadth-first dyadic enumeration. -/
namespace ThesisCommon

theorem dyadicTreeEnumeration_strict_prefix_index {s t : DyadicTreeNode}
    (hst : s.IsPrefix t) (hne : s ≠ t) :
    dyadicTreeEnumeration.symm s < dyadicTreeEnumeration.symm t := by
  have hle := dyadicTreeEnumeration_prefix_index hst
  have hidx : dyadicTreeEnumeration.symm s ≠ dyadicTreeEnumeration.symm t :=
    fun h => hne (dyadicTreeEnumeration.symm.injective h)
  omega

@[simp] theorem dyadicTreeEnumeration_index_nil : dyadicTreeEnumeration.symm [] = 0 := by
  have h := dyadicTreeEnumeration_prefix_index
    (List.nil_prefix : ([] : DyadicTreeNode).IsPrefix (dyadicTreeEnumeration 0))
  simpa only [Equiv.symm_apply_apply, Nat.le_zero] using h

@[simp] theorem dyadicTreeEnumeration_zero : dyadicTreeEnumeration 0 = [] := by
  apply dyadicTreeEnumeration.symm.injective
  simp only [Equiv.symm_apply_apply,dyadicTreeEnumeration_index_nil]

theorem dyadicTreeEnumeration_child_index (t : DyadicTreeNode) (b : Bool) :
    dyadicTreeEnumeration.symm t < dyadicTreeEnumeration.symm (t ++ [b]) := by
  apply dyadicTreeEnumeration_strict_prefix_index (List.prefix_append t [b])
  intro h
  have hh := congrArg List.length h
  simp only [List.length_append,List.length_singleton] at hh
  omega

theorem dyadic_proper_prefix_of_child {s t : DyadicTreeNode} {b : Bool}
    (hs : s.IsPrefix (t ++ [b])) (hne : s ≠ t ++ [b]) : s.IsPrefix t := by
  apply List.prefix_of_prefix_length_le hs (List.prefix_append t [b])
  have hle := hs.length_le
  have hlt : s.length ≠ (t ++ [b]).length := fun h => hne (hs.eq_of_length h)
  simp only [List.length_append,List.length_singleton] at hle hlt
  omega

theorem exists_dyadic_child_prefix_of_strict_prefix {s t : DyadicTreeNode}
    (hst : s.IsPrefix t) (hne : s ≠ t) : ∃ b : Bool, (s ++ [b]).IsPrefix t := by
  obtain ⟨r,rfl⟩ := hst
  cases r with
  | nil => exact (hne (List.append_nil s).symm).elim
  | cons b r => exact ⟨b,r,by simp only [List.append_assoc,List.singleton_append]⟩

end ThesisCommon

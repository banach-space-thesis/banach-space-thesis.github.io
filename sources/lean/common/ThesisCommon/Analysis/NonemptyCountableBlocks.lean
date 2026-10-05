import ThesisCommon.Analysis.TwoSidedFreeSet

/-! A countable cover of an uncountable set has as many nonempty blocks as
the set, whenever its index set has that same cardinality. -/
noncomputable section
open scoped Cardinal
namespace ThesisCommon
universe u
variable {Γ ι : Type u}

theorem cardinal_nonempty_countable_blocks (B : ι → Set Γ)
    (hΓ : Cardinal.aleph0 < Cardinal.mk Γ)
    (hι : Cardinal.mk ι = Cardinal.mk Γ)
    (hcount : ∀ i, (B i).Countable) (hcover : (⋃ i, B i) = Set.univ) :
    Cardinal.mk {i | (B i).Nonempty} = Cardinal.mk Γ := by
  let A : Set ι := {i | (B i).Nonempty}
  have hcover' : (⋃ i : A, B i.val) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    have hx : x ∈ ⋃ i, B i := by rw [hcover]; trivial
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨⟨i, ⟨x, hi⟩⟩, hi⟩
  have hupper : Cardinal.mk A ≤ Cardinal.mk Γ := (Cardinal.mk_subtype_le A).trans hι.le
  apply le_antisymm hupper
  by_contra h
  have hsmall : Cardinal.mk A < Cardinal.mk Γ := lt_of_not_ge h
  have hbound := mk_iUnion_countable_le (fun i : A => B i.val) (fun i => hcount i.val)
  rw [hcover', Cardinal.mk_univ] at hbound
  exact (not_lt_of_ge hbound) ((Cardinal.mul_le_max_of_aleph0_le_right le_rfl).trans_lt
    (max_lt hsmall hΓ))

end ThesisCommon

import ThesisCommon.Analysis.ALMaximalDisjointFamily

/-! A property available below every nonzero positive vector can be imposed
on every member of a total disjoint family. This is an actual maximal-family
construction; the local property is discharged separately for homogeneity. -/
noncomputable section
open Set
namespace ThesisCommon
variable {E : Type*} [NormedAddCommGroup E] [Lattice E]

theorem exists_total_positive_disjoint_family_of_cofinal_property
    (P : E → Prop)
    (hP : ∀ x : E, 0 ≤ x → x ≠ 0 → ∃ y : E, 0 ≤ y ∧ y ≤ x ∧ y ≠ 0 ∧ P y) :
    ∃ S : Set E, (∀ e ∈ S, 0 ≤ e ∧ e ≠ 0 ∧ P e) ∧
      S.Pairwise (fun e f => e ⊓ f = 0) ∧
      ∀ x : E, 0 ≤ x → (∀ e ∈ S, x ⊓ e = 0) → x = 0 := by
  let A : Set (Set E) := {S | (∀ e ∈ S, 0 ≤ e ∧ e ≠ 0 ∧ P e) ∧
    S.Pairwise (fun e f => e ⊓ f = 0)}
  obtain ⟨S, hS⟩ := zorn_subset A (by
    intro c hc hchain
    refine ⟨⋃₀ c, ⟨?_, ?_⟩, fun s hs => subset_sUnion_of_mem hs⟩
    · rintro e ⟨s, hs, he⟩
      exact (hc hs).1 e he
    · rintro e ⟨s, hs, he⟩ f ⟨t, ht, hf⟩ hef
      rcases hchain.total hs ht with hst | hts
      · exact (hc ht).2 (hst he) hf hef
      · exact (hc hs).2 he (hts hf) hef)
  refine ⟨S, hS.prop.1, hS.prop.2, ?_⟩
  intro x hx hdis
  by_contra hx0
  obtain ⟨y, hy0, hyx, hyne, hyP⟩ := hP x hx hx0
  have hyS (e : E) (he : e ∈ S) : y ⊓ e = 0 :=
    le_antisymm ((inf_le_inf_right e hyx).trans_eq (hdis e he))
      (le_inf hy0 (hS.prop.1 e he).1)
  have hi : insert y S ∈ A := by
    refine ⟨?_, ?_⟩
    · intro e he
      rcases mem_insert_iff.mp he with rfl | he
      · exact ⟨hy0, hyne, hyP⟩
      · exact hS.prop.1 e he
    · intro e he f hf hef
      rcases mem_insert_iff.mp he with hey | heS
      · subst e
        rcases mem_insert_iff.mp hf with hfy | hfS
        · exact (hef hfy.symm).elim
        · exact hyS f hfS
      · rcases mem_insert_iff.mp hf with hfy | hfS
        · subst f
          rw [inf_comm]
          exact hyS e heS
        · exact hS.prop.2 heS hfS hef
  have heq : insert y S = S := (hS.eq_of_subset hi (subset_insert y S)).symm
  have hys : y ∈ S := heq ▸ mem_insert y S
  have hyy := hyS y hys
  rw [inf_idem] at hyy
  exact hyne hyy

end ThesisCommon

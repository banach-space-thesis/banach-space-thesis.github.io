import ThesisCommon.Analysis.NonemptyCountableBlocks

/-! A countable partition indexed with the same uncountable cardinal may
be restricted to its nonempty pieces by an actual injective reindexing. -/
noncomputable section
namespace ThesisCommon
universe u
variable {Γ ι : Type u}

theorem countable_partition_nonempty_embedding (B : ι → Set Γ)
    (hΓ : Cardinal.aleph0 < Cardinal.mk Γ) (hι : Cardinal.mk ι = Cardinal.mk Γ)
    (hcount : ∀ i, (B i).Countable) (hcover : (⋃ i, B i) = Set.univ) :
    ∃ e : Γ ↪ ι, (∀ γ, (B (e γ)).Nonempty) ∧ (⋃ γ, B (e γ)) = Set.univ := by
  classical
  let A : Set ι := {i | (B i).Nonempty}
  have hA : Cardinal.mk A = Cardinal.mk Γ := cardinal_nonempty_countable_blocks B hΓ hι hcount hcover
  let e : Γ ≃ A := Classical.choice (Cardinal.eq.mp hA.symm)
  refine ⟨e.toEmbedding.trans (Function.Embedding.subtype A), fun γ => (e γ).property, ?_⟩
  apply Set.eq_univ_of_forall
  intro x
  have hx : x ∈ ⋃ i, B i := by rw [hcover]; trivial
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  let a : A := ⟨i, ⟨x, hi⟩⟩
  refine Set.mem_iUnion.mpr ⟨e.symm a, ?_⟩
  change x ∈ B (e (e.symm a)).val
  simpa only [e.apply_symm_apply] using hi

end ThesisCommon

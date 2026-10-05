import ThesisCommon.Analysis.NonemptyCountableBlocks

/-! Removing empty blocks and reindexing by the original uncountable set
preserves every property of the individual blocks. -/
noncomputable section
namespace ThesisCommon
universe u
variable {Γ ι : Type u}

theorem countable_partition_nonempty_reindex (B : ι → Set Γ)
    (hΓ : Cardinal.aleph0 < Cardinal.mk Γ) (hι : Cardinal.mk ι = Cardinal.mk Γ)
    (hdisj : Pairwise (fun i j => Disjoint (B i) (B j)))
    (hcount : ∀ i, (B i).Countable) (hcover : (⋃ i, B i) = Set.univ)
    (P : Set Γ → Prop) (hP : ∀ i, P (B i)) :
    ∃ D : Γ → Set Γ, Pairwise (fun i j => Disjoint (D i) (D j)) ∧
      (∀ i, (D i).Countable) ∧ (∀ i, (D i).Nonempty) ∧
      (⋃ i, D i) = Set.univ ∧ ∀ i, P (D i) := by
  classical
  let A : Set ι := {i | (B i).Nonempty}
  have hA : Cardinal.mk A = Cardinal.mk Γ :=
    cardinal_nonempty_countable_blocks B hΓ hι hcount hcover
  let e : Γ ≃ A := Classical.choice (Cardinal.eq.mp hA.symm)
  refine ⟨fun i => B (e i).val, ?_, fun i => hcount _, fun i => (e i).property, ?_,
    fun i => hP _⟩
  · intro i j hij
    apply hdisj
    exact fun h => hij (e.injective (Subtype.ext h))
  · apply Set.eq_univ_of_forall
    intro x
    have hx : x ∈ ⋃ i, B i := by rw [hcover]; trivial
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    let a : A := ⟨i, ⟨x, hi⟩⟩
    exact Set.mem_iUnion.mpr ⟨e.symm a, by simpa only [e.apply_symm_apply] using hi⟩

end ThesisCommon

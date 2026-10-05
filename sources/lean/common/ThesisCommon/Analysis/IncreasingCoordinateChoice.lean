import ThesisCommon.Analysis.InfiniteFusion

/-! Select an increasing sequence from a different infinite inner set in
each row, as required by UPFP Proposition 5.4. -/
noncomputable section
namespace ThesisCommon

theorem increasing_choice_from_embeddings (a : ℕ → (ℕ ↪ ℕ)) :
    ∃ t : ℕ → ℕ, StrictMono (fun k => a k (t k)) := by
  classical
  have hex : ∀ k b : ℕ, ∃ t, b < a k t := by
    intro k b
    obtain ⟨m, ⟨⟨t, rfl⟩, ht⟩⟩ :=
      (infinite_above (Set.infinite_range_of_injective (a k).injective) b).nonempty
    exact ⟨t, ht⟩
  choose next hnext using hex
  let t : ℕ → ℕ := fun k => Nat.rec 0 (fun j tj => next (j+1) (a j tj)) k
  refine ⟨t, strictMono_nat_of_lt_succ ?_⟩
  intro k
  exact hnext (k+1) (a k (t k))

end ThesisCommon

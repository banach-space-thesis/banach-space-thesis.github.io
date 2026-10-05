import Posets.Models

/-! A choice of the order embedding in Section 5 that gives every index a
common coordinate. This addresses the empty-coordinate issue without changing
Theorem 1.1's order-embedding hypothesis. -/
namespace Posets

def markedSet (A : Set ℕ) : Set ℕ := insert 0 (Nat.succ '' A)

@[simp] theorem succ_mem_markedSet (A : Set ℕ) (n : ℕ) :
    Nat.succ n ∈ markedSet A ↔ n ∈ A := by
  simp [markedSet]

theorem markedSet_injective : Function.Injective markedSet := by
  intro A B h
  ext n
  have h' := congrArg (fun S : Set ℕ => Nat.succ n ∈ S) h
  simpa using h'

theorem markedSet_ne_empty (A : Set ℕ) : markedSet A ≠ ∅ := by
  intro h
  have hzero : 0 ∈ markedSet A := Set.mem_insert _ _
  rw [h] at hzero
  exact hzero

def paddedFamily (S : Set (Set ℕ)) : Set (Set ℕ) := insert ∅ (markedSet '' S)

theorem paddedFamily_subset_iff (S T : Set (Set ℕ)) :
    paddedFamily S ⊆ paddedFamily T ↔ S ⊆ T := by
  constructor
  · intro h A hA
    have hmem := h (Set.mem_insert_of_mem ∅ (Set.mem_image_of_mem markedSet hA))
    rcases hmem with hempty | ⟨B, hB, hBA⟩
    · exact (markedSet_ne_empty A hempty).elim
    · have hBA' := markedSet_injective hBA
      subst B
      exact hB
  · intro h
    exact Set.insert_subset_insert (Set.image_mono h)

/-- Any embedding in the theorem's exact powerset carrier can be chosen so
that all its values contain the fixed coordinate ∅. -/
def commonCoordinateEmbedding {P : Type*} [PartialOrder P]
    (e : P ↪o Set (Set ℕ)) : P ↪o Set (Set ℕ) where
  toFun p := paddedFamily (e p)
  inj' := by
    intro p q h
    apply e.injective
    exact Set.Subset.antisymm
      ((paddedFamily_subset_iff _ _).mp h.le)
      ((paddedFamily_subset_iff _ _).mp h.ge)
  map_rel_iff' := by
    intro p q
    exact (paddedFamily_subset_iff (e p) (e q)).trans e.map_rel_iff

theorem commonCoordinateEmbedding_mem {P : Type*} [PartialOrder P]
    (e : P ↪o Set (Set ℕ)) (p : P) : ∅ ∈ commonCoordinateEmbedding e p :=
  Set.mem_insert _ _

end Posets

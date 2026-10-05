import Mathlib.Data.Set.Finite.Basic

/-! Every infinite set of natural numbers contains two disjoint infinite
subsets, obtained from the even and odd positions of an actual embedding. -/
noncomputable section
open Set Function
namespace ThesisCommon

theorem infinite_nat_set_exists_disjoint_infinite_subsets {A : Set ℕ}
    (hA : A.Infinite) :
    ∃ B C : Set ℕ, B.Infinite ∧ C.Infinite ∧ B ⊆ A ∧ C ⊆ A ∧ Disjoint B C := by
  let e : ℕ ↪ A := hA.natEmbedding A
  let b : ℕ → ℕ := fun n => (e (2 * n)).val
  let c : ℕ → ℕ := fun n => (e (2 * n + 1)).val
  have hb : Injective b := by
    intro m n h
    have he : 2 * m = 2 * n := e.injective (Subtype.ext h)
    omega
  have hc : Injective c := by
    intro m n h
    have he : 2 * m + 1 = 2 * n + 1 := e.injective (Subtype.ext h)
    omega
  refine ⟨range b, range c, infinite_range_of_injective hb,
    infinite_range_of_injective hc, ?_, ?_, ?_⟩
  · rintro _ ⟨n, rfl⟩
    exact (e (2 * n)).property
  · rintro _ ⟨n, rfl⟩
    exact (e (2 * n + 1)).property
  · apply Set.disjoint_left.mpr
    rintro _ ⟨m, rfl⟩ ⟨n, h⟩
    have he : 2 * n + 1 = 2 * m := e.injective (Subtype.ext h)
    omega

end ThesisCommon

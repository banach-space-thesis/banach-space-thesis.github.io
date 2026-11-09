import BanachIsometric.PiolaBoxBoundary
import Mathlib.Topology.Order.DenselyOrdered

/-! # The coordinate-face boundary is exactly the topological box boundary -/

namespace BanachIsometric

open Set

theorem interior_piolaBox {n : ℕ} (a b : PiolaSpace n) :
    interior (Icc a b) = Set.univ.pi (fun i => Ioo (a i) (b i)) := by
  rw [← pi_univ_Icc, interior_pi_set Set.finite_univ]
  simp only [interior_Icc]

theorem piolaBoxBoundary_eq_frontier {n : ℕ} (a b : PiolaSpace n) :
    piolaBoxBoundary a b = frontier (Icc a b) := by
  classical
  rw [frontier, isClosed_Icc.closure_eq, interior_piolaBox]
  ext x
  rw [mem_piolaBoxBoundary_iff]
  simp only [mem_diff, mem_pi, mem_univ, true_implies, mem_Ioo]
  change (x ∈ Icc a b ∧ ∃ i, x i = a i ∨ x i = b i) ↔
    x ∈ Icc a b ∧ ¬ ∀ i, a i < x i ∧ x i < b i
  constructor
  · rintro ⟨hx, i, hi⟩
    refine ⟨hx, fun hstrict => ?_⟩
    rcases hi with hi | hi
    · exact (ne_of_lt (hstrict i).1) hi.symm
    · exact (ne_of_lt (hstrict i).2) hi
  · rintro ⟨hx, hstrict⟩
    obtain ⟨i, hi⟩ := not_forall.mp hstrict
    refine ⟨hx, i, ?_⟩
    by_cases hleft : x i = a i
    · exact Or.inl hleft
    · right
      have hlt : a i < x i := lt_of_le_of_ne (hx.1 i) (Ne.symm hleft)
      exact le_antisymm (hx.2 i) (le_of_not_gt (fun hright => hi ⟨hlt, hright⟩))

end BanachIsometric

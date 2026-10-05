import Posets.WolfeMassBounds
import Mathlib.Data.Nat.Pairing

/-! The disjoint unions used in Wolfe's finite mass-budget descent. -/
noncomputable section
open Set
namespace Posets

variable {K : Type*}

def wolfeCrossUnion (G : ℕ → Set K) (i : ℕ) : Set K := ⋃ j, ⋃ (_ : j ≠ i), G j

theorem mem_wolfeCrossUnion (G : ℕ → Set K) (i : ℕ) (x : K) :
    x ∈ wolfeCrossUnion G i ↔ ∃ j, j ≠ i ∧ x ∈ G j := by
  simp [wolfeCrossUnion]

theorem wolfeCrossUnion_reindex_subset (G : ℕ → Set K) {k : ℕ → ℕ}
    (hk : Function.Injective k) (i : ℕ) :
    wolfeCrossUnion (G ∘ k) i ⊆ wolfeCrossUnion G (k i) := by
  intro x hx
  obtain ⟨j, hji, hj⟩ := (mem_wolfeCrossUnion _ _ _).mp hx
  exact (mem_wolfeCrossUnion _ _ _).mpr ⟨k j, hk.ne hji, hj⟩

theorem wolfeCrossUnion_isOpen [TopologicalSpace K] (G : ℕ → Set K)
    (hG : ∀ i, IsOpen (G i)) (i : ℕ) : IsOpen (wolfeCrossUnion G i) :=
  isOpen_iUnion fun j => isOpen_iUnion fun _ => hG j

theorem wolfePairRow_injective (p : ℕ) : Function.Injective (Nat.pair p) := by
  intro i j h
  exact (Nat.pair_eq_pair.mp h).2

theorem wolfePairDiagonal_injective (s : ℕ → ℕ) :
    Function.Injective (fun p => Nat.pair p (s p)) := by
  intro i j h
  exact (Nat.pair_eq_pair.mp h).1

/-- Other selected rows are disjoint from the unselected members of one row. -/
theorem wolfeCrossUnion_pair_disjoint (G : ℕ → Set K)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (s : ℕ → ℕ) (p : ℕ) :
    Disjoint (wolfeCrossUnion (fun j => G (Nat.pair p j)) (s p))
      (wolfeCrossUnion (fun r => G (Nat.pair r (s r))) p) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  obtain ⟨j, _, hxj⟩ := (mem_wolfeCrossUnion _ _ _).mp hx
  obtain ⟨r, hrp, hyr⟩ := (mem_wolfeCrossUnion _ _ _).mp hy
  exact Set.disjoint_left.mp (hG (fun h => hrp (Nat.pair_eq_pair.mp h).1.symm)) hxj hyr

variable {𝕜 : Type*} [RCLike 𝕜] [TopologicalSpace K]

/-- The cross-mass of a diagonal subsequence loses the mass reserved in its row. -/
theorem wolfeCrossUnion_pair_budget (M : JLMS.AtomicDualModel 𝕜 K)
    (G : ℕ → Set K) (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (s : ℕ → ℕ) (p : ℕ) (μ : WeakDual 𝕜 (JLMS.CZero 𝕜 K))
    {Q ε : ℝ} (hQ : wolfeMass M μ (wolfeCrossUnion G (Nat.pair p (s p))) ≤ Q)
    (hε : ε ≤ wolfeMass M μ (wolfeCrossUnion (fun j => G (Nat.pair p j)) (s p))) :
    wolfeMass M μ (wolfeCrossUnion (fun r => G (Nat.pair r (s r))) p) ≤ Q - ε := by
  have hsub : wolfeCrossUnion (fun j => G (Nat.pair p j)) (s p) ∪
      wolfeCrossUnion (fun r => G (Nat.pair r (s r))) p ⊆
      wolfeCrossUnion G (Nat.pair p (s p)) :=
    union_subset (wolfeCrossUnion_reindex_subset G (wolfePairRow_injective p) (s p))
      (wolfeCrossUnion_reindex_subset G (wolfePairDiagonal_injective s) p)
  have h := (wolfeMass_mono M μ hsub).trans hQ
  rw [wolfeMass_union M μ (wolfeCrossUnion_pair_disjoint G hG s p)] at h
  linarith

end Posets

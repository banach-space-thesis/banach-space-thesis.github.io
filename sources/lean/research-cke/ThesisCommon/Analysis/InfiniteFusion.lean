import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

/-! The nested infinite-set recursion in the primariness papers.
The step property remains explicit; the theorem constructs the entire sequence
and proves that all later selected points lie in every earlier retained set.
-/
noncomputable section
namespace ThesisCommon

/-- Removing a finite initial interval leaves an infinite set of naturals. -/
theorem infinite_above {A : Set ℕ} (hA : A.Infinite) (b : ℕ) :
    {m ∈ A | b < m}.Infinite := by
  convert hA.diff (Set.finite_Iic b) using 1
  ext m
  simp

/-- Recursively retain an infinite tail and one new point. Besides strict
increase, this records the tail containment needed for operator restrictions.
The predicate Q is the concrete estimate proved by a paper's one-step lemma. -/
theorem infinite_fusion (Q : ℕ → ℕ → Set ℕ → Prop) {M : Set ℕ} (hM : M.Infinite)
    (step : ∀ k (A : Set ℕ), A.Infinite →
      ∃ n ∈ A, ∃ B : Set ℕ, B.Infinite ∧ B ⊆ A ∧
        (∀ m ∈ B, n < m) ∧ Q k n B) :
    ∃ (f : ℕ → ℕ) (A : ℕ → Set ℕ), A 0 = M ∧
      (∀ k, (A k).Infinite) ∧ (∀ k, f k ∈ A k) ∧
      (∀ k, A (k + 1) ⊆ A k) ∧ (∀ k m, m ∈ A (k + 1) → f k < m) ∧
      StrictMono f ∧ (∀ k, Q k (f k) (A (k + 1))) ∧
      (∀ k j, k < j → f j ∈ A (k + 1)) := by
  classical
  let S := {A : Set ℕ // A.Infinite}
  have hstep : ∀ k (A : S), ∃ n ∈ A.val, ∃ B : Set ℕ, B.Infinite ∧ B ⊆ A.val ∧
      (∀ m ∈ B, n < m) ∧ Q k n B := fun k A => step k A.val A.property
  choose n hn B hB hsub hgt hQ using hstep
  let states : ℕ → S := fun k => Nat.rec (⟨M, hM⟩ : S)
    (fun k A => ⟨B k A, hB k A⟩) k
  let A : ℕ → Set ℕ := fun k => (states k).val
  let f : ℕ → ℕ := fun k => n k (states k)
  have hnext : ∀ k, A (k + 1) = B k (states k) := fun _ => rfl
  have hmem : ∀ k, f k ∈ A k := fun k => hn k (states k)
  have hnest : ∀ k, A (k + 1) ⊆ A k := by
    intro k
    rw [hnext]
    exact hsub k (states k)
  have hanti : Antitone A := antitone_nat_of_succ_le hnest
  have htail : ∀ k j, k < j → f j ∈ A (k + 1) := by
    intro k j hkj
    exact hanti (Nat.succ_le_of_lt hkj) (hmem j)
  have horder : ∀ k m, m ∈ A (k + 1) → f k < m := by
    intro k m hm
    rw [hnext] at hm
    exact hgt k (states k) m hm
  refine ⟨f, A, rfl, (fun k => (states k).property), hmem, hnest, horder,
    (fun i j hij => horder i (f j) (htail i j hij)), ?_, htail⟩
  intro k
  rw [hnext]
  exact hQ k (states k)

/-- The entry-wise specialization used for upper-triangular estimates. -/
theorem infinite_fusion_entries (R : ℕ → ℕ → ℕ → Prop) {M : Set ℕ} (hM : M.Infinite)
    (step : ∀ k (A : Set ℕ), A.Infinite →
      ∃ n ∈ A, ∃ B : Set ℕ, B.Infinite ∧ B ⊆ A ∧
        (∀ m ∈ B, n < m) ∧ (∀ m ∈ B, R k n m)) :
    ∃ f : ℕ → ℕ, StrictMono f ∧ (∀ k, f k ∈ M) ∧
      ∀ i j, i < j → R i (f i) (f j) := by
  obtain ⟨f, A, hzero, _hinf, hmem, hnest, _horder, hmono, hR, htail⟩ :=
    infinite_fusion (fun k n B => ∀ m ∈ B, R k n m) hM step
  refine ⟨f, hmono, ?_, ?_⟩
  · intro k
    rw [← hzero]
    exact (antitone_nat_of_succ_le hnest) (Nat.zero_le k) (hmem k)
  · intro i j hij
    exact hR i (f j) (htail i j hij)

end ThesisCommon

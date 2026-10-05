import ThesisCommon.Analysis.InfiniteFusion

/-! Nested infinite-set selection with parameters refined at every stage.
This expands the simultaneous inner-coordinate recursion in UPFP 3.8.
The invariant records why every earlier estimate survives later refinements.
-/
noncomputable section
namespace ThesisCommon

theorem infinite_fusion_parameters {P : Type*}
    (r : P → P → Prop) (hr : Reflexive r) (ht : Transitive r)
    (Q : ℕ → ℕ → ℕ → P → Prop)
    (hQmono : ∀ k n m a b, r b a → Q k n m a → Q k n m b)
    {M : Set ℕ} (hM : M.Infinite) (b₀ : ℕ → P)
    (step : ∀ k (A : Set ℕ), A.Infinite → ∀ b : ℕ → P,
      ∃ n ∈ A, ∃ (B : Set ℕ) (c : ℕ → P), B.Infinite ∧ B ⊆ A ∧
        (∀ m ∈ B, n < m) ∧ (∀ m, r (c m) (b m)) ∧ (∀ m ∈ B, Q k n m (c m))) :
    ∃ (f : ℕ → ℕ) (a : ℕ → P), StrictMono f ∧ (∀ k, f k ∈ M) ∧
      ∀ i j, i < j → Q i (f i) (f j) (a j) := by
  classical
  let S := {A : Set ℕ // A.Infinite} × (ℕ → P)
  have hs : ∀ k (s : S), ∃ n ∈ s.1.val, ∃ (B : Set ℕ) (c : ℕ → P),
      B.Infinite ∧ B ⊆ s.1.val ∧ (∀ m ∈ B, n < m) ∧
        (∀ m, r (c m) (s.2 m)) ∧ (∀ m ∈ B, Q k n m (c m)) :=
    fun k s => step k s.1.val s.1.property s.2
  choose n hn B c hB hsub hgt hrel hQ using hs
  let states : ℕ → S := fun k => Nat.rec ((⟨M, hM⟩, b₀) : S)
    (fun k s => (⟨B k s, hB k s⟩, c k s)) k
  let A : ℕ → Set ℕ := fun k => (states k).1.val
  let b : ℕ → ℕ → P := fun k => (states k).2
  let f : ℕ → ℕ := fun k => n k (states k)
  have hAnext : ∀ k, A (k+1) = B k (states k) := fun _ => rfl
  have hbnext : ∀ k, b (k+1) = c k (states k) := fun _ => rfl
  have hmem : ∀ k, f k ∈ A k := fun k => hn k (states k)
  have hnest : ∀ k, A (k+1) ⊆ A k := by
    intro k
    rw [hAnext]
    exact hsub k (states k)
  have htail : ∀ i j, i < j → f j ∈ A (i+1) := fun i j hij =>
    (antitone_nat_of_succ_le hnest) (Nat.succ_le_of_lt hij) (hmem j)
  have hmono : StrictMono f := by
    intro i j hij
    exact hgt i (states i) (f j) (htail i j hij)
  have hbref : ∀ i j, i ≤ j → ∀ m, r (b j m) (b i m) := by
    intro i j hij m
    induction j, hij using Nat.le_induction with
    | base => exact hr _
    | succ j hij ih =>
      exact ht (hrel j (states j) m) ih
  refine ⟨f, (fun j => b j (f j)), hmono, ?_, ?_⟩
  · intro k
    exact (antitone_nat_of_succ_le hnest) (Nat.zero_le k) (hmem k)
  · intro i j hij
    apply hQmono i (f i) (f j) (b (i+1) (f j)) (b j (f j))
      (hbref (i+1) j (Nat.succ_le_of_lt hij) (f j))
    exact hQ i (states i) (f j) (htail i j hij)

end ThesisCommon

import ThesisCommon.Analysis.InfiniteFusion

/-! The nested-set recursion with an additional strictly increasing label,
used for the inner coordinates of LPCK Lemma 3.10. -/
noncomputable section
namespace ThesisCommon

theorem infinite_fusion_increasing_labels (Q : ℕ → ℕ → ℕ → Set ℕ → Prop)
    {M : Set ℕ} (hM : M.Infinite)
    (step : ∀ k (A : Set ℕ), A.Infinite → ∀ b : ℕ,
      ∃ n ∈ A, ∃ m, b < m ∧ ∃ B : Set ℕ, B.Infinite ∧ B ⊆ A ∧
        (∀ t ∈ B, n < t) ∧ Q k n m B) :
    ∃ (f g : ℕ → ℕ) (A : ℕ → Set ℕ), StrictMono f ∧ StrictMono g ∧
      (∀ k, f k ∈ M) ∧ (∀ k, Q k (f k) (g k) (A (k+1))) ∧
      (∀ k j, k < j → f j ∈ A (k+1)) := by
  classical
  let S := {A : Set ℕ // A.Infinite} × ℕ
  have hstep : ∀ k (s : S), ∃ n ∈ s.1.val, ∃ m, s.2 < m ∧
      ∃ B : Set ℕ, B.Infinite ∧ B ⊆ s.1.val ∧ (∀ t ∈ B, n < t) ∧ Q k n m B :=
    fun k s => step k s.1.val s.1.property s.2
  choose n hn m hm B hB hsub hgt hQ using hstep
  let states : ℕ → S := fun k => Nat.rec ((⟨M, hM⟩, 0) : S)
    (fun k s => (⟨B k s, hB k s⟩, m k s)) k
  let A : ℕ → Set ℕ := fun k => (states k).1.val
  let f : ℕ → ℕ := fun k => n k (states k)
  let g : ℕ → ℕ := fun k => m k (states k)
  have hnext : ∀ k, A (k+1) = B k (states k) := fun _ => rfl
  have hmem : ∀ k, f k ∈ A k := fun k => hn k (states k)
  have hnest : ∀ k, A (k+1) ⊆ A k := by
    intro k
    rw [hnext]
    exact hsub k (states k)
  have htail : ∀ k j, k < j → f j ∈ A (k+1) := fun k j hkj =>
    (antitone_nat_of_succ_le hnest) (Nat.succ_le_of_lt hkj) (hmem j)
  have hmono : StrictMono f := by
    intro i j hij
    exact hgt i (states i) (f j) (htail i j hij)
  have hlabels : StrictMono g := strictMono_nat_of_lt_succ (fun k => hm (k+1) (states (k+1)))
  refine ⟨f, g, A, hmono, hlabels, ?_, ?_, htail⟩
  · intro k
    exact (antitone_nat_of_succ_le hnest) (Nat.zero_le k) (hmem k)
  · intro k
    exact hQ k (states k)

end ThesisCommon

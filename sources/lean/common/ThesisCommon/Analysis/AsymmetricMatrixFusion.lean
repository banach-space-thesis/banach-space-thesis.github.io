import ThesisCommon.Analysis.AsymmetricMatrixStep

/-! Iterate the checked finite-history extension and read off its stable
coordinates. Every pair enters at its pairing index; its choices are then
unchanged, so any two final coordinates inherit a finite-stage estimate.
-/
noncomputable section
open scoped BigOperators
namespace ThesisCommon

/-- Asymmetric selection with whole-row finiteness, finite incoming
interference, and uniformly bounded finite column sums in every block. -/
theorem asymmetric_matrix_selection
    (w : (ℕ × ℕ) → (ℕ × ℕ) → ℝ) (δ : (ℕ × ℕ) → ℕ → ℝ)
    (hδ : ∀ p i, 0 < δ p i)
    (hrow : ∀ p ε, 0 < ε → {i | ∃ j, ε ≤ w p (i, j)}.Finite)
    (hcol : ∀ p ε, 0 < ε → {q | ε ≤ w q p}.Finite)
    (C : ℕ → ℕ → ℝ)
    (hbound : ∀ r i j (F : Finset ℕ), ∑ s ∈ F, w (r, s) (i, j) ≤ C r i) :
    ∃ (n : ℕ → ℕ) (m : ℕ → ℕ → ℕ), StrictMono n ∧ (∀ i, StrictMono (m i)) ∧
      ∀ p q : ℕ × ℕ, p ≠ q → w (n p.1, m p.1 p.2) (n q.1, m q.1 q.2) ≤ δ p q.1 := by
  classical
  let next (t : ℕ) (S : AsymmetricMatrixSelection.State w δ t) :=
    (AsymmetricMatrixSelection.step hδ hrow hcol C hbound S).choose
  let states : (t : ℕ) → AsymmetricMatrixSelection.State w δ t :=
    Nat.rec AsymmetricMatrixSelection.initial (fun t S => next t S)
  have hrowstep (t i : ℕ) (hi : AsymmetricMatrixSelection.index (i, 0) < t) :
      (states (t + 1)).row i = (states t).row i :=
    (AsymmetricMatrixSelection.step hδ hrow hcol C hbound (states t)).choose_spec.1 i hi
  have hcolstep (t : ℕ) (p : ℕ × ℕ) (hp : AsymmetricMatrixSelection.index p < t) :
      (states (t + 1)).col p = (states t).col p :=
    (AsymmetricMatrixSelection.step hδ hrow hcol C hbound (states t)).choose_spec.2 p hp
  have hrowstable (a t i : ℕ) (hi : AsymmetricMatrixSelection.index (i, 0) < a)
      (hat : a ≤ t) : (states t).row i = (states a).row i := by
    induction t, hat using Nat.le_induction with
    | base => rfl
    | succ t hat ih => rw [hrowstep t i (hi.trans_le hat), ih]
  have hcolstable (a t : ℕ) (p : ℕ × ℕ) (hp : AsymmetricMatrixSelection.index p < a)
      (hat : a ≤ t) : (states t).col p = (states a).col p := by
    induction t, hat using Nat.le_induction with
    | base => rfl
    | succ t hat ih => rw [hcolstep t p (hp.trans_le hat), ih]
  let n := fun i => (states (Nat.pair i 0 + 1)).row i
  let m := fun i j => (states (Nat.pair i j + 1)).col (i, j)
  have hn (t i : ℕ) (hi : Nat.pair i 0 < t) : (states t).row i = n i :=
    hrowstable _ _ _ (Nat.lt_succ_self _) (Nat.succ_le_of_lt hi)
  have hm (t : ℕ) (p : ℕ × ℕ) (hp : Nat.pair p.1 p.2 < t) :
      (states t).col p = m p.1 p.2 :=
    hcolstable _ _ _ (Nat.lt_succ_self _) (Nat.succ_le_of_lt hp)
  refine ⟨n, m, ?_, ?_, ?_⟩
  · intro i j hij
    let t := Nat.pair j 0 + 1
    have hi : Nat.pair i 0 < t :=
      (Nat.pair_lt_pair_left 0 hij).trans (Nat.lt_succ_self _)
    have hj : Nat.pair j 0 < t := Nat.lt_succ_self _
    rw [← hn t i hi, ← hn t j hj]
    exact (states t).row_mono i j hi hj hij
  · intro i j k hjk
    let t := Nat.pair i k + 1
    have hj : Nat.pair i j < t :=
      (Nat.pair_lt_pair_right i hjk).trans (Nat.lt_succ_self _)
    have hk : Nat.pair i k < t := Nat.lt_succ_self _
    rw [← hm t (i, j) hj, ← hm t (i, k) hk]
    exact (states t).col_mono (i, j) (i, k) hj hk rfl hjk
  · intro p q hpq
    let t := max (Nat.pair p.1 p.2) (Nat.pair q.1 q.2) + 1
    have hp : Nat.pair p.1 p.2 < t := (le_max_left _ _).trans_lt (Nat.lt_succ_self _)
    have hq : Nat.pair q.1 q.2 < t := (le_max_right _ _).trans_lt (Nat.lt_succ_self _)
    have hh := (states t).small p q hp hq hpq
    rw [hm t p hp, hm t q hq,
      hn t p.1 ((AsymmetricMatrixSelection.index_zero_le p.1 p.2).trans_lt hp),
      hn t q.1 ((AsymmetricMatrixSelection.index_zero_le q.1 q.2).trans_lt hq)] at hh
    exact hh

end ThesisCommon

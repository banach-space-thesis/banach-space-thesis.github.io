import ThesisCommon.Analysis.FiniteColumnInterference
import Mathlib.Data.Nat.Pairing

/-! Finite-reservoir selection for a matrix indexed by pairs. Unlike a
two-sided weak-null gliding hump, old target rows constrain whole future
reservoirs. The error depends on the target pair and the source outer row.
-/
noncomputable section
open scoped Classical
namespace ThesisCommon
namespace AsymmetricMatrixSelection

abbrev index (p : ℕ × ℕ) : ℕ := Nat.pair p.1 p.2

theorem index_zero_le (i j : ℕ) : index (i, 0) ≤ index (i, j) :=
  (strictMono_nat_of_lt_succ (fun n => Nat.pair_lt_pair_right i (Nat.lt_succ_self n))).monotone
    (Nat.zero_le j)

theorem index_mono_left {i j : ℕ} (h : i ≤ j) : index (i, 0) ≤ index (j, 0) :=
  (strictMono_nat_of_lt_succ (fun n => Nat.pair_lt_pair_left 0 (Nat.lt_succ_self n))).monotone h

theorem finite_past (t : ℕ) : {p : ℕ × ℕ | index p < t}.Finite :=
  (Set.finite_Iio t).preimage Nat.pairEquiv.injective.injOn

theorem finite_active (t : ℕ) : {i : ℕ | index (i, 0) < t}.Finite :=
  (Set.finite_Iio t).subset (fun i hi => (Nat.left_le_pair i 0).trans_lt hi)

/-- A finite history and its genuinely infinite future reservoirs. -/
structure State (w : (ℕ × ℕ) → (ℕ × ℕ) → ℝ) (δ : (ℕ × ℕ) → ℕ → ℝ) (t : ℕ) where
  row : ℕ → ℕ
  col : (ℕ × ℕ) → ℕ
  reservoir : ℕ → Set ℕ
  row_mono : ∀ i j, index (i, 0) < t → index (j, 0) < t → i < j → row i < row j
  col_mono : ∀ p q, index p < t → index q < t → p.1 = q.1 → p.2 < q.2 → col p < col q
  infinite : ∀ i, index (i, 0) < t → (reservoir i).Infinite
  tail : ∀ p, index p < t → ∀ v ∈ reservoir p.1, col p < v
  small : ∀ p q, index p < t → index q < t → p ≠ q →
    w (row p.1, col p) (row q.1, col q) ≤ δ p q.1
  future : ∀ p, index p < t → ∀ i, index (i, 0) < t → ∀ v ∈ reservoir i,
    w (row p.1, col p) (row i, v) ≤ δ p i

variable {w : (ℕ × ℕ) → (ℕ × ℕ) → ℝ} {δ : (ℕ × ℕ) → ℕ → ℝ}

def initial : State w δ 0 where
  row := fun _ => 0
  col := fun _ => 0
  reservoir := fun _ => Set.univ
  row_mono := by simp
  col_mono := by simp
  infinite := by simp
  tail := by simp
  small := by simp
  future := by simp

/-- Open the next outer row if necessary. All old target estimates then
hold on the enlarged family of reservoirs, before choosing the new inner index. -/
theorem open_row (hδ : ∀ p i, 0 < δ p i)
    (hrow : ∀ p ε, 0 < ε → {i | ∃ j, ε ≤ w p (i, j)}.Finite)
    {t : ℕ} (S : State w δ t) :
    ∃ (n : ℕ → ℕ) (H : ℕ → Set ℕ),
      (∀ i, index (i, 0) < t → n i = S.row i) ∧
      (∀ i j, index (i, 0) < t + 1 → index (j, 0) < t + 1 → i < j → n i < n j) ∧
      (∀ i, index (i, 0) < t + 1 → (H i).Infinite) ∧
      (∀ p, index p < t → ∀ v ∈ H p.1, S.col p < v) ∧
      (∀ p, index p < t → ∀ i, index (i, 0) < t + 1 → ∀ v ∈ H i,
        w (n p.1, S.col p) (n i, v) ≤ δ p i) := by
  classical
  let p := Nat.unpair t
  have hp : index p = t := Nat.pair_unpair t
  have hactive (i : ℕ) (hi : index (i, 0) < t + 1) :
      index (i, 0) < t ∨ i = p.1 := by
    by_cases h : index (i, 0) < t
    · exact Or.inl h
    · right
      have heq : index (i, 0) = index p := by omega
      exact (Nat.pair_eq_pair.mp heq).1
  by_cases hk : index (p.1, 0) < t
  · refine ⟨S.row, S.reservoir, fun _ _ => rfl, ?_, ?_, S.tail, ?_⟩
    · intro i j hi hj hij
      apply S.row_mono i j _ _ hij
      · rcases hactive i hi with h | rfl <;> assumption
      · rcases hactive j hj with h | rfl <;> assumption
    · intro i hi
      apply S.infinite i
      rcases hactive i hi with h | rfl <;> assumption
    · intro q hq i hi v hv
      apply S.future q hq i _ v hv
      rcases hactive i hi with h | rfl <;> assumption
  · have hbefore (i : ℕ) (hi : index (i, 0) < t) : i < p.1 := by
      by_contra h
      have hh := index_mono_left (le_of_not_gt h)
      omega
    let bad : Set ℕ := ⋃ q ∈ {q : ℕ × ℕ | index q < t},
      {i | ∃ j, δ q p.1 ≤ w (S.row q.1, S.col q) (i, j)}
    have hbad : bad.Finite := (finite_past t).biUnion
      (fun q _ => hrow _ _ (hδ q p.1))
    let old : Finset ℕ := (finite_active t).toFinset.image S.row
    obtain ⟨N, hN, hlarge⟩ :=
      ((Set.infinite_univ : (Set.univ : Set ℕ).Infinite).diff hbad).exists_gt (old.sup id)
    have hNold (i : ℕ) (hi : index (i, 0) < t) : S.row i < N :=
      (Finset.le_sup (f := id) (Finset.mem_image.mpr
        ⟨i, (finite_active t).mem_toFinset.mpr hi, rfl⟩)).trans_lt hlarge
    let n := Function.update S.row p.1 N
    let H := Function.update S.reservoir p.1 Set.univ
    have hn (i : ℕ) (hi : index (i, 0) < t) : n i = S.row i := by
      exact Function.update_of_ne (ne_of_lt (hbefore i hi)) _ _
    have hH (i : ℕ) (hi : index (i, 0) < t) : H i = S.reservoir i := by
      exact Function.update_of_ne (ne_of_lt (hbefore i hi)) _ _
    refine ⟨n, H, hn, ?_, ?_, ?_, ?_⟩
    · intro i j hi hj hij
      rcases hactive i hi with hi | rfl
      · rw [hn i hi]
        rcases hactive j hj with hj | rfl
        · rw [hn j hj]; exact S.row_mono i j hi hj hij
        · simpa only [n, Function.update_self] using hNold i hi
      · rcases hactive j hj with hj | rfl
        · exact (not_lt_of_ge (hbefore j hj).le hij).elim
        · exact (lt_irrefl _ hij).elim
    · intro i hi
      rcases hactive i hi with hi | rfl
      · rw [hH i hi]; exact S.infinite i hi
      · simpa only [H, Function.update_self] using (Set.infinite_univ : (Set.univ : Set ℕ).Infinite)
    · intro q hq v hv
      rw [hH q.1 ((index_zero_le q.1 q.2).trans_lt hq)] at hv
      exact S.tail q hq v hv
    · intro q hq i hi v hv
      rw [hn q.1 ((index_zero_le q.1 q.2).trans_lt hq)]
      rcases hactive i hi with hi | rfl
      · rw [hn i hi]
        rw [hH i hi] at hv
        exact S.future q hq i hi v hv
      · simp only [n, Function.update_self]
        by_contra hh
        apply hN.2
        exact Set.mem_iUnion.mpr ⟨q, Set.mem_iUnion.mpr ⟨hq, v, le_of_not_ge hh⟩⟩

end AsymmetricMatrixSelection
end ThesisCommon

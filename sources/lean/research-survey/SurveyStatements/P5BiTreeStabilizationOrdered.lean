import SurveyStatements.P5BiTreeStabilizationRounds

/-! Choose the finite level branches in order above every earlier
frequency. This supplies the strict frequency separation needed by the
actual Haar compression formula. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter Set Topology
open scoped ENNReal BigOperators Classical

namespace SurveyStatements.P5.BiTree
open P5Support
variable {𝕜 : Type*} [RCLike 𝕜]

theorem exists_ordered_finite_splits {q : ℕ}
    (P : Fin q → LpHaarFiniteSplit → Prop)
    (hnext : ∀ i N, ∃ S : LpHaarFiniteSplit, N ≤ S.level ∧ P i S)
    (N : ℕ) :
    ∃ S : Fin q → LpHaarFiniteSplit,
      (∀ i, N ≤ (S i).level ∧ P i (S i)) ∧
        ∀ i j, i.val < j.val → (S i).level < (S j).level := by
  let R (j : ℕ) (h : Fin j → LpHaarFiniteSplit) (S : LpHaarFiniteSplit) : Prop :=
    ∀ hj : j < q, N ≤ S.level ∧ P ⟨j, hj⟩ S ∧ ∀ i, (h i).level < S.level
  obtain ⟨s, hs⟩ := exists_sequence_with_history R (fun j h => by
    by_cases hj : j < q
    · obtain ⟨S, hlevel, hP⟩ := hnext ⟨j, hj⟩ (max N ((∑ i : Fin j, (h i).level) + 1))
      refine ⟨S, fun _ => ⟨(le_max_left _ _).trans hlevel, hP, ?_⟩⟩
      intro i
      have hi : (h i).level ≤ ∑ k : Fin j, (h k).level :=
        Finset.single_le_sum (f := fun k : Fin j => (h k).level)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      have hlarge := (le_max_right N ((∑ k : Fin j, (h k).level) + 1)).trans hlevel
      omega
    · exact ⟨⟨0, {⟨0, by decide⟩}, fun _ => true, Finset.singleton_nonempty _⟩,
        fun hbad => (hj hbad).elim⟩)
  refine ⟨fun i => s i.val, fun i => ?_, fun i j hij => ?_⟩
  · exact ⟨(hs i.val i.isLt).1, (hs i.val i.isLt).2.1⟩
  · exact (hs j.val j.isLt).2.2 ⟨i.val, hij⟩

structure OrderedRoundSpec (d : DyadicIndex → DyadicIndex → 𝕜) {M : ℝ}
    (H : IteratedTraceData d M) (ε : ℕ → ℝ) (n : ℕ)
    (h : (i : Fin n) → LevelPairs i.val) (r : LevelPairs n) : Prop
    extends RoundSpec d H ε n h r where
  outer_before : ∀ i : Fin n, ∀ k : Fin (2 ^ i.val), ∀ l,
    ((h i).1 k).level < (r.1 l).level
  inner_before : ∀ i : Fin n, ∀ k : Fin (2 ^ i.val), ∀ l,
    ((h i).2 k).level < (r.2 l).level
  outer_within : ∀ k l, k.val < l.val → (r.1 k).level < (r.1 l).level
  inner_within : ∀ k l, k.val < l.val → (r.2 k).level < (r.2 l).level

theorem exists_ordered_round (d : DyadicIndex → DyadicIndex → 𝕜)
    {M : ℝ} (hM : 0 ≤ M) (H : IteratedTraceData d M)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n)
    (n : ℕ) (h : (i : Fin n) → LevelPairs i.val) :
    ∃ r : LevelPairs n, OrderedRoundSpec d H ε n h r := by
  let Ni := (∑ r : PastIndex n, ((h r.1).2 r.2).level) + 1
  have hi (k : Fin (2 ^ n)) (N : ℕ) : ∃ S : LpHaarFiniteSplit, N ≤ S.level ∧
      InnerStepSpec d H (outerParents n h) (pastOuter n h) (innerParents n h k)
        (lpHaarHeapIndex n k) (ε n) S := by
    obtain ⟨S, hs⟩ := exists_inner_step d hM H (outerParents n h) (pastOuter n h)
      (innerParents n h k) (max (lpHaarHeapIndex n k) N) (hε n)
    refine ⟨S, (le_max_right _ _).trans hs.level, ?_⟩
    exact ⟨(le_max_left _ _).trans hs.level, hs.parent, hs.past_approx,
      hs.lower_approx, hs.past_balance, hs.lower_balance, hs.upper_balance⟩
  obtain ⟨T, hT, hTwithin⟩ := exists_ordered_finite_splits
    (fun k S => InnerStepSpec d H (outerParents n h) (pastOuter n h) (innerParents n h k)
      (lpHaarHeapIndex n k) (ε n) S) hi Ni
  let No := (∑ r : PastIndex n, ((h r.1).1 r.2).level) + 1
  have ho (k : Fin (2 ^ n)) (N : ℕ) : ∃ S : LpHaarFiniteSplit, N ≤ S.level ∧
      OuterStepSpec d H (fun q : Fin (2 ^ n) × Bool => (T q.1).child q.2)
        (innerThroughCurrent n h T) (outerParents n h k)
          (lpHaarHeapIndex n k) (ε n) S := by
    obtain ⟨S, hs⟩ := exists_outer_step d hM H
      (fun q : Fin (2 ^ n) × Bool => (T q.1).child q.2)
      (innerThroughCurrent n h T) (outerParents n h k)
        (max (lpHaarHeapIndex n k) N) (hε n)
    refine ⟨S, (le_max_right _ _).trans hs.level, ?_⟩
    exact ⟨(le_max_left _ _).trans hs.level, hs.parent, hs.past_approx,
      hs.upper_approx, hs.past_balance, hs.lower_balance, hs.upper_balance⟩
  obtain ⟨S, hS, hSwithin⟩ := exists_ordered_finite_splits
    (fun k S => OuterStepSpec d H (fun q : Fin (2 ^ n) × Bool => (T q.1).child q.2)
      (innerThroughCurrent n h T) (outerParents n h k)
        (lpHaarHeapIndex n k) (ε n) S) ho No
  refine ⟨⟨S, T⟩, ⟨⟨fun k => (hT k).2, fun k => (hS k).2⟩,
    ?_, ?_, hSwithin, hTwithin⟩⟩
  · intro i k l
    change ((h i).1 k).level < (S l).level
    have hi : ((h i).1 k).level ≤ ∑ r : PastIndex n, ((h r.1).1 r.2).level :=
      Finset.single_le_sum (f := fun r : PastIndex n => ((h r.1).1 r.2).level)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ ⟨i, k⟩)
    have hl := (hS l).1
    dsimp only [No] at hl
    omega
  · intro i k l
    change ((h i).2 k).level < (T l).level
    have hi : ((h i).2 k).level ≤ ∑ r : PastIndex n, ((h r.1).2 r.2).level :=
      Finset.single_le_sum (f := fun r : PastIndex n => ((h r.1).2 r.2).level)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ ⟨i, k⟩)
    have hl := (hT l).1
    dsimp only [Ni] at hl
    omega

theorem exists_ordered_round_sequence (d : DyadicIndex → DyadicIndex → 𝕜)
    {M : ℝ} (hM : 0 ≤ M) (H : IteratedTraceData d M)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) :
    ∃ r : (n : ℕ) → LevelPairs n, ∀ n,
      OrderedRoundSpec d H ε n (fun i : Fin n => r i.val) (r n) :=
  exists_dependent_sequence_with_history (OrderedRoundSpec d H ε)
    (exists_ordered_round d hM H ε hε)

theorem heap_ordered_frequencies (f : (n : ℕ) → LevelSplits n)
    (hbefore : ∀ n (i : Fin n) (k : Fin (2 ^ i.val)) l,
      (f i.val k).level < (f n l).level)
    (hwithin : ∀ n k l, k.val < l.val → (f n k).level < (f n l).level)
    (i j : ℕ) (hij : i < j) :
    (f (heapDecode i).1 (heapDecode i).2).level <
      (f (heapDecode j).1 (heapDecode j).2).level := by
  have hdepth : (heapDecode i).1 ≤ (heapDecode j).1 := by
    change (i + 1).log2 ≤ (j + 1).log2
    rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
    exact Nat.log_mono_right (by omega)
  rcases hI : heapDecode i with ⟨n, k⟩
  rcases hJ : heapDecode j with ⟨m, l⟩
  have hi : lpHaarHeapIndex n k = i :=
    (congrArg (fun K : DyadicIndex => lpHaarHeapIndex K.1 K.2) hI).symm.trans
      (heapIndex_decode i)
  have hj : lpHaarHeapIndex m l = j :=
    (congrArg (fun K : DyadicIndex => lpHaarHeapIndex K.1 K.2) hJ).symm.trans
      (heapIndex_decode j)
  simp only [hI, hJ] at hdepth ⊢
  change n ≤ m at hdepth
  rcases lt_or_eq_of_le hdepth with hnm | rfl
  · exact hbefore m ⟨n, hnm⟩ k l
  · apply hwithin n k l
    simp only [lpHaarHeapIndex] at hi hj
    omega

theorem roundOuterTree_strict_frequencies
    (d : DyadicIndex → DyadicIndex → 𝕜) {M : ℝ} (H : IteratedTraceData d M)
    (ε : ℕ → ℝ) (r : (n : ℕ) → LevelPairs n)
    (hr : ∀ n, OrderedRoundSpec d H ε n (fun i : Fin n => r i.val) (r n)) :
    ∀ i j, i < j →
      ((roundOuterTree d H ε r (fun n => (hr n).toRoundSpec)).toSequentialSplits.node i).level <
      ((roundOuterTree d H ε r (fun n => (hr n).toRoundSpec)).toSequentialSplits.node j).level :=
  heap_ordered_frequencies (fun n => (r n).1)
    (fun n => (hr n).outer_before) (fun n => (hr n).outer_within)

theorem roundInnerTree_strict_frequencies
    (d : DyadicIndex → DyadicIndex → 𝕜) {M : ℝ} (H : IteratedTraceData d M)
    (ε : ℕ → ℝ) (r : (n : ℕ) → LevelPairs n)
    (hr : ∀ n, OrderedRoundSpec d H ε n (fun i : Fin n => r i.val) (r n)) :
    ∀ i j, i < j →
      ((roundInnerTree d H ε r (fun n => (hr n).toRoundSpec)).toSequentialSplits.node i).level <
      ((roundInnerTree d H ε r (fun n => (hr n).toRoundSpec)).toSequentialSplits.node j).level :=
  heap_ordered_frequencies (fun n => (r n).2)
    (fun n => (hr n).inner_before) (fun n => (hr n).inner_within)

end SurveyStatements.P5.BiTree

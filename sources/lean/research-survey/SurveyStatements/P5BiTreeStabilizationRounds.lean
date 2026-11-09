import SurveyStatements.P5BiTreeStabilizationSelection

/-! Alternate actual inner and outer signed choices level by level. The
entire infinite construction uses only the finite selection lemmas. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter Set Topology
open scoped ENNReal BigOperators Classical

namespace SurveyStatements.P5.BiTree
open P5Support
variable {𝕜 : Type*} [RCLike 𝕜]

abbrev PastIndex (n : ℕ) := Σ i : Fin n, Fin (2 ^ i.val)

def outerParents (n : ℕ) (h : (i : Fin n) → LevelPairs i.val) :
    Fin (2 ^ n) → LpHaarFiniteParent :=
  historyParents n (fun i => (h i).1)

def innerParents (n : ℕ) (h : (i : Fin n) → LevelPairs i.val) :
    Fin (2 ^ n) → LpHaarFiniteParent :=
  historyParents n (fun i => (h i).2)

def pastOuter (n : ℕ) (h : (i : Fin n) → LevelPairs i.val)
    (r : PastIndex n) : LpHaarFiniteSplit := (h r.1).1 r.2

def extendedInner (n : ℕ) (h : (i : Fin n) → LevelPairs i.val)
    (T : LevelSplits n) : (i : Fin (n + 1)) → LevelSplits i.val :=
  Fin.lastCases (motive := fun i : Fin (n + 1) => LevelSplits i.val) T
    (fun i => (h i).2)

def innerThroughCurrent (n : ℕ) (h : (i : Fin n) → LevelPairs i.val)
    (T : LevelSplits n) (r : PastIndex (n + 1)) : LpHaarFiniteSplit :=
  extendedInner n h T r.1 r.2

structure RoundSpec (d : DyadicIndex → DyadicIndex → 𝕜) {M : ℝ}
    (H : IteratedTraceData d M) (ε : ℕ → ℝ) (n : ℕ)
    (h : (i : Fin n) → LevelPairs i.val) (r : LevelPairs n) : Prop where
  inner : ∀ k, InnerStepSpec d H (outerParents n h) (pastOuter n h)
    (innerParents n h k) (lpHaarHeapIndex n k) (ε n) (r.2 k)
  outer : ∀ k, OuterStepSpec d H (fun q : Fin (2 ^ n) × Bool => (r.2 q.1).child q.2)
    (innerThroughCurrent n h r.2) (outerParents n h k)
      (lpHaarHeapIndex n k) (ε n) (r.1 k)

theorem exists_round (d : DyadicIndex → DyadicIndex → 𝕜) {M : ℝ} (hM : 0 ≤ M)
    (H : IteratedTraceData d M) (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n)
    (n : ℕ) (h : (i : Fin n) → LevelPairs i.val) :
    ∃ r : LevelPairs n, RoundSpec d H ε n h r := by
  have hinner (k : Fin (2 ^ n)) := exists_inner_step d hM H
    (outerParents n h) (pastOuter n h) (innerParents n h k)
      (lpHaarHeapIndex n k) (hε n)
  let T : LevelSplits n := fun k => (hinner k).choose
  have hT (k : Fin (2 ^ n)) : InnerStepSpec d H (outerParents n h) (pastOuter n h)
      (innerParents n h k) (lpHaarHeapIndex n k) (ε n) (T k) := (hinner k).choose_spec
  have houter (k : Fin (2 ^ n)) := exists_outer_step d hM H
    (fun q : Fin (2 ^ n) × Bool => (T q.1).child q.2)
    (innerThroughCurrent n h T) (outerParents n h k)
      (lpHaarHeapIndex n k) (hε n)
  exact ⟨⟨fun k => (houter k).choose, T⟩,
    ⟨hT, fun k => (houter k).choose_spec⟩⟩

theorem exists_round_sequence (d : DyadicIndex → DyadicIndex → 𝕜)
    {M : ℝ} (hM : 0 ≤ M) (H : IteratedTraceData d M)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) :
    ∃ r : (n : ℕ) → LevelPairs n, ∀ n,
      RoundSpec d H ε n (fun i : Fin n => r i.val) (r n) :=
  exists_dependent_sequence_with_history (RoundSpec d H ε)
    (exists_round d hM H ε hε)

theorem extendedInner_sequence (r : (n : ℕ) → LevelPairs n)
    (n : ℕ) (i : Fin (n + 1)) :
    extendedInner n (fun j : Fin n => r j.val) (r n).2 i = (r i.val).2 := by
  induction i using Fin.lastCases with
  | last => exact Fin.lastCases_last
  | cast i => exact Fin.lastCases_castSucc i

def roundOuterTree (d : DyadicIndex → DyadicIndex → 𝕜) {M : ℝ}
    (H : IteratedTraceData d M) (ε : ℕ → ℝ)
    (r : (n : ℕ) → LevelPairs n)
    (hr : ∀ n, RoundSpec d H ε n (fun i : Fin n => r i.val) (r n)) :
    DyadicSignedTree where
  node I := (r I.1).1 I.2
  level I := ((hr I.1).outer I.2).level
  root := ((hr 0).outer ⟨0, by decide⟩).parent
  children I b := by
    cases b
    · change ((r (I.1 + 1)).1 (lpHaarRightIndex I.1 I.2)).parent.set = _
      have h := ((hr (I.1 + 1)).outer (lpHaarRightIndex I.1 I.2)).parent
      simpa only [outerParents, historyParents_right] using h
    · change ((r (I.1 + 1)).1 (lpHaarLeftIndex I.1 I.2)).parent.set = _
      have h := ((hr (I.1 + 1)).outer (lpHaarLeftIndex I.1 I.2)).parent
      simpa only [outerParents, historyParents_left] using h

def roundInnerTree (d : DyadicIndex → DyadicIndex → 𝕜) {M : ℝ}
    (H : IteratedTraceData d M) (ε : ℕ → ℝ)
    (r : (n : ℕ) → LevelPairs n)
    (hr : ∀ n, RoundSpec d H ε n (fun i : Fin n => r i.val) (r n)) :
    DyadicSignedTree where
  node I := (r I.1).2 I.2
  level I := ((hr I.1).inner I.2).level
  root := ((hr 0).inner ⟨0, by decide⟩).parent
  children I b := by
    cases b
    · change ((r (I.1 + 1)).2 (lpHaarRightIndex I.1 I.2)).parent.set = _
      have h := ((hr (I.1 + 1)).inner (lpHaarRightIndex I.1 I.2)).parent
      simpa only [innerParents, historyParents_right] using h
    · change ((r (I.1 + 1)).2 (lpHaarLeftIndex I.1 I.2)).parent.set = _
      have h := ((hr (I.1 + 1)).inner (lpHaarLeftIndex I.1 I.2)).parent
      simpa only [innerParents, historyParents_left] using h

end SurveyStatements.P5.BiTree

import SurveyStatements.P5Support.LpHaarSequentialSplits

/-! Coherent alternating finite histories. A legal finite history is enough
for the next selection; no extension property of an arbitrary illegal
history is assumed. The resulting trees have genuine parent sets and
strictly increasing block frequencies. Analytic step predicates remain
explicit here and must be established by the finite selection theorems. -/

noncomputable section
set_option autoImplicit false
open scoped Classical

namespace SurveyStatements.P5OperatorReduction
open SurveyStatements.P5Support

def historyPrefix {A : Type*} {n : ℕ} (h : Fin n → A) (i : Fin n) :
    Fin i.val → A := fun j => h ⟨j.val, j.isLt.trans i.isLt⟩

theorem exists_sequence_from_legal_histories {A : Type*}
    (P : (n : ℕ) → (Fin n → A) → A → Prop)
    (hnext : ∀ n h, (∀ i : Fin n, P i.val (historyPrefix h i) (h i)) →
      ∃ a, P n h a) :
    ∃ r : ℕ → A, ∀ n, P n (fun i : Fin n => r i.val) (r n) := by
  obtain ⟨a₀, _⟩ := hnext 0 Fin.elim0 (fun i => Fin.elim0 i)
  obtain ⟨r, hr⟩ := exists_sequence_with_history
    (fun n h a => (∀ i : Fin n, P i.val (historyPrefix h i) (h i)) → P n h a)
    (fun n h => by
      by_cases hh : ∀ i : Fin n, P i.val (historyPrefix h i) (h i)
      · obtain ⟨a, ha⟩ := hnext n h hh
        exact ⟨a, fun _ => ha⟩
      · exact ⟨a₀, fun hlegal => (hh hlegal).elim⟩)
  refine ⟨r, ?_⟩
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      apply hr n
      intro i
      exact ih i.val i.isLt

abbrev AlternatingSplitHistory (n : ℕ) :=
  Fin n → LpHaarFiniteSplit × LpHaarFiniteSplit

def alternatingOuterHistory {n : ℕ} (h : AlternatingSplitHistory n) :
    Fin n → LpHaarFiniteSplit := fun i => (h i).1

def alternatingInnerHistory {n : ℕ} (h : AlternatingSplitHistory n) :
    Fin n → LpHaarFiniteSplit := fun i => (h i).2

structure AlternatingSplitStep
    (InnerSpec : (n : ℕ) → (Fin n → LpHaarFiniteSplit) →
      (Fin n → LpHaarFiniteSplit) → LpHaarFiniteSplit → Prop)
    (OuterSpec : (n : ℕ) → (Fin n → LpHaarFiniteSplit) →
      (Fin (n + 1) → LpHaarFiniteSplit) → LpHaarFiniteSplit → Prop)
    (n : ℕ) (h : AlternatingSplitHistory n)
    (S : LpHaarFiniteSplit × LpHaarFiniteSplit) : Prop where
  outer_level : n ≤ S.1.level
  inner_level : n ≤ S.2.level
  outer_parent : S.1.parent.set =
    (lpHaarHistoryParent n (alternatingOuterHistory h)).set
  inner_parent : S.2.parent.set =
    (lpHaarHistoryParent n (alternatingInnerHistory h)).set
  outer_after : ∀ i : Fin n, (h i).1.level < S.1.level
  inner_after : ∀ i : Fin n, (h i).2.level < S.2.level
  inner_spec : InnerSpec n (alternatingOuterHistory h) (alternatingInnerHistory h) S.2
  outer_spec : OuterSpec n (alternatingOuterHistory h)
    (Fin.lastCases S.2 (alternatingInnerHistory h)) S.1

theorem exists_alternating_split_histories
    (InnerSpec : (n : ℕ) → (Fin n → LpHaarFiniteSplit) →
      (Fin n → LpHaarFiniteSplit) → LpHaarFiniteSplit → Prop)
    (OuterSpec : (n : ℕ) → (Fin n → LpHaarFiniteSplit) →
      (Fin (n + 1) → LpHaarFiniteSplit) → LpHaarFiniteSplit → Prop)
    (hnext : ∀ n (h : AlternatingSplitHistory n),
      (∀ i : Fin n, AlternatingSplitStep InnerSpec OuterSpec i.val
        (historyPrefix h i) (h i)) →
      ∃ S, AlternatingSplitStep InnerSpec OuterSpec n h S) :
    ∃ Fo Fi : LpHaarSequentialSplits,
      (∀ i j, i < j → (Fo.node i).level < (Fo.node j).level) ∧
      (∀ i j, i < j → (Fi.node i).level < (Fi.node j).level) ∧
      (∀ n, InnerSpec n (fun i : Fin n => Fo.node i.val)
        (fun i : Fin n => Fi.node i.val) (Fi.node n)) ∧
      ∀ n, OuterSpec n (fun i : Fin n => Fo.node i.val)
        (Fin.lastCases (Fi.node n) (fun i : Fin n => Fi.node i.val)) (Fo.node n) := by
  obtain ⟨r, hr⟩ := exists_sequence_from_legal_histories
    (AlternatingSplitStep InnerSpec OuterSpec) hnext
  let Fo : LpHaarSequentialSplits :=
    ⟨fun n => (r n).1, fun n => (hr n).outer_level, fun n => (hr n).outer_parent⟩
  let Fi : LpHaarSequentialSplits :=
    ⟨fun n => (r n).2, fun n => (hr n).inner_level, fun n => (hr n).inner_parent⟩
  refine ⟨Fo, Fi, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    exact (hr j).outer_after ⟨i, hij⟩
  · intro i j hij
    exact (hr j).inner_after ⟨i, hij⟩
  · intro n
    exact (hr n).inner_spec
  · intro n
    exact (hr n).outer_spec

end SurveyStatements.P5OperatorReduction

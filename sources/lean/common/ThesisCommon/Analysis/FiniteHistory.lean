import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Range
import Mathlib.Order.Monotone.Basic

noncomputable section
namespace ThesisCommon

/-- Choose an increasing sequence when each finite admissible history admits
a larger witness. The predicate sees exactly the preceding chosen indices. -/
theorem increasing_finite_history (C : Set ℕ) (P : ℕ → Finset ℕ → Prop)
    (hnext : ∀ F : Finset ℕ, (∀ m ∈ F, m ∈ C) →
      ∃ n ∈ C, (∀ m ∈ F, m < n) ∧ P n F) :
    ∃ r : ℕ → ℕ, StrictMono r ∧ (∀ n, r n ∈ C) ∧
      ∀ n, P (r n) ((Finset.range n).image r) := by
  classical
  let State := {F : Finset ℕ // ∀ m ∈ F, m ∈ C}
  let next (s : State) : ℕ := (hnext s.val s.property).choose
  have hn (s : State) : next s ∈ C ∧ (∀ m ∈ s.val, m < next s) ∧ P (next s) s.val :=
    (hnext s.val s.property).choose_spec
  let step (s : State) : State :=
    ⟨insert (next s) s.val, by
      intro m hm
      rcases Finset.mem_insert.mp hm with rfl | hm
      · exact (hn s).1
      · exact s.property m hm⟩
  let state : ℕ → State := Nat.rec ⟨∅, by simp⟩ (fun _ s => step s)
  let r : ℕ → ℕ := fun n => next (state n)
  have hstep (n : ℕ) : (state (n + 1)).val = insert (r n) (state n).val := rfl
  have hmono : StrictMono r := strictMono_nat_of_lt_succ (fun n =>
    (hn (state (n + 1))).2.1 (r n) (by rw [hstep]; exact Finset.mem_insert_self _ _))
  have hpast (n : ℕ) : (state n).val = (Finset.range n).image r := by
    induction n with
    | zero => rfl
    | succ n ih => rw [hstep, ih, Finset.range_add_one, Finset.image_insert]
  exact ⟨r, hmono, fun n => (hn (state n)).1, fun n => hpast n ▸ (hn (state n)).2.2⟩

end ThesisCommon

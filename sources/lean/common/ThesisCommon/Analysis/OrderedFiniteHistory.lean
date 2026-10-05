import Mathlib.Data.Fin.Basic

/-! Ordered finite histories, with each choice depending on all earlier
values and no future values. The construction uses dependent Nat recursion. -/

noncomputable section
namespace ThesisCommon

theorem exists_sequence_with_history {A : Type*}
    (P : (n : ℕ) → (Fin n → A) → A → Prop)
    (hnext : ∀ n h, ∃ a, P n h a) :
    ∃ r : ℕ → A, ∀ n, P n (fun i : Fin n => r i.val) (r n) := by
  let next (n : ℕ) (h : Fin n → A) : A := (hnext n h).choose
  let state : (n : ℕ) → Fin n → A :=
    Nat.rec (motive := fun n => Fin n → A) Fin.elim0
      (fun n h => Fin.lastCases (next n h) h)
  let r : ℕ → A := fun n => next n (state n)
  have hpast (n : ℕ) (i : Fin n) : state n i = r i.val := by
    induction n with
    | zero => exact Fin.elim0 i
    | succ n ih =>
        induction i using Fin.lastCases with
        | last =>
            change Fin.lastCases (r n) (state n) (Fin.last n) = r n
            exact Fin.lastCases_last
        | cast i =>
            change Fin.lastCases (r n) (state n) i.castSucc = r i.val
            rw [Fin.lastCases_castSucc]
            exact ih i
  refine ⟨r, fun n => ?_⟩
  have h := (hnext n (state n)).choose_spec
  change P n (state n) (r n) at h
  have he : state n = fun i : Fin n => r i.val := funext (hpast n)
  simpa only [he] using h

end ThesisCommon

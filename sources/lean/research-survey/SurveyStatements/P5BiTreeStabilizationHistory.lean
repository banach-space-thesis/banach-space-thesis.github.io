import SurveyStatements.P5Support.OrderedFiniteHistory

/-! Dependent finite histories for choosing a whole signed level in each
round of the two-parameter stabilization construction. -/

noncomputable section
set_option autoImplicit false

namespace SurveyStatements.P5.BiTree

theorem exists_dependent_sequence_with_history {A : ℕ → Type*}
    (P : (n : ℕ) → ((i : Fin n) → A i.val) → A n → Prop)
    (hnext : ∀ n h, ∃ a, P n h a) :
    ∃ r : (n : ℕ) → A n, ∀ n, P n (fun i : Fin n => r i.val) (r n) := by
  let next (n : ℕ) (h : (i : Fin n) → A i.val) : A n := (hnext n h).choose
  let state : (n : ℕ) → (i : Fin n) → A i.val :=
    Nat.rec (motive := fun n => (i : Fin n) → A i.val) (fun i => Fin.elim0 i)
      (fun n h => Fin.lastCases (motive := fun i : Fin (n + 1) => A i.val) (next n h) h)
  let r : (n : ℕ) → A n := fun n => next n (state n)
  have hpast (n : ℕ) (i : Fin n) : state n i = r i.val := by
    induction n with
    | zero => exact Fin.elim0 i
    | succ n ih =>
        induction i using Fin.lastCases with
        | last =>
            change Fin.lastCases (motive := fun i : Fin (n + 1) => A i.val)
              (r n) (state n) (Fin.last n) = r n
            exact Fin.lastCases_last
        | cast i =>
            change Fin.lastCases (motive := fun i : Fin (n + 1) => A i.val)
              (r n) (state n) i.castSucc = r i.val
            rw [Fin.lastCases_castSucc]
            exact ih i
  refine ⟨r, fun n => ?_⟩
  have h := (hnext n (state n)).choose_spec
  change P n (state n) (r n) at h
  have he : state n = fun i : Fin n => r i.val := funext (hpast n)
  simpa only [he] using h

end SurveyStatements.P5.BiTree
